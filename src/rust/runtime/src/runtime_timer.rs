/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(all(feature = "std", not(target_family = "wasm")))]
mod runtime_timer_impl {
    use crate::*;
    use core::ptr::{addr_of_mut, null_mut};
    use libuv_sys2::{
        uv_close as uv_close_sys, uv_timer_init as uv_timer_init_sys,
        uv_timer_start as uv_timer_start_sys, uv_timer_stop as uv_timer_stop_sys,
    };

    const TIMER_STATE_INITIAL: c_int = 0;
    const TIMER_STATE_RUNNING: c_int = 1;
    const TIMER_STATE_FINISHED: c_int = 2;
    const LEAN_TASK_STATE_FINISHED: u8 = 2;

    #[repr(C, align(8))]
    pub struct UvTimer {
        handle: UvHandle,
        rest: [u8; 56],
    }

    #[repr(C)]
    struct LeanUvTimerObject {
        uv_timer: *mut UvTimer,
        promise: *mut LeanObject,
        timeout: u64,
        repeating: bool,
        state: c_int,
    }

    static mut UV_TIMER_EXTERNAL_CLASS: *mut LeanExternalClass = null_mut();

    unsafe fn uv_close(handle: *mut UvHandle, close_cb: Option<unsafe fn(*mut UvHandle)>) {
        uv_close_sys(handle.cast(), close_cb.map(|cb| core::mem::transmute(cb)));
    }

    unsafe fn uv_timer_init(loop_: *mut UvLoop, handle: *mut UvTimer) -> c_int {
        uv_timer_init_sys(loop_.cast(), handle.cast())
    }

    unsafe fn uv_timer_start(
        handle: *mut UvTimer,
        cb: Option<unsafe fn(*mut UvTimer)>,
        timeout: u64,
        repeat: u64,
    ) -> c_int {
        uv_timer_start_sys(handle.cast(), cb.map(|cb| core::mem::transmute(cb)), timeout, repeat)
    }

    unsafe fn uv_timer_stop(handle: *mut UvTimer) -> c_int {
        uv_timer_stop_sys(handle.cast())
    }

    unsafe fn timer_from_obj(obj: *mut LeanObject) -> *mut LeanUvTimerObject {
        lean_runtime_get_external_data(obj).cast()
    }

    unsafe fn timer_promise_is_finished(timer: *mut LeanUvTimerObject) -> bool {
        let promise = (*timer).promise.cast::<LeanPromiseObject>();
        lean_io_get_task_state_core((*promise).result) == LEAN_TASK_STATE_FINISHED
    }

    unsafe fn close_free_handle(handle: *mut UvHandle) {
        libc::free(handle.cast());
    }
    pub unsafe fn lean_uv_timer_finalizer(ptr: *mut c_void) {
        let timer = ptr.cast::<LeanUvTimerObject>();

        if !(*timer).promise.is_null() {
            lean_dec((*timer).promise);
        }

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        uv_close(
            (*timer).uv_timer.cast::<UvHandle>(),
            Some(close_free_handle),
        );
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        libc::free(timer.cast());
    }

    unsafe fn timer_foreach(obj: *mut c_void, f: *mut LeanObject) {
        let timer = obj.cast::<LeanUvTimerObject>();
        if !(*timer).promise.is_null() {
            lean_inc(f);
            lean_apply_1(f, (*timer).promise);
        }
    }
    pub unsafe fn initialize_libuv_timer() {
        UV_TIMER_EXTERNAL_CLASS =
            lean_register_external_class(Some(lean_uv_timer_finalizer), Some(timer_foreach));
    }
    pub unsafe fn handle_timer_event(handle: *mut UvTimer) {
        let obj = (*handle).handle.data.cast::<LeanObject>();
        let timer = timer_from_obj(obj);

        debug_assert_eq!((*timer).state, TIMER_STATE_RUNNING);

        if (*timer).repeating {
            if !(*timer).promise.is_null() && !timer_promise_is_finished(timer) {
                let result = lean_io_promise_resolve(lean_box(0), (*timer).promise);
                lean_dec(result);
            }
        } else {
            if !(*timer).promise.is_null() {
                debug_assert!(!timer_promise_is_finished(timer));
                let result = lean_io_promise_resolve(lean_box(0), (*timer).promise);
                lean_dec(result);
            }

            uv_timer_stop((*timer).uv_timer);
            (*timer).state = TIMER_STATE_FINISHED;
            lean_dec(obj);
        }
    }

    pub unsafe fn lean_uv_timer_mk(timeout: u64, repeating: u8) -> *mut LeanObject {
        let timer =
            libc::malloc(core::mem::size_of::<LeanUvTimerObject>()).cast::<LeanUvTimerObject>();
        if timer.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        (*timer).timeout = timeout;
        (*timer).repeating = repeating != 0;
        (*timer).state = TIMER_STATE_INITIAL;
        (*timer).promise = null_mut();

        let uv_timer = libc::malloc(core::mem::size_of::<UvTimer>()).cast::<UvTimer>();
        if uv_timer.is_null() {
            libc::free(timer.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_timer_init(_ZN4lean9global_evE.loop_, uv_timer);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result != 0 {
            libc::free(uv_timer.cast());
            libc::free(timer.cast());
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        (*timer).uv_timer = uv_timer;

        let obj = lean_runtime_alloc_external(UV_TIMER_EXTERNAL_CLASS, timer.cast());
        lean_mark_mt(obj);
        (*uv_timer).handle.data = obj.cast();

        lean_io_result_mk_ok(obj)
    }

    unsafe fn setup_timer(obj: *mut LeanObject, timer: *mut LeanUvTimerObject) -> *mut LeanObject {
        debug_assert!((*timer).promise.is_null());

        let promise = lean_io_promise_new();
        (*timer).promise = promise;
        (*timer).state = TIMER_STATE_RUNNING;

        lean_inc(obj);
        lean_inc(promise);

        let result = uv_timer_start(
            (*timer).uv_timer,
            Some(handle_timer_event),
            if (*timer).repeating {
                0
            } else {
                (*timer).timeout
            },
            if (*timer).repeating {
                (*timer).timeout
            } else {
                0
            },
        );

        if result != 0 {
            lean_dec(obj);
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        lean_io_result_mk_ok(promise)
    }

    pub unsafe fn lean_uv_timer_next(obj: *mut LeanObject) -> *mut LeanObject {
        let timer = timer_from_obj(obj);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if (*timer).repeating {
            match (*timer).state {
                TIMER_STATE_INITIAL => setup_timer(obj, timer),
                TIMER_STATE_RUNNING => {
                    if (*timer).promise.is_null() || timer_promise_is_finished(timer) {
                        if !(*timer).promise.is_null() {
                            lean_dec((*timer).promise);
                        }
                        (*timer).promise = lean_io_promise_new();
                    }

                    lean_inc((*timer).promise);
                    let promise = (*timer).promise;
                    event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
                    lean_io_result_mk_ok(promise)
                }
                TIMER_STATE_FINISHED => {
                    if !(*timer).promise.is_null() {
                        lean_inc((*timer).promise);
                        let promise = (*timer).promise;
                        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
                        lean_io_result_mk_ok(promise)
                    } else {
                        let finished_promise = lean_io_promise_new();
                        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
                        lean_io_result_mk_ok(finished_promise)
                    }
                }
                _ => {
                    event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
                    lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(
                        b"invalid timer state\0".as_ptr().cast(),
                    )))
                }
            }
        } else if (*timer).state == TIMER_STATE_INITIAL {
            setup_timer(obj, timer)
        } else if !(*timer).promise.is_null() {
            lean_inc((*timer).promise);
            let promise = (*timer).promise;
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            lean_io_result_mk_ok(promise)
        } else {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            let finished_promise = lean_io_promise_new();
            lean_io_result_mk_ok(finished_promise)
        }
    }

    pub unsafe fn lean_uv_timer_reset(obj: *mut LeanObject) -> *mut LeanObject {
        let timer = timer_from_obj(obj);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if (*timer).state == TIMER_STATE_RUNNING {
            uv_timer_stop((*timer).uv_timer);

            let result = uv_timer_start(
                (*timer).uv_timer,
                Some(handle_timer_event),
                (*timer).timeout,
                if (*timer).repeating {
                    (*timer).timeout
                } else {
                    0
                },
            );

            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

            if result != 0 {
                lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()))
            } else {
                lean_io_result_mk_ok(lean_box(0))
            }
        } else {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            lean_io_result_mk_ok(lean_box(0))
        }
    }

    pub unsafe fn lean_uv_timer_stop(obj: *mut LeanObject) -> *mut LeanObject {
        let timer = timer_from_obj(obj);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if !(*timer).promise.is_null() {
            lean_dec((*timer).promise);
            (*timer).promise = null_mut();
        }

        if (*timer).state == TIMER_STATE_RUNNING {
            uv_timer_stop((*timer).uv_timer);
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

            (*timer).state = TIMER_STATE_FINISHED;
            lean_dec(obj);

            lean_io_result_mk_ok(lean_box(0))
        } else {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            lean_io_result_mk_ok(lean_box(0))
        }
    }

    pub unsafe fn lean_uv_timer_cancel(obj: *mut LeanObject) -> *mut LeanObject {
        let timer = timer_from_obj(obj);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if (*timer).state == TIMER_STATE_RUNNING && !(*timer).promise.is_null() {
            if (*timer).repeating {
                lean_dec((*timer).promise);
                (*timer).promise = null_mut();
            } else {
                uv_timer_stop((*timer).uv_timer);

                lean_dec((*timer).promise);
                (*timer).promise = null_mut();
                (*timer).state = TIMER_STATE_INITIAL;

                lean_dec(obj);
            }
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        lean_io_result_mk_ok(lean_box(0))
    }

    const _: () = {
        assert!(core::mem::size_of::<UvHandle>() == 96);
        assert!(core::mem::align_of::<UvHandle>() == 8);
        assert!(core::mem::size_of::<UvTimer>() == 152);
        assert!(core::mem::align_of::<UvTimer>() == 8);
    };
}

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub use runtime_timer_impl::*;
