/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_timer_impl {
    use crate::runtime_event_loop::GLOBAL_EV;
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::ptr::{addr_of_mut, null_mut};
    use libuv_sys2::{
        uv_close, uv_loop_t, uv_timer_init,
        uv_timer_start, uv_timer_stop,
    };

    const TIMER_STATE_INITIAL: c_int = 0;
    const TIMER_STATE_RUNNING: c_int = 1;
    const TIMER_STATE_FINISHED: c_int = 2;
    const LEAN_TASK_STATE_FINISHED: u8 = 2;

    unsafe fn timer_from_obj(obj: *mut LeanObject) -> *mut LeanUvTimerObject {
        lean_runtime_get_external_data(obj).cast()
    }

    unsafe fn timer_promise_is_finished(timer: *mut LeanUvTimerObject) -> bool {
        let promise = (*timer).promise.cast::<LeanPromiseObject>();
        lean_io_get_task_state_core((*promise).result) == LEAN_TASK_STATE_FINISHED
    }

    pub unsafe fn handle_timer_event(handle: *mut uv_timer_t) {
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

        let uv_timer = libc::malloc(core::mem::size_of::<uv_timer_t>()).cast::<uv_timer_t>();
        if uv_timer.is_null() {
            libc::free(timer.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        event_loop_lock(addr_of_mut!(GLOBAL_EV));
        let result = uv_timer_init(GLOBAL_EV.loop_, uv_timer);
        event_loop_unlock(addr_of_mut!(GLOBAL_EV));

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
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        event_loop_unlock(addr_of_mut!(GLOBAL_EV));
        lean_io_result_mk_ok(promise)
    }

    pub unsafe fn lean_uv_timer_next(obj: *mut LeanObject) -> *mut LeanObject {
        let timer = timer_from_obj(obj);

        event_loop_lock(addr_of_mut!(GLOBAL_EV));

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
                    event_loop_unlock(addr_of_mut!(GLOBAL_EV));
                    lean_io_result_mk_ok(promise)
                }
                TIMER_STATE_FINISHED => {
                    if !(*timer).promise.is_null() {
                        lean_inc((*timer).promise);
                        let promise = (*timer).promise;
                        event_loop_unlock(addr_of_mut!(GLOBAL_EV));
                        lean_io_result_mk_ok(promise)
                    } else {
                        let finished_promise = lean_io_promise_new();
                        event_loop_unlock(addr_of_mut!(GLOBAL_EV));
                        lean_io_result_mk_ok(finished_promise)
                    }
                }
                _ => {
                    event_loop_unlock(addr_of_mut!(GLOBAL_EV));
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
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));
            lean_io_result_mk_ok(promise)
        } else {
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));
            let finished_promise = lean_io_promise_new();
            lean_io_result_mk_ok(finished_promise)
        }
    }

    pub unsafe fn lean_uv_timer_reset(obj: *mut LeanObject) -> *mut LeanObject {
        let timer = timer_from_obj(obj);

        event_loop_lock(addr_of_mut!(GLOBAL_EV));

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

            event_loop_unlock(addr_of_mut!(GLOBAL_EV));

            if result != 0 {
                lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()))
            } else {
                lean_io_result_mk_ok(lean_box(0))
            }
        } else {
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));
            lean_io_result_mk_ok(lean_box(0))
        }
    }

    pub unsafe fn lean_uv_timer_stop(obj: *mut LeanObject) -> *mut LeanObject {
        let timer = timer_from_obj(obj);

        event_loop_lock(addr_of_mut!(GLOBAL_EV));

        if !(*timer).promise.is_null() {
            lean_dec((*timer).promise);
            (*timer).promise = null_mut();
        }

        if (*timer).state == TIMER_STATE_RUNNING {
            uv_timer_stop((*timer).uv_timer);
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));

            (*timer).state = TIMER_STATE_FINISHED;
            lean_dec(obj);

            lean_io_result_mk_ok(lean_box(0))
        } else {
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));
            lean_io_result_mk_ok(lean_box(0))
        }
    }

    pub unsafe fn lean_uv_timer_cancel(obj: *mut LeanObject) -> *mut LeanObject {
        let timer = timer_from_obj(obj);

        event_loop_lock(addr_of_mut!(GLOBAL_EV));

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

        event_loop_unlock(addr_of_mut!(GLOBAL_EV));
        lean_io_result_mk_ok(lean_box(0))
    }

    const _: () = {
        assert!(core::mem::size_of::<uv_handle_t>() == 96);
        assert!(core::mem::align_of::<uv_handle_t>() == 8);
        assert!(core::mem::size_of::<uv_timer_t>() == 152);
        assert!(core::mem::align_of::<uv_timer_t>() == 8);
    };
}

pub use runtime_timer_impl::*;
