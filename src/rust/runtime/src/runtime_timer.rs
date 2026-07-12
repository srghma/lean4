/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_timer_impl {
    use crate::datatypes::LeanTaskState;
    use crate::runtime_event_loop::GLOBAL_EV;
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::ptr::{addr_of_mut, null_mut};
    use libuv_sys2::{uv_close, uv_loop_t, uv_timer_init, uv_timer_start, uv_timer_stop};

    #[repr(i32)]
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    enum TimerState {
        Initial = 0,
        Running = 1,
        Finished = 2,
    }

    impl TimerState {
        fn from_i32(v: c_int) -> Self {
            match v {
                0 => TimerState::Initial,
                1 => TimerState::Running,
                2 => TimerState::Finished,
                n => panic!("invalid TimerState {n}"),
            }
        }
    }

    unsafe fn timer_from_obj(obj: *mut LeanObject) -> *mut LeanUvTimerObject {
        lean_get_external_data(obj).cast()
    }

    unsafe fn timer_promise_is_finished(timer: *mut LeanUvTimerObject) -> bool {
        let promise = (*timer).promise.cast::<LeanPromiseObject>();
        lean_io_get_task_state_core((*promise).result) == LeanTaskState::Finished
    }

    pub unsafe fn handle_timer_event(handle: *mut uv_timer_t) {
        let obj = (*handle).handle.data.cast::<LeanObject>();
        let timer = timer_from_obj(obj);

        debug_assert_eq!(TimerState::from_i32((*timer).state), TimerState::Running);

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
            (*timer).state = TimerState::Finished as c_int;
            lean_dec(obj);
        }
    }

    pub unsafe fn lean_uv_timer_mk(timeout: u64, repeating: bool) -> *mut LeanObject {
        let timer =
            libc::malloc(core::mem::size_of::<LeanUvTimerObject>()).cast::<LeanUvTimerObject>();
        if timer.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        (*timer).timeout = timeout;
        (*timer).repeating = repeating;
        (*timer).state = TimerState::Initial as c_int;
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

        let obj = lean_alloc_external(UV_TIMER_EXTERNAL_CLASS, timer.cast());
        lean_mark_mt(obj);
        (*uv_timer).handle.data = obj.cast();

        lean_io_result_mk_ok(obj)
    }

    unsafe fn setup_timer(obj: *mut LeanObject, timer: *mut LeanUvTimerObject) -> *mut LeanObject {
        debug_assert!((*timer).promise.is_null());

        let promise = lean_io_promise_new();
        (*timer).promise = promise;
        (*timer).state = TimerState::Running as c_int;

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
            match TimerState::from_i32((*timer).state) {
                TimerState::Initial => setup_timer(obj, timer),
                TimerState::Running => {
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
                TimerState::Finished => {
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
        } else if TimerState::from_i32((*timer).state) == TimerState::Initial {
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

        if TimerState::from_i32((*timer).state) == TimerState::Running {
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

        if TimerState::from_i32((*timer).state) == TimerState::Running {
            uv_timer_stop((*timer).uv_timer);
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));

            (*timer).state = TimerState::Finished as c_int;
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

        if TimerState::from_i32((*timer).state) == TimerState::Running && !(*timer).promise.is_null() {
            if (*timer).repeating {
                lean_dec((*timer).promise);
                (*timer).promise = null_mut();
            } else {
                uv_timer_stop((*timer).uv_timer);

                lean_dec((*timer).promise);
                (*timer).promise = null_mut();
                (*timer).state = TimerState::Initial as c_int;

                lean_dec(obj);
            }
        }

        event_loop_unlock(addr_of_mut!(GLOBAL_EV));
        lean_io_result_mk_ok(lean_box(0))
    }

    const TIMER_LAYOUT_ASSERTS: () = {
        assert!(core::mem::size_of::<uv_handle_t>() == 96);
        assert!(core::mem::align_of::<uv_handle_t>() == 8);
        assert!(core::mem::size_of::<uv_timer_t>() == 152);
        assert!(core::mem::align_of::<uv_timer_t>() == 8);
    };
}

pub use runtime_timer_impl::*;
