/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_signal_impl {
    use crate::datatypes::LeanTaskState;
    use crate::runtime_event_loop::GLOBAL_EV;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::ptr::{addr_of_mut, null_mut};
    use libuv_sys2::{
        uv_close, uv_loop_t, uv_signal_init, uv_signal_start, uv_signal_start_oneshot,
        uv_signal_stop,
    };

    #[repr(i32)]
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    enum SignalState {
        Initial = 0,
        Running = 1,
        Finished = 2,
    }

    impl SignalState {
        fn from_i32(v: c_int) -> Self {
            match v {
                0 => SignalState::Initial,
                1 => SignalState::Running,
                2 => SignalState::Finished,
                n => panic!("invalid SignalState {n}"),
            }
        }
    }

    #[repr(u32)]
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    enum LeanSignalKind {
        Hup = 1,
        Int = 2,
        Quit = 3,
        Abort = 6,
        Trap = 5,
        Usr1 = 10,
        Usr2 = 12,
        Alarm = 14,
        Term = 15,
        Chld = 17,
        Cont = 18,
        Tstp = 20,
        Ttin = 21,
        Ttou = 22,
        Urg = 23,
        Xcpu = 24,
        Xfsz = 25,
        Vtalrm = 26,
        Prof = 27,
        Winch = 28,
        Io = 29,
        Sys = 31,
    }

    impl LeanSignalKind {
        fn from_u32(v: u32) -> Self {
            match v {
                1 => LeanSignalKind::Hup,
                2 => LeanSignalKind::Int,
                3 => LeanSignalKind::Quit,
                5 => LeanSignalKind::Trap,
                6 => LeanSignalKind::Abort,
                10 => LeanSignalKind::Usr1,
                12 => LeanSignalKind::Usr2,
                14 => LeanSignalKind::Alarm,
                15 => LeanSignalKind::Term,
                17 => LeanSignalKind::Chld,
                18 => LeanSignalKind::Cont,
                20 => LeanSignalKind::Tstp,
                21 => LeanSignalKind::Ttin,
                22 => LeanSignalKind::Ttou,
                23 => LeanSignalKind::Urg,
                24 => LeanSignalKind::Xcpu,
                25 => LeanSignalKind::Xfsz,
                26 => LeanSignalKind::Vtalrm,
                27 => LeanSignalKind::Prof,
                28 => LeanSignalKind::Winch,
                29 => LeanSignalKind::Io,
                31 => LeanSignalKind::Sys,
                n => panic!("invalid LeanSignalKind {n}"),
            }
        }
    }

    fn lean_signal_to_libc(sig: LeanSignalKind) -> c_int {
        match sig {
            LeanSignalKind::Hup => libc::SIGHUP,
            LeanSignalKind::Int => libc::SIGINT,
            LeanSignalKind::Quit => libc::SIGQUIT,
            LeanSignalKind::Abort => libc::SIGABRT,
            LeanSignalKind::Trap => libc::SIGTRAP,
            LeanSignalKind::Usr1 => libc::SIGUSR1,
            LeanSignalKind::Usr2 => libc::SIGUSR2,
            LeanSignalKind::Alarm => libc::SIGALRM,
            LeanSignalKind::Term => libc::SIGTERM,
            LeanSignalKind::Chld => libc::SIGCHLD,
            LeanSignalKind::Cont => libc::SIGCONT,
            LeanSignalKind::Tstp => libc::SIGTSTP,
            LeanSignalKind::Ttin => libc::SIGTTIN,
            LeanSignalKind::Ttou => libc::SIGTTOU,
            LeanSignalKind::Urg => libc::SIGURG,
            LeanSignalKind::Xcpu => libc::SIGXCPU,
            LeanSignalKind::Xfsz => libc::SIGXFSZ,
            LeanSignalKind::Vtalrm => libc::SIGVTALRM,
            LeanSignalKind::Prof => libc::SIGPROF,
            LeanSignalKind::Winch => libc::SIGWINCH,
            LeanSignalKind::Io => libc::SIGIO,
            LeanSignalKind::Sys => libc::SIGSYS,
        }
    }

    unsafe fn signal_from_obj(obj: *mut LeanObject) -> *mut LeanUvSignalObject {
        lean_get_external_data(obj).cast()
    }

    unsafe fn signal_promise_is_finished(signal: *mut LeanUvSignalObject) -> bool {
        let promise = (*signal).promise.cast::<LeanPromiseObject>();
        lean_io_get_task_state_core((*promise).result) == LeanTaskState::Finished
    }

    pub unsafe fn handle_signal_event(handle: *mut uv_signal_t, signum: c_int) {
        let obj = (*handle).handle.data.cast::<LeanObject>();
        let signal = signal_from_obj(obj);

        debug_assert_eq!(SignalState::from_i32((*signal).state), SignalState::Running);

        if (*signal).repeating {
            if !(*signal).promise.is_null() && !signal_promise_is_finished(signal) {
                let result = lean_io_promise_resolve(lean_box(signum as usize), (*signal).promise);
                lean_dec(result);
            }
        } else {
            if !(*signal).promise.is_null() {
                debug_assert!(!signal_promise_is_finished(signal));
                let result = lean_io_promise_resolve(lean_box(signum as usize), (*signal).promise);
                lean_dec(result);
            }

            uv_signal_stop((*signal).uv_signal);
            (*signal).state = SignalState::Finished as c_int;
            lean_dec(obj);
        }
    }

    pub unsafe fn lean_uv_signal_mk(signum_obj: u32, repeating: bool) -> *mut LeanObject {
        let signum = lean_signal_to_libc(LeanSignalKind::from_u32(signum_obj));

        let signal =
            libc::malloc(core::mem::size_of::<LeanUvSignalObject>()).cast::<LeanUvSignalObject>();
        if signal.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        (*signal).signum = signum;
        (*signal).repeating = repeating;
        (*signal).state = SignalState::Initial as c_int;
        (*signal).promise = null_mut();

        let uv_signal = libc::malloc(core::mem::size_of::<uv_signal_t>()).cast::<uv_signal_t>();
        if uv_signal.is_null() {
            libc::free(signal.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        event_loop_lock(addr_of_mut!(GLOBAL_EV));
        let result = uv_signal_init(GLOBAL_EV.loop_, uv_signal);
        event_loop_unlock(addr_of_mut!(GLOBAL_EV));

        if result != 0 {
            libc::free(uv_signal.cast());
            libc::free(signal.cast());
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        (*signal).uv_signal = uv_signal;

        let obj = lean_alloc_external(UV_SIGNAL_EXTERNAL_CLASS, signal.cast());
        lean_mark_mt(obj);
        (*uv_signal).handle.data = obj.cast();

        lean_io_result_mk_ok(obj)
    }

    unsafe fn setup_signal(
        obj: *mut LeanObject,
        signal: *mut LeanUvSignalObject,
    ) -> *mut LeanObject {
        debug_assert!((*signal).promise.is_null());

        let promise = lean_io_promise_new();
        (*signal).promise = promise;
        (*signal).state = SignalState::Running as c_int;

        lean_inc(obj);
        lean_inc(promise);

        let result = if (*signal).repeating {
            uv_signal_start(
                (*signal).uv_signal,
                Some(handle_signal_event),
                (*signal).signum,
            )
        } else {
            uv_signal_start_oneshot(
                (*signal).uv_signal,
                Some(handle_signal_event),
                (*signal).signum,
            )
        };

        if result != 0 {
            lean_dec(obj);
            lean_dec(promise);
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        event_loop_unlock(addr_of_mut!(GLOBAL_EV));
        lean_io_result_mk_ok(promise)
    }

    pub unsafe fn lean_uv_signal_next(obj: *mut LeanObject) -> *mut LeanObject {
        let signal = signal_from_obj(obj);

        event_loop_lock(addr_of_mut!(GLOBAL_EV));

        if (*signal).repeating {
            match SignalState::from_i32((*signal).state) {
                SignalState::Initial => setup_signal(obj, signal),
                SignalState::Running => {
                    if (*signal).promise.is_null() || signal_promise_is_finished(signal) {
                        if !(*signal).promise.is_null() {
                            lean_dec((*signal).promise);
                        }
                        (*signal).promise = lean_io_promise_new();
                    }

                    lean_inc((*signal).promise);
                    let promise = (*signal).promise;
                    event_loop_unlock(addr_of_mut!(GLOBAL_EV));
                    lean_io_result_mk_ok(promise)
                }
                SignalState::Finished => {
                    if !(*signal).promise.is_null() {
                        lean_inc((*signal).promise);
                        let promise = (*signal).promise;
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
                        b"invalid signal state\0".as_ptr().cast(),
                    )))
                }
            }
        } else if SignalState::from_i32((*signal).state) == SignalState::Initial {
            setup_signal(obj, signal)
        } else if !(*signal).promise.is_null() {
            lean_inc((*signal).promise);
            let promise = (*signal).promise;
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));
            lean_io_result_mk_ok(promise)
        } else {
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));
            let finished_promise = lean_io_promise_new();
            lean_io_result_mk_ok(finished_promise)
        }
    }

    pub unsafe fn lean_uv_signal_stop(obj: *mut LeanObject) -> *mut LeanObject {
        let signal = signal_from_obj(obj);

        event_loop_lock(addr_of_mut!(GLOBAL_EV));

        if !(*signal).promise.is_null() {
            lean_dec((*signal).promise);
            (*signal).promise = null_mut();
        }

        if SignalState::from_i32((*signal).state) == SignalState::Running {
            let result = uv_signal_stop((*signal).uv_signal);
            event_loop_unlock(addr_of_mut!(GLOBAL_EV));

            (*signal).state = SignalState::Finished as c_int;
            lean_dec(obj);

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

    pub unsafe fn lean_uv_signal_cancel(obj: *mut LeanObject) -> *mut LeanObject {
        let signal = signal_from_obj(obj);

        event_loop_lock(addr_of_mut!(GLOBAL_EV));

        if SignalState::from_i32((*signal).state) == SignalState::Running && !(*signal).promise.is_null() {
            if (*signal).repeating {
                lean_dec((*signal).promise);
                (*signal).promise = null_mut();
            } else {
                uv_signal_stop((*signal).uv_signal);

                lean_dec((*signal).promise);
                (*signal).promise = null_mut();
                (*signal).state = SignalState::Initial as c_int;

                lean_dec(obj);
            }
        }

        event_loop_unlock(addr_of_mut!(GLOBAL_EV));
        lean_io_result_mk_ok(lean_box(0))
    }

    const SIGNAL_LAYOUT_ASSERTS: () = {
        assert!(core::mem::size_of::<uv_handle_t>() == 96);
        assert!(core::mem::align_of::<uv_handle_t>() == 8);
        assert!(core::mem::size_of::<uv_signal_t>() == 152);
        assert!(core::mem::align_of::<uv_signal_t>() == 8);
    };
}

pub use runtime_signal_impl::*;
