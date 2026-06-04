/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(all(feature = "std", not(target_family = "wasm")))]
mod runtime_signal_impl {
    use super::*;
    use core::ptr::{addr_of_mut, null_mut};

    const SIGNAL_STATE_INITIAL: c_int = 0;
    const SIGNAL_STATE_RUNNING: c_int = 1;
    const SIGNAL_STATE_FINISHED: c_int = 2;
    const LEAN_TASK_STATE_FINISHED: u8 = 2;

    #[repr(C, align(8))]
    pub struct UvSignal {
        handle: UvHandle,
        rest: [u8; 56],
    }

    #[repr(C)]
    struct LeanUvSignalObject {
        uv_signal: *mut UvSignal,
        promise: *mut LeanObject,
        signum: c_int,
        repeating: bool,
        state: c_int,
    }

    static mut UV_SIGNAL_EXTERNAL_CLASS: *mut LeanExternalClass = null_mut();

    extern "C" {
        fn uv_close(handle: *mut UvHandle, close_cb: Option<unsafe extern "C" fn(*mut UvHandle)>);
        fn uv_signal_init(loop_: *mut UvLoop, handle: *mut UvSignal) -> c_int;
        fn uv_signal_start(
            handle: *mut UvSignal,
            cb: Option<unsafe extern "C" fn(*mut UvSignal, c_int)>,
            signum: c_int,
        ) -> c_int;
        fn uv_signal_start_oneshot(
            handle: *mut UvSignal,
            cb: Option<unsafe extern "C" fn(*mut UvSignal, c_int)>,
            signum: c_int,
        ) -> c_int;
        fn uv_signal_stop(handle: *mut UvSignal) -> c_int;
    }

    unsafe fn signal_from_obj(obj: *mut LeanObject) -> *mut LeanUvSignalObject {
        lean_runtime_get_external_data(obj).cast()
    }

    unsafe fn signal_promise_is_finished(signal: *mut LeanUvSignalObject) -> bool {
        let promise = (*signal).promise.cast::<LeanPromiseObject>();
        lean_io_get_task_state_core((*promise).result) == LEAN_TASK_STATE_FINISHED
    }

    unsafe extern "C" fn close_free_handle(handle: *mut UvHandle) {
        libc::free(handle.cast());
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean25lean_uv_signal_finalizerEPv")]
    pub unsafe extern "C" fn lean_uv_signal_finalizer(ptr: *mut c_void) {
        let signal = ptr.cast::<LeanUvSignalObject>();

        if !(*signal).promise.is_null() {
            lean_dec((*signal).promise);
        }

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        uv_close((*signal).uv_signal.cast::<UvHandle>(), Some(close_free_handle));
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        libc::free(signal.cast());
    }

    unsafe extern "C" fn signal_foreach(obj: *mut c_void, f: *mut LeanObject) {
        let signal = obj.cast::<LeanUvSignalObject>();
        if !(*signal).promise.is_null() {
            lean_inc(f);
            lean_apply_1(f, (*signal).promise);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean23initialize_libuv_signalEv")]
    pub unsafe extern "C" fn initialize_libuv_signal() {
        UV_SIGNAL_EXTERNAL_CLASS =
            lean_register_external_class(Some(lean_uv_signal_finalizer), Some(signal_foreach));
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean19handle_signal_eventEP11uv_signal_si")]
    pub unsafe extern "C" fn handle_signal_event(handle: *mut UvSignal, signum: c_int) {
        let obj = (*handle).handle.data.cast::<LeanObject>();
        let signal = signal_from_obj(obj);

        debug_assert_eq!((*signal).state, SIGNAL_STATE_RUNNING);

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
            (*signal).state = SIGNAL_STATE_FINISHED;
            lean_dec(obj);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_signal_mk(signum_obj: u32, repeating: u8) -> *mut LeanObject {
        let mut signum = signum_obj as c_int;

        #[cfg(not(target_os = "windows"))]
        match signum {
            1 => signum = libc::SIGHUP,
            2 => signum = libc::SIGINT,
            3 => signum = libc::SIGQUIT,
            6 => signum = libc::SIGABRT,
            15 => signum = libc::SIGTERM,
            28 => signum = libc::SIGWINCH,
            5 => signum = libc::SIGTRAP,
            10 => signum = libc::SIGUSR1,
            12 => signum = libc::SIGUSR2,
            14 => signum = libc::SIGALRM,
            17 => signum = libc::SIGCHLD,
            18 => signum = libc::SIGCONT,
            20 => signum = libc::SIGTSTP,
            21 => signum = libc::SIGTTIN,
            22 => signum = libc::SIGTTOU,
            23 => signum = libc::SIGURG,
            24 => signum = libc::SIGXCPU,
            25 => signum = libc::SIGXFSZ,
            26 => signum = libc::SIGVTALRM,
            27 => signum = libc::SIGPROF,
            29 => signum = libc::SIGIO,
            31 => signum = libc::SIGSYS,
            _ => signum = 0,
        }

        #[cfg(target_os = "windows")]
        match signum {
            1 => signum = libc::SIGHUP,
            2 => signum = libc::SIGINT,
            3 => signum = libc::SIGQUIT,
            6 => signum = libc::SIGABRT,
            15 => signum = libc::SIGTERM,
            28 => signum = libc::SIGWINCH,
            _ => signum = 0,
        }

        let signal = libc::malloc(core::mem::size_of::<LeanUvSignalObject>()).cast::<LeanUvSignalObject>();
        if signal.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        (*signal).signum = signum;
        (*signal).repeating = repeating != 0;
        (*signal).state = SIGNAL_STATE_INITIAL;
        (*signal).promise = null_mut();

        let uv_signal = libc::malloc(core::mem::size_of::<UvSignal>()).cast::<UvSignal>();
        if uv_signal.is_null() {
            libc::free(signal.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_signal_init(_ZN4lean9global_evE.loop_, uv_signal);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result != 0 {
            libc::free(uv_signal.cast());
            libc::free(signal.cast());
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        (*signal).uv_signal = uv_signal;

        let obj = lean_runtime_alloc_external(UV_SIGNAL_EXTERNAL_CLASS, signal.cast());
        lean_mark_mt(obj);
        (*uv_signal).handle.data = obj.cast();

        lean_io_result_mk_ok(obj)
    }

    unsafe fn setup_signal(obj: *mut LeanObject, signal: *mut LeanUvSignalObject) -> *mut LeanObject {
        debug_assert!((*signal).promise.is_null());

        let promise = lean_io_promise_new();
        (*signal).promise = promise;
        (*signal).state = SIGNAL_STATE_RUNNING;

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
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        lean_io_result_mk_ok(promise)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_signal_next(obj: *mut LeanObject) -> *mut LeanObject {
        let signal = signal_from_obj(obj);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if (*signal).repeating {
            match (*signal).state {
                SIGNAL_STATE_INITIAL => setup_signal(obj, signal),
                SIGNAL_STATE_RUNNING => {
                    if (*signal).promise.is_null() || signal_promise_is_finished(signal) {
                        if !(*signal).promise.is_null() {
                            lean_dec((*signal).promise);
                        }
                        (*signal).promise = lean_io_promise_new();
                    }

                    lean_inc((*signal).promise);
                    let promise = (*signal).promise;
                    event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
                    lean_io_result_mk_ok(promise)
                }
                SIGNAL_STATE_FINISHED => {
                    if !(*signal).promise.is_null() {
                        lean_inc((*signal).promise);
                        let promise = (*signal).promise;
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
                    lean_io_result_mk_error(lean_mk_io_user_error(
                        lean_mk_string(b"invalid signal state\0".as_ptr().cast()),
                    ))
                }
            }
        } else if (*signal).state == SIGNAL_STATE_INITIAL {
            setup_signal(obj, signal)
        } else if !(*signal).promise.is_null() {
            lean_inc((*signal).promise);
            let promise = (*signal).promise;
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            lean_io_result_mk_ok(promise)
        } else {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            let finished_promise = lean_io_promise_new();
            lean_io_result_mk_ok(finished_promise)
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_signal_stop(obj: *mut LeanObject) -> *mut LeanObject {
        let signal = signal_from_obj(obj);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if !(*signal).promise.is_null() {
            lean_dec((*signal).promise);
            (*signal).promise = null_mut();
        }

        if (*signal).state == SIGNAL_STATE_RUNNING {
            let result = uv_signal_stop((*signal).uv_signal);
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

            (*signal).state = SIGNAL_STATE_FINISHED;
            lean_dec(obj);

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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_signal_cancel(obj: *mut LeanObject) -> *mut LeanObject {
        let signal = signal_from_obj(obj);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if (*signal).state == SIGNAL_STATE_RUNNING && !(*signal).promise.is_null() {
            if (*signal).repeating {
                lean_dec((*signal).promise);
                (*signal).promise = null_mut();
            } else {
                uv_signal_stop((*signal).uv_signal);

                lean_dec((*signal).promise);
                (*signal).promise = null_mut();
                (*signal).state = SIGNAL_STATE_INITIAL;

                lean_dec(obj);
            }
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        lean_io_result_mk_ok(lean_box(0))
    }

    const _: () = {
        assert!(core::mem::size_of::<UvHandle>() == 96);
        assert!(core::mem::align_of::<UvHandle>() == 8);
        assert!(core::mem::size_of::<UvSignal>() == 152);
        assert!(core::mem::align_of::<UvSignal>() == 8);
    };
}

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub use runtime_signal_impl::*;

#[cfg(all(feature = "std", target_family = "wasm"))]
mod runtime_signal_impl {
    use super::*;

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_signal_mk(_: u32, _: u8) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_signal_next(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_signal_stop(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_signal_cancel(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
}

#[cfg(all(feature = "std", target_family = "wasm"))]
pub use runtime_signal_impl::*;
