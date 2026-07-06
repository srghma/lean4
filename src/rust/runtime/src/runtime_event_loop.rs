/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_event_loop_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::ptr;
    use core::ptr::null_mut;
    use core::sync::atomic::{AtomicI32, Ordering};
    use libuv_sys2::{
        uv_async_init, uv_async_send, uv_cond_init, uv_cond_signal, uv_cond_wait, uv_default_loop,
        uv_loop_alive, uv_loop_configure, uv_loop_t, uv_mutex_init_recursive, uv_mutex_lock,
        uv_mutex_trylock, uv_mutex_unlock, uv_run, uv_stop, uv_strerror,
    };

    const UV_LOOP_BLOCK_SIGNAL: c_uint = 0;
    const UV_METRICS_IDLE_TIME: c_uint = 1;
    const UV_RUN_ONCE: c_uint = 1;

    unsafe extern "C" {
        fn lean_internal_panic(msg: *const c_char) -> !;
    }

    unsafe fn check_uv(result: c_int, msg: &'static [u8]) {
        if result != 0 {
            let err = CStr::from_ptr(uv_strerror(result)).to_string_lossy();
            let text = std::ffi::CString::new(format!(
                "{}: {err}",
                CStr::from_bytes_with_nul(msg).unwrap().to_string_lossy()
            ))
            .expect("libuv error message has no NUL");
            lean_internal_panic(text.as_ptr());
        }
    }

    unsafe fn async_callback(handle: *mut uv_async_t) {
        uv_stop((*handle).prefix.loop_);
    }
    pub unsafe fn event_loop_init(event_loop: *mut EventLoop) {
        (*event_loop).loop_ = uv_default_loop();
        check_uv(
            uv_mutex_init_recursive(ptr::addr_of_mut!((*event_loop).mutex)),
            b"Failed to initialize mutex\0",
        );
        check_uv(
            uv_cond_init(ptr::addr_of_mut!((*event_loop).cond_var)),
            b"Failed to initialize condition variable\0",
        );
        check_uv(
            uv_async_init(
                (*event_loop).loop_,
                ptr::addr_of_mut!((*event_loop).async_),
                Some(async_callback),
            ),
            b"Failed to initialize async\0",
        );
        (*event_loop).n_waiters.store(0, Ordering::Relaxed);
    }
    pub unsafe fn event_loop_run_loop(event_loop: *mut EventLoop) {
        while uv_loop_alive((*event_loop).loop_) != 0 {
            uv_mutex_lock(ptr::addr_of_mut!((*event_loop).mutex));

            while (*event_loop).n_waiters.load(Ordering::SeqCst) != 0 {
                uv_cond_wait(
                    ptr::addr_of_mut!((*event_loop).cond_var),
                    ptr::addr_of_mut!((*event_loop).mutex),
                );
            }

            uv_run((*event_loop).loop_, UV_RUN_ONCE);
            uv_mutex_unlock(ptr::addr_of_mut!((*event_loop).mutex));
        }
    }
    pub unsafe fn initialize_libuv_loop() {
        event_loop_init(ptr::addr_of_mut!(GLOBAL_EV));
    }
    pub unsafe fn lean_promise_resolve_with_code(status: c_int, promise: *mut LeanObject) {
        let result = if status == 0 {
            lean_runtime_alloc_ctor(1, 1, 0)
        } else {
            lean_runtime_alloc_ctor(0, 1, 0)
        };
        let value = if status == 0 {
            lean_box(0)
        } else {
            lean_decode_uv_error(status, null_mut())
        };
        lean_runtime_ctor_set(result, 0, value);
        lean_promise_resolve(result, promise);
    }

    pub unsafe fn lean_uv_event_loop_configure(options: *mut LeanObject) -> *mut LeanObject {
        let accum = lean_ctor_get_uint8(options, 0) != 0;
        let block = lean_ctor_get_uint8(options, 1) != 0;
        let event_loop = ptr::addr_of_mut!(GLOBAL_EV);

        event_loop_lock(event_loop);

        if accum {
            let result = uv_loop_configure((*event_loop).loop_, UV_METRICS_IDLE_TIME);
            if result != 0 {
                event_loop_unlock(event_loop);
                return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
            }
        }

        if block {
            let result =
                uv_loop_configure((*event_loop).loop_, UV_LOOP_BLOCK_SIGNAL, libc::SIGPROF);
            if result != 0 {
                event_loop_unlock(event_loop);
                return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
            }
        }

        event_loop_unlock(event_loop);
        lean_box(0)
    }

    pub unsafe fn lean_uv_event_loop_alive() -> u8 {
        let event_loop = ptr::addr_of_mut!(GLOBAL_EV);
        event_loop_lock(event_loop);
        let is_alive = uv_loop_alive((*event_loop).loop_) != 0;
        event_loop_unlock(event_loop);
        is_alive as u8
    }

    const _: () = {
        assert!(core::mem::size_of::<uv_mutex_t>() == 40);
        assert!(core::mem::align_of::<uv_mutex_t>() == 8);
        assert!(core::mem::size_of::<uv_cond_t>() == 48);
        assert!(core::mem::align_of::<uv_cond_t>() == 8);
        assert!(core::mem::size_of::<uv_async_t>() == 128);
        assert!(core::mem::align_of::<uv_async_t>() == 8);
        assert!(core::mem::size_of::<EventLoop>() == 232);
        assert!(core::mem::align_of::<EventLoop>() == 8);
    };
}

pub use runtime_event_loop_impl::*;
