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

    pub unsafe fn lean_promise_resolve_with_code(status: c_int, promise: *mut LeanObject) {
        let result = if status == 0 {
            lean_alloc_ctor(1, 1, 0)
        } else {
            lean_alloc_ctor(0, 1, 0)
        };
        let value = if status == 0 {
            lean_box(0)
        } else {
            lean_decode_uv_error(status, null_mut())
        };
        lean_ctor_set(result, 0, value);
        lean_promise_resolve(result, promise);
    }

    pub unsafe fn lean_uv_event_loop_configure(options: *mut LeanObject) -> *mut LeanObject {
        let accum = lean_ctor_get_uint8(options, 0) != 0;
        let block = lean_ctor_get_uint8(options, 1) != 0;
        let event_loop = ptr::addr_of_mut!(GLOBAL_EV);

        event_loop_lock(event_loop);

        if accum {
            let result =
                uv_loop_configure((*event_loop).loop_, uv_loop_option_UV_METRICS_IDLE_TIME);
            if result != 0 {
                event_loop_unlock(event_loop);
                return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
            }
        }

        if block {
            let result = uv_loop_configure(
                (*event_loop).loop_,
                uv_loop_option_UV_LOOP_BLOCK_SIGNAL,
                libc::SIGPROF,
            );
            if result != 0 {
                event_loop_unlock(event_loop);
                return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
            }
        }

        event_loop_unlock(event_loop);
        lean_box(0)
    }

    pub unsafe fn lean_uv_event_loop_alive() -> bool {
        let event_loop = ptr::addr_of_mut!(GLOBAL_EV);
        event_loop_lock(event_loop);
        let is_alive = uv_loop_alive((*event_loop).loop_) != 0;
        event_loop_unlock(event_loop);
        is_alive
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
