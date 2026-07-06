/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(all(feature = "std", not(target_family = "wasm")))]
mod runtime_event_loop_impl {
    use crate::*;
    use core::ptr;
    use core::ptr::null_mut;
    use core::sync::atomic::{AtomicI32, Ordering};
    use libuv_sys2::{
        uv_async_init as uv_async_init_sys, uv_async_send as uv_async_send_sys,
        uv_cond_init as uv_cond_init_sys, uv_cond_signal as uv_cond_signal_sys,
        uv_cond_wait as uv_cond_wait_sys, uv_default_loop as uv_default_loop_sys,
        uv_loop_alive as uv_loop_alive_sys, uv_loop_configure as uv_loop_configure_sys,
        uv_loop_t, uv_mutex_init_recursive as uv_mutex_init_recursive_sys,
        uv_mutex_lock as uv_mutex_lock_sys, uv_mutex_trylock as uv_mutex_trylock_sys,
        uv_mutex_unlock as uv_mutex_unlock_sys, uv_run as uv_run_sys, uv_stop as uv_stop_sys,
        uv_strerror,
    };

    const UV_LOOP_BLOCK_SIGNAL: c_uint = 0;
    const UV_METRICS_IDLE_TIME: c_uint = 1;
    const UV_RUN_ONCE: c_uint = 1;

    #[repr(C, align(8))]
    struct UvMutex {
        storage: [u8; 40],
    }

    #[repr(C, align(8))]
    struct UvCond {
        storage: [u8; 48],
    }

    #[repr(C)]
    struct UvHandlePrefix {
        data: *mut c_void,
        loop_: *mut uv_loop_t,
    }

    #[repr(C, align(8))]
    struct UvAsync {
        prefix: UvHandlePrefix,
        rest: [u8; 112],
    }

    #[repr(C)]
    pub struct EventLoop {
        pub loop_: *mut uv_loop_t,
        mutex: UvMutex,
        cond_var: UvCond,
        async_: UvAsync,
        n_waiters: AtomicI32,
    }

    unsafe fn uv_default_loop() -> *mut uv_loop_t {
        uv_default_loop_sys().cast()
    }

    unsafe fn uv_mutex_init_recursive(mutex: *mut UvMutex) -> c_int {
        uv_mutex_init_recursive_sys(mutex.cast())
    }

    unsafe fn uv_cond_init(cond: *mut UvCond) -> c_int {
        uv_cond_init_sys(cond.cast())
    }

    unsafe fn uv_async_init(
        loop_: *mut uv_loop_t,
        async_: *mut UvAsync,
        cb: Option<unsafe fn(*mut UvAsync)>,
    ) -> c_int {
        uv_async_init_sys(
            loop_.cast(),
            async_.cast(),
            cb.map(|cb| core::mem::transmute(cb)),
        )
    }

    unsafe fn uv_mutex_trylock(mutex: *mut UvMutex) -> c_int {
        uv_mutex_trylock_sys(mutex.cast())
    }

    unsafe fn uv_mutex_lock(mutex: *mut UvMutex) {
        uv_mutex_lock_sys(mutex.cast())
    }

    unsafe fn uv_mutex_unlock(mutex: *mut UvMutex) {
        uv_mutex_unlock_sys(mutex.cast())
    }

    unsafe fn uv_cond_signal(cond: *mut UvCond) {
        uv_cond_signal_sys(cond.cast())
    }

    unsafe fn uv_cond_wait(cond: *mut UvCond, mutex: *mut UvMutex) {
        uv_cond_wait_sys(cond.cast(), mutex.cast())
    }

    unsafe fn uv_async_send(async_: *mut UvAsync) -> c_int {
        uv_async_send_sys(async_.cast())
    }

    unsafe fn uv_run(loop_: *mut uv_loop_t, mode: c_uint) -> c_int {
        uv_run_sys(loop_.cast(), mode)
    }

    unsafe fn uv_stop(loop_: *mut uv_loop_t) {
        uv_stop_sys(loop_.cast())
    }

    unsafe fn uv_loop_alive(loop_: *mut uv_loop_t) -> c_int {
        uv_loop_alive_sys(loop_.cast())
    }

    unsafe fn uv_loop_configure(loop_: *mut uv_loop_t, option: c_uint, arg: c_int) -> c_int {
        uv_loop_configure_sys(loop_.cast(), option, arg)
    }

    unsafe extern "C" {
        fn lean_internal_panic(msg: *const c_char) -> !;
    }

    pub static mut GLOBAL_EV: EventLoop = EventLoop {
        loop_: null_mut(),
        mutex: UvMutex { storage: [0; 40] },
        cond_var: UvCond { storage: [0; 48] },
        async_: UvAsync {
            prefix: UvHandlePrefix {
                data: null_mut(),
                loop_: null_mut(),
            },
            rest: [0; 112],
        },
        n_waiters: AtomicI32::new(0),
    };

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

    unsafe fn async_callback(handle: *mut UvAsync) {
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
    pub unsafe fn event_loop_interrupt(event_loop: *mut EventLoop) {
        let result = uv_async_send(ptr::addr_of_mut!((*event_loop).async_));
        debug_assert_eq!(result, 0);
    }
    pub unsafe fn event_loop_lock(event_loop: *mut EventLoop) {
        if uv_mutex_trylock(ptr::addr_of_mut!((*event_loop).mutex)) != 0 {
            (*event_loop).n_waiters.fetch_add(1, Ordering::SeqCst);
            event_loop_interrupt(event_loop);
            uv_mutex_lock(ptr::addr_of_mut!((*event_loop).mutex));
            (*event_loop).n_waiters.fetch_sub(1, Ordering::SeqCst);
        }
    }
    pub unsafe fn event_loop_unlock(event_loop: *mut EventLoop) {
        if (*event_loop).n_waiters.load(Ordering::SeqCst) == 0 {
            uv_cond_signal(ptr::addr_of_mut!((*event_loop).cond_var));
        }
        uv_mutex_unlock(ptr::addr_of_mut!((*event_loop).mutex));
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
            let result = uv_loop_configure((*event_loop).loop_, UV_LOOP_BLOCK_SIGNAL, libc::SIGPROF);
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
        assert!(core::mem::size_of::<UvMutex>() == 40);
        assert!(core::mem::align_of::<UvMutex>() == 8);
        assert!(core::mem::size_of::<UvCond>() == 48);
        assert!(core::mem::align_of::<UvCond>() == 8);
        assert!(core::mem::size_of::<UvAsync>() == 128);
        assert!(core::mem::align_of::<UvAsync>() == 8);
        assert!(core::mem::size_of::<EventLoop>() == 232);
        assert!(core::mem::align_of::<EventLoop>() == 8);
    };
}

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub use runtime_event_loop_impl::*;
