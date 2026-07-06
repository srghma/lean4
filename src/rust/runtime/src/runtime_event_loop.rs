/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(all(feature = "std", not(target_family = "wasm")))]
mod runtime_event_loop_impl {
    use super::*;
    use core::ptr::null_mut;
    use core::sync::atomic::{AtomicI32, Ordering};

    const UV_LOOP_BLOCK_SIGNAL: c_uint = 0;
    const UV_METRICS_IDLE_TIME: c_uint = 1;
    const UV_RUN_ONCE: c_uint = 1;

    #[repr(C)]
    pub struct UvLoop {
        _private: [u8; 0],
    }

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
        loop_: *mut UvLoop,
    }

    #[repr(C, align(8))]
    struct UvAsync {
        prefix: UvHandlePrefix,
        rest: [u8; 112],
    }

    #[repr(C)]
    pub struct EventLoop {
        pub loop_: *mut UvLoop,
        mutex: UvMutex,
        cond_var: UvCond,
        async_: UvAsync,
        n_waiters: AtomicI32,
    }

    extern "C" {
        fn uv_default_loop() -> *mut UvLoop;
        fn uv_mutex_init_recursive(mutex: *mut UvMutex) -> c_int;
        fn uv_cond_init(cond: *mut UvCond) -> c_int;
        fn uv_async_init(
            loop_: *mut UvLoop,
            async_: *mut UvAsync,
            cb: Option<unsafe extern "C" fn(*mut UvAsync)>,
        ) -> c_int;
        fn uv_mutex_trylock(mutex: *mut UvMutex) -> c_int;
        fn uv_mutex_lock(mutex: *mut UvMutex);
        fn uv_mutex_unlock(mutex: *mut UvMutex);
        fn uv_cond_signal(cond: *mut UvCond);
        fn uv_cond_wait(cond: *mut UvCond, mutex: *mut UvMutex);
        fn uv_async_send(async_: *mut UvAsync) -> c_int;
        fn uv_run(loop_: *mut UvLoop, mode: c_uint) -> c_int;
        fn uv_stop(loop_: *mut UvLoop);
        fn uv_loop_alive(loop_: *mut UvLoop) -> c_int;
        fn uv_loop_configure(loop_: *mut UvLoop, option: c_uint, ...) -> c_int;
        fn uv_strerror(err: c_int) -> *const c_char;
        #[link_name = "lean_internal_panic"]
        fn lean_internal_panic(msg: *const c_char) -> !;
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub static mut _ZN4lean9global_evE: EventLoop = EventLoop {
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

    unsafe extern "C" fn async_callback(handle: *mut UvAsync) {
        uv_stop((*handle).prefix.loop_);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15event_loop_initEPNS_12event_loop_tE"
    )]
    pub unsafe extern "C" fn event_loop_init(event_loop: *mut EventLoop) {
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

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean20event_loop_interruptEPNS_12event_loop_tE"
    )]
    pub unsafe extern "C" fn event_loop_interrupt(event_loop: *mut EventLoop) {
        let result = uv_async_send(ptr::addr_of_mut!((*event_loop).async_));
        debug_assert_eq!(result, 0);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15event_loop_lockEPNS_12event_loop_tE"
    )]
    pub unsafe extern "C" fn event_loop_lock(event_loop: *mut EventLoop) {
        if uv_mutex_trylock(ptr::addr_of_mut!((*event_loop).mutex)) != 0 {
            (*event_loop).n_waiters.fetch_add(1, Ordering::SeqCst);
            event_loop_interrupt(event_loop);
            uv_mutex_lock(ptr::addr_of_mut!((*event_loop).mutex));
            (*event_loop).n_waiters.fetch_sub(1, Ordering::SeqCst);
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean17event_loop_unlockEPNS_12event_loop_tE"
    )]
    pub unsafe extern "C" fn event_loop_unlock(event_loop: *mut EventLoop) {
        if (*event_loop).n_waiters.load(Ordering::SeqCst) == 0 {
            uv_cond_signal(ptr::addr_of_mut!((*event_loop).cond_var));
        }
        uv_mutex_unlock(ptr::addr_of_mut!((*event_loop).mutex));
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean19event_loop_run_loopEPNS_12event_loop_tE"
    )]
    pub unsafe extern "C" fn event_loop_run_loop(event_loop: *mut EventLoop) {
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

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean21initialize_libuv_loopEv"
    )]
    pub unsafe extern "C" fn initialize_libuv_loop() {
        event_loop_init(ptr::addr_of_mut!(_ZN4lean9global_evE));
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean30lean_promise_resolve_with_codeEiP11lean_object"
    )]
    pub unsafe extern "C" fn lean_promise_resolve_with_code(
        status: c_int,
        promise: *mut LeanObject,
    ) {
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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_event_loop_configure(
        options: *mut LeanObject,
    ) -> *mut LeanObject {
        let accum = lean_ctor_get_uint8(options, 0) != 0;
        let block = lean_ctor_get_uint8(options, 1) != 0;
        let event_loop = ptr::addr_of_mut!(_ZN4lean9global_evE);

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

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_event_loop_alive() -> u8 {
        let event_loop = ptr::addr_of_mut!(_ZN4lean9global_evE);
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
