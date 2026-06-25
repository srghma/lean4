/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub(crate) mod runtime_libuv_impl {
    use super::*;
    use std::thread;

    #[repr(C)]
    struct EventLoop {
        _private: [u8; 0],
    }

    extern "C" {
        #[link_name = "_ZN4lean22initialize_libuv_timerEv"]
        fn initialize_libuv_timer();
        #[link_name = "_ZN4lean27initialize_libuv_tcp_socketEv"]
        fn initialize_libuv_tcp_socket();
        #[link_name = "_ZN4lean27initialize_libuv_udp_socketEv"]
        fn initialize_libuv_udp_socket();
        #[link_name = "_ZN4lean23initialize_libuv_signalEv"]
        fn initialize_libuv_signal();
        #[link_name = "_ZN4lean21initialize_libuv_loopEv"]
        fn initialize_libuv_loop();
        #[link_name = "_ZN4lean19event_loop_run_loopEPNS_12event_loop_tE"]
        fn event_loop_run_loop(event_loop: *mut EventLoop);
        #[link_name = "_ZN4lean9global_evE"]
        static mut GLOBAL_EV: EventLoop;

        fn lean_initialize_thread();
        fn lean_finalize_thread();
        fn uv_setup_args(argc: c_int, argv: *mut *mut c_char) -> *mut *mut c_char;
        fn uv_version() -> c_uint;
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn initialize_libuv() {
        initialize_libuv_timer();
        initialize_libuv_tcp_socket();
        initialize_libuv_udp_socket();
        initialize_libuv_signal();
        initialize_libuv_loop();

        let event_loop_addr = ptr::addr_of_mut!(GLOBAL_EV) as usize;
        thread::spawn(move || unsafe {
            lean_initialize_thread();
            event_loop_run_loop(event_loop_addr as *mut EventLoop);
            lean_finalize_thread();
        });
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_setup_args(
        argc: c_int,
        argv: *mut *mut c_char,
    ) -> *mut *mut c_char {
        uv_setup_args(argc, argv)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject {
        lean_box(uv_version() as usize)
    }
}

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub use runtime_libuv_impl::*;

#[cfg(all(feature = "std", target_family = "wasm"))]
pub(crate) mod runtime_libuv_impl {
    use super::*;

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn initialize_libuv() {}

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_setup_args(_: c_int, argv: *mut *mut c_char) -> *mut *mut c_char {
        argv
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject {
        lean_box(0)
    }
}

#[cfg(all(feature = "std", target_family = "wasm"))]
pub use runtime_libuv_impl::*;
