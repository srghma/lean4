/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(all(feature = "std", not(target_family = "wasm")))]
mod runtime_libuv_impl {
    use super::*;
    use std::thread;

    #[repr(C)]
    struct EventLoop {
        _private: [u8; 0],
    }

    use libuv_sys2::{uv_setup_args as uv_setup_args_sys, uv_version as uv_version_sys};

    extern "C" {
        fn initialize_libuv_timer();
        fn initialize_libuv_tcp_socket();
        fn initialize_libuv_udp_socket();
        fn initialize_libuv_signal();
        fn initialize_libuv_loop();
        fn event_loop_run_loop(event_loop: *mut EventLoop);
        static mut GLOBAL_EV: EventLoop;

        fn lean_initialize_thread();
        fn lean_finalize_thread();
    }

    unsafe fn uv_setup_args(argc: c_int, argv: *mut *mut c_char) -> *mut *mut c_char {
        uv_setup_args_sys(argc, argv)
    }

    unsafe fn uv_version() -> c_uint {
        uv_version_sys()
    }

    pub unsafe fn initialize_libuv() {
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

    pub unsafe fn lean_setup_args(argc: c_int, argv: *mut *mut c_char) -> *mut *mut c_char {
        // duplicate in undefined at line 46 (🔁)
        uv_setup_args(argc, argv)
    }

    pub unsafe fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject {
        lean_box(uv_version() as usize)
    }
}

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub use runtime_libuv_impl::*;

#[cfg(all(feature = "std", target_family = "wasm"))]
mod runtime_libuv_impl {
    use super::*;

    pub fn initialize_libuv() {}

    pub unsafe fn lean_setup_args(_: c_int, argv: *mut *mut c_char) -> *mut *mut c_char {
        // duplicate in undefined at line 64 (🔁)
        argv
    }

    pub unsafe fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject {
        lean_box(0)
    }
}

#[cfg(all(feature = "std", target_family = "wasm"))]
pub use runtime_libuv_impl::*;
