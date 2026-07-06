/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_libuv_impl {
    use crate::base::{LeanObject, c_char, c_int, c_uint, lean_box};
    use crate::runtime_event_loop::{EventLoop, GLOBAL_EV, event_loop_run_loop};
    use crate::runtime_signal::initialize_libuv_signal;
    use crate::runtime_tcp::initialize_libuv_tcp_socket;
    use crate::runtime_thread::{lean_finalize_thread, lean_initialize_thread};
    use crate::runtime_timer::initialize_libuv_timer;
    use crate::runtime_udp::initialize_libuv_udp_socket;
    use core::ptr;
    use std::thread;

    use libuv_sys2::{uv_setup_args as uv_setup_args_sys, uv_version as uv_version_sys};

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

    pub unsafe fn lean_setup_args(argc: c_int, argv: *mut *mut c_char) -> *mut *mut c_char { // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 411 (🔁)

        uv_setup_args(argc, argv)
    }

    pub unsafe fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject {
        lean_box(uv_version() as usize)
    }
}

pub use runtime_libuv_impl::*;
