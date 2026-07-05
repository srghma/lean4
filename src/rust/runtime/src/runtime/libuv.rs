/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use leanh::*;
use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};


#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub(crate) mod runtime_libuv_impl {
    use std::thread;
    use crate::runtime::event_loop::runtime_event_loop_impl::{
        event_loop_run_loop, initialize_libuv_loop, EventLoop, _ZN4lean9global_evE as GLOBAL_EV,
    };
    use crate::runtime::signal::runtime_signal_impl::initialize_libuv_signal;
    use crate::runtime::tcp::runtime_tcp_impl::initialize_libuv_tcp_socket;
    use crate::runtime::timer::runtime_timer_impl::initialize_libuv_timer;
    use crate::runtime::runtime_thread_impl::{lean_finalize_thread, lean_initialize_thread};
    use crate::runtime::udp::runtime_udp_impl::initialize_libuv_udp_socket;

    extern "C" {
        fn uv_setup_args(argc: c_int, argv: *mut *mut c_char) -> *mut *mut c_char;
        fn uv_version() -> c_uint;
    }

    #[inline]
    pub(crate) unsafe fn initialize_libuv() {
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

    #[inline]
    pub(crate) unsafe fn lean_setup_args( // duplicate in leanh at line 47 (🔁)
        argc: c_int,
        argv: *mut *mut c_char,
    ) -> *mut *mut c_char {
        uv_setup_args(argc, argv)
    }

    #[inline]
    #[cfg(false)]
    pub(crate) unsafe fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject { // duplicate in leanh at line 56 (🔁) // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Lean/Runtime.lean:21
        lean_box(uv_version() as usize)
    }
}

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub(crate) use runtime_libuv_impl::*;

#[cfg(all(feature = "std", target_family = "wasm"))]
pub(crate) mod runtime_libuv_impl {

    #[inline]
    pub(crate) unsafe fn lean_setup_args(_: c_int, argv: *mut *mut c_char) -> *mut *mut c_char { // duplicate in leanh at line 69 (🔁)
        argv
    }

    #[inline]
    #[cfg(false)]
    pub(crate) unsafe fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject { // duplicate in leanh at line 75 (🔁)
        lean_box(0)
    }
}

#[cfg(all(feature = "std", target_family = "wasm"))]
pub(crate) use runtime_libuv_impl::*;
