/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the panic, sorry, and stack trace helpers from src/runtime/object.cpp.

mod runtime_object_panic_impl {
    use crate::base::{
        c_void, lean_dec, lean_io_eprintln, lean_mk_string, lean_mk_string_from_bytes,
        lean_string_cstr, ptr, AtomicBool, LeanObject, Ordering,
    };
    #[cfg(unix)]
    use libloading::os::unix::Library as UnixLibrary;
    use std::io::Write;

    mod backtrace_impl {
        use super::*;
    }

    pub unsafe fn lean_internal_panic_unreachable() -> ! {
        lean_internal_panic("unreachable code has been reached")
    }

    pub unsafe fn lean_internal_panic_rc_overflow() -> ! {
        lean_internal_panic("reference counter overflowed")
    }

    pub unsafe fn lean_internal_panic_overflow() -> ! {
        lean_internal_panic("integer overflow in runtime computation")
    }

    pub fn lean_set_exit_on_panic(flag: bool) {
        G_EXIT_ON_PANIC.store(flag, Ordering::Relaxed);
    }

    pub unsafe fn lean_internal_set_exit_on_panic(exit: bool) -> *mut LeanObject {
        G_EXIT_ON_PANIC.store(exit, Ordering::Relaxed);
        lean_box(0)
    }

    pub fn lean_set_panic_messages(flag: bool) {
        G_PANIC_MESSAGES.store(flag, Ordering::Relaxed);
    }
    pub unsafe fn lean_dbg_stack_trace(fn_obj: *mut LeanObject) -> *mut LeanObject {
        backtrace_impl::print_backtrace(false);
        lean_apply_1(fn_obj, lean_box(0))
    }
}
