/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the panic, sorry, and stack trace helpers from src/runtime/object.cpp.

mod runtime_object_panic_impl {
    use crate::base::{
        AtomicBool, CStr, LeanObject, Ordering, c_char, c_int, c_void, lean_dec, lean_io_eprintln,
        lean_mk_string, lean_mk_string_from_bytes, lean_string_cstr, ptr,
    };
    #[cfg(unix)]
    use libloading::os::unix::Library as UnixLibrary;
    use std::io::Write;

    mod backtrace_impl {
        use super::*;
    }

    pub unsafe fn lean_internal_panic_unreachable() -> ! {
        lean_internal_panic(c_char_ptr(b"unreachable code has been reached\0"))
    }

    pub unsafe fn lean_internal_panic_rc_overflow() -> ! {
        lean_internal_panic(c_char_ptr(b"reference counter overflowed\0"))
    }

    pub unsafe fn lean_internal_panic_overflow() -> ! {
        lean_internal_panic(c_char_ptr(b"integer overflow in runtime computation\0"))
    }

    pub fn lean_set_exit_on_panic(flag: bool) {
        G_EXIT_ON_PANIC.store(flag, Ordering::Relaxed);
    }

    pub unsafe fn lean_internal_set_exit_on_panic(exit: u8) -> *mut LeanObject {
        G_EXIT_ON_PANIC.store(exit != 0, Ordering::Relaxed);
        lean_box(0)
    }

    pub fn lean_set_panic_messages(flag: bool) {
        G_PANIC_MESSAGES.store(flag, Ordering::Relaxed);
    }

    pub unsafe fn lean_panic_fn(
        default_val: *mut LeanObject,
        msg: *mut LeanObject,
    ) -> *mut LeanObject {
        let size = lean_string_size(msg).saturating_sub(1);
        let bytes = core::slice::from_raw_parts(lean_string_cstr(msg).cast::<u8>(), size);
        lean_panic_impl(bytes, false);
        lean_dec(msg);
        default_val
    }

    pub unsafe fn lean_panic_fn_borrowed(
        default_val: *mut LeanObject,
        msg: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_inc(default_val);
        lean_panic_fn(default_val, msg)
    }

    pub unsafe fn lean_sorry(_: u8) -> *mut LeanObject {
        lean_internal_panic(c_char_ptr(b"executed 'sorry'\0"))
    }

    pub unsafe fn lean_dbg_stack_trace(fn_obj: *mut LeanObject) -> *mut LeanObject {
        backtrace_impl::print_backtrace(false);
        lean_apply_1(fn_obj, lean_box(0))
    }
}
