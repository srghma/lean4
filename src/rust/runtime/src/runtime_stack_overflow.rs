/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(unix)]
mod runtime_stack_overflow_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use std::mem;
    use std::ptr;
    use std::sync::atomic::{AtomicPtr, Ordering};

    pub unsafe fn stack_guard_ctor_complete(this: *mut StackGuard) {
        stack_guard_ctor(this);
    }
    pub unsafe fn stack_guard_ctor_base(this: *mut StackGuard) {
        stack_guard_ctor(this);
    }
    pub unsafe fn stack_guard_dtor_base(this: *mut StackGuard) {
        stack_guard_dtor(this);
    }
}

#[cfg(unix)]
pub use runtime_stack_overflow_impl::*;
