/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the Name primitives section from src/runtime/object.cpp.
// Include from lib.rs: include!("runtime_object_name.rs");

mod runtime_object_name_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

    #[inline]
    unsafe fn lean_nat_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
        if lean_is_scalar(a1) && lean_is_scalar(a2) {
            a1 == a2
        } else {
            crate::runtime_object_nat_int_impl::lean_nat_big_eq(a1, a2)
        }
    }
}
