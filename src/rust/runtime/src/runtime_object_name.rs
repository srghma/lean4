/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the Name primitives section from src/runtime/object.cpp.
// Include from lib.rs: include!("runtime_object_name.rs");

mod runtime_object_name_impl {
    use crate::*;

    // Reads the cached hash u64 stored after the 2 lean_object* fields.
    // Layout (64-bit): [LeanObject header (8)] [field0 ptr (8)] [field1 ptr (8)] [hash u64 (8)]
    #[inline]
    unsafe fn lean_name_hash_ptr(n: *mut LeanObject) -> u64 {
        lean_ctor_get_uint64(n, core::mem::size_of::<*mut LeanObject>() * 2)
    }

    #[inline]
    unsafe fn lean_string_eq(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
        s1 == s2
            || (lean_string_size(s1) == lean_string_size(s2)
                && runtime_object_string_impl::lean_string_eq_cold(s1, s2))
    }

    #[inline]
    unsafe fn lean_nat_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
        if lean_is_scalar(a1) && lean_is_scalar(a2) {
            a1 == a2
        } else {
            crate::runtime_object_nat_int_impl::lean_nat_big_eq(a1, a2)
        }
    }

    #[inline(always)]
    pub(crate) unsafe fn lean_name_eq(mut n1: *mut LeanObject, mut n2: *mut LeanObject) -> u8 {
        if n1 == n2 {
            return 1;
        }
        // If one is scalar (anonymous) and the other isn't, they differ.
        if lean_is_scalar(n1) != lean_is_scalar(n2) {
            return 0;
        }
        // Both scalar but n1 != n2: can't happen for valid Names (anonymous = unique lean_box(0)).
        if lean_is_scalar(n1) {
            return 0;
        }
        // Both non-scalar: fast-reject by cached hash.
        if lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2) {
            return 0;
        }
        loop {
            debug_assert!(!lean_is_scalar(n1));
            debug_assert!(!lean_is_scalar(n2));
            if lean_ptr_tag(n1) != lean_ptr_tag(n2) {
                return 0;
            }
            if lean_ptr_tag(n1) == 1 {
                // Name.str: field 1 is the string component
                if !lean_string_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)) {
                    return 0;
                }
            } else {
                // Name.num: field 1 is the nat component
                if !lean_nat_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)) {
                    return 0;
                }
            }
            // Advance to prefix (field 0)
            n1 = lean_ctor_get(n1, 0);
            n2 = lean_ctor_get(n2, 0);
            if n1 == n2 {
                return 1;
            }
            if lean_is_scalar(n1) != lean_is_scalar(n2) {
                return 0;
            }
            // If both anonymous (scalar) but not equal — shouldn't happen for valid Names.
            if lean_is_scalar(n1) {
                return 0;
            }
        }
    }
}
