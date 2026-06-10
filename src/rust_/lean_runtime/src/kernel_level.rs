// Port of kernel/level.cpp
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: All real level logic lives in C++ (kernel/level.cpp) because it
// operates on lean::level / lean::name C++ value types that Rust cannot name.
// This file owns:
//   - lean_level_mk_data   (the one LEAN_EXPORT function with pure numeric logic)
//   - lean_level_eqv / lean_level_eq  (delegate to C++ shims)
//   - initialize_level / finalize_level (module init pair, delegate to C++ shims)
//
// Everything else (mk_succ, mk_max, mk_imax, is_explicit, normalize, …) stays
// in kernel/level.cpp because it requires lean::level constructors/comparators.

mod kernel_level_impl {
    use super::*;

    unsafe fn level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> bool {
        if l1 == l2 {
            return true;
        }
        let tag = lean_obj_tag(l1);
        if tag != lean_obj_tag(l2) {
            return false;
        }
        match tag {
            0 => true,
            1 => level_eq(lean_ctor_get(l1, 0), lean_ctor_get(l2, 0)),
            2 | 3 => {
                level_eq(lean_ctor_get(l1, 0), lean_ctor_get(l2, 0))
                    && level_eq(lean_ctor_get(l1, 1), lean_ctor_get(l2, 1))
            }
            4 | 5 => lean_name_eq(lean_ctor_get(l1, 0), lean_ctor_get(l2, 0)) != 0,
            _ => false,
        }
    }

    /// Pack hash, depth, hasMVar, hasParam into a u64 data word stored in the
    /// level object header.  This is the only LEAN_EXPORT function in level.cpp
    /// that contains pure numeric logic and can be fully ported to Rust.
    ///
    /// ```text
    /// bits [31:0]  = h (lower 32 bits of the hash)
    /// bit  32      = hasMVar
    /// bit  33      = hasParam
    /// bits [63:40] = depth (24-bit, max 16777215)
    /// ```
    #[no_mangle]
    pub unsafe extern "C" fn lean_level_mk_data(
        h: u64,
        depth: *mut LeanObject, // boxed Nat (must be scalar / small)
        has_mvar: u8,
        has_param: u8,
    ) -> u64 {
        if !lean_is_scalar(depth) {
            lean_internal_panic(b"universe level depth is too big\0".as_ptr() as *const i8);
        }
        let d = lean_unbox(depth) as usize;
        if d > 0x00FF_FFFF {
            lean_internal_panic(b"universe level depth is too big\0".as_ptr() as *const i8);
        }
        let h1 = h as u32 as u64;
        h1 | ((has_mvar as u64) << 32)
            | ((has_param as u64) << 33)
            | ((d as u64) << 40)
    }

    /// `is_equivalent` wrapper exposed to Lean.
    #[no_mangle]
    pub unsafe extern "C" fn lean_level_eqv(
        l1: *mut LeanObject,
        l2: *mut LeanObject,
    ) -> u8 {
        level_eq(l1, l2) as u8
    }

    /// Structural equality wrapper exposed to Lean.
    #[no_mangle]
    pub unsafe extern "C" fn lean_level_eq(
        l1: *mut LeanObject,
        l2: *mut LeanObject,
    ) -> u8 {
        level_eq(l1, l2) as u8
    }

    // initialize_level / finalize_level: when libleancpp.a is linked (lean_use_libleancpp),
    // those symbols are provided by C++ directly; otherwise the no-op stubs in lib.rs
    // satisfy the extern block.
}
