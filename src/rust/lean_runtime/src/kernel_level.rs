use crate::*;

/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of the exported raw level operations previously backed by kernel/level.cpp:
  lean_level_mk_data, lean_level_eqv, lean_level_eq, initialize_level, finalize_level

The C++ value-type facade now lives inline in kernel/level.h.
*/

pub(crate) mod kernel_level_impl {
    use super::runtime_object_name_impl::lean_name_eq;
    use super::runtime_object_rc_impl::lean_mark_persistent;
    use super::runtime_object_panic_impl::lean_internal_panic;
    use super::*;
    use core::ptr;

    static mut G_LEVEL_ZERO: *mut LeanObject = ptr::null_mut();
    static mut G_LEVEL_ONE: *mut LeanObject = ptr::null_mut();

    extern "C" {
        fn lean_level_mk_zero() -> *mut LeanObject;
        fn lean_level_mk_succ(l: *mut LeanObject) -> *mut LeanObject;
    }

    // Structural equality on lean Level objects (mirrors C++ operator==).
    // Level tags:
    //   0 = zero (scalar lean_box(0), caught by pointer equality above)
    //   1 = succ  — 1 obj field: inner level
    //   2 = max   — 2 obj fields: lhs, rhs
    //   3 = imax  — 2 obj fields: lhs, rhs
    //   4 = param — 1 obj field: Name
    //   5 = mvar  — 1 obj field: LevelMVarId (a Name)
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

    // Pack hash, depth, hasMVar, hasParam into a u64 data word stored in the
    // level object header (see lean_level_data in static runtime layout).
    // bits [31:0]  = h (lower 32 bits of the hash)
    // bit  32      = hasMVar
    // bit  33      = hasParam
    // bits [63:40] = depth (24-bit, max 16777215 = 0x00FFFFFF)
    #[inline]
    pub(crate) unsafe fn lean_level_mk_data(
        h: u64,
        depth: *mut LeanObject,
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
        h1 | ((has_mvar as u64) << 32) | ((has_param as u64) << 33) | ((d as u64) << 40)
    }

    #[inline]
    pub(crate) unsafe fn lean_level_eqv(l1: *mut LeanObject, l2: *mut LeanObject) -> u8 {
        level_eq(l1, l2) as u8
    }

    #[inline]
    pub(crate) unsafe fn lean_level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> u8 {
        level_eq(l1, l2) as u8
    }

    pub unsafe fn initialize_level() {
        if G_LEVEL_ZERO.is_null() {
            let zero = lean_level_mk_zero();
            lean_mark_persistent(zero);
            G_LEVEL_ZERO = zero;

            let one = lean_level_mk_succ(zero);
            lean_mark_persistent(one);
            G_LEVEL_ONE = one;
        }
    }

    pub unsafe fn finalize_level() {
        lean_dec(G_LEVEL_ONE);
        lean_dec(G_LEVEL_ZERO);
        G_LEVEL_ONE = ptr::null_mut();
        G_LEVEL_ZERO = ptr::null_mut();
    }
}
