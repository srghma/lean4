/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of the exported raw level operations previously backed by kernel/level.cpp:
  lean_level_mk_data, lean_level_eqv, lean_level_eq, initialize_level, finalize_level

The C++ value-type facade now lives inline in kernel/level.h.
*/

mod kernel_level_impl {
    use crate::runtime_expr_shared::{LeanLevelKind, level_kind};
    use crate::runtime_object_name_impl::lean_name_eq;
    use crate::runtime_object_panic_impl::lean_internal_panic;
    use crate::*;
    use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};

    // Structural equality on lean Level objects (mirrors C++ operator==).
    // Level tags:
    //   0 = zero (scalar lean_box(0), caught by pointer equality above)
    //   1 = succ  — 1 obj field: inner level
    //   2 = max   — 2 obj fields: lhs, rhs
    //   3 = imax  — 2 obj fields: lhs, rhs
    //   4 = param — 1 obj field: Name
    //   5 = mvar  — 1 obj field: LevelMVarId (a Name)
    unsafe fn level_eq(l1: *const LeanObject, l2: *const LeanObject) -> bool {
        if l1 == l2 {
            return true;
        }
        let tag = level_kind(l1);
        if tag != level_kind(l2) {
            return false;
        }
        match tag {
            LeanLevelKind::Zero => true,
            LeanLevelKind::Succ => level_eq(lean_ctor_get(l1, 0), lean_ctor_get(l2, 0)),
            LeanLevelKind::Max | LeanLevelKind::IMax => {
                level_eq(lean_ctor_get(l1, 0), lean_ctor_get(l2, 0))
                    && level_eq(lean_ctor_get(l1, 1), lean_ctor_get(l2, 1))
            }
            LeanLevelKind::Param | LeanLevelKind::MVar => {
                lean_name_eq(lean_ctor_get(l1, 0), lean_ctor_get(l2, 0))
            }
        }
    }

    // Pack hash, depth, hasMVar, hasParam into a u64 data word stored in the
    // level object header (see lean_level_data in lean.h).
    // bits [31:0]  = h (lower 32 bits of the hash)
    // bit  32      = hasMVar
    // bit  33      = hasParam
    // bits [63:40] = depth (24-bit, max 16777215 = 0x00FFFFFF)
    #[no_mangle]
    pub unsafe fn lean_level_mk_data(
        h: u64,
        depth: *mut LeanObject,
        has_mvar: bool,
        has_param: bool,
    ) -> u64 {
        if !lean_is_scalar(depth) {
            lean_internal_panic("universe level depth is too big");
        }
        let d = lean_unbox(depth) as usize;
        if d > 0x00FF_FFFF {
            lean_internal_panic("universe level depth is too big");
        }
        let h1 = h as u32 as u64;
        h1 | ((has_mvar as u64) << 32) | ((has_param as u64) << 33) | ((d as u64) << 40)
    }

    #[no_mangle]
    pub unsafe fn lean_level_eqv(l1: *const LeanObject, l2: *const LeanObject) -> bool {
        level_eq(l1, l2)
    }

    #[no_mangle]
    pub unsafe fn lean_level_eq(l1: *const LeanObject, l2: *const LeanObject) -> bool {
        level_eq(l1, l2)
    }
}
