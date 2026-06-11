// Port of kernel/expr.cpp
// Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Authors: Leonardo de Moura, Soonho Kong
// Ported to Rust.
//
// NOTE: expr.cpp has several LEAN_EXPORT functions with pure numeric/bit-packing
// logic that can be ported directly, plus initialize_expr / finalize_expr.
// C++ class methods (mk_*, update_*, get_app_*, etc.) stay in C++.

mod kernel_expr_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_initialize_expr();
        fn lean_cxx_finalize_expr();
        fn lean_cxx_expr_has_loose_bvar(e: *mut LeanObject, i: *mut LeanObject) -> u8;
        fn lean_cxx_expr_lower_loose_bvars(
            e: *mut LeanObject,
            s: *mut LeanObject,
            d: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_expr_lift_loose_bvars(
            e: *mut LeanObject,
            s: *mut LeanObject,
            d: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    // -----------------------------------------------------------------------
    // lean_expr_mk_data — pure bit-packing, fully portable to Rust
    //
    // Layout (64-bit word):
    //   bits [31:0]  = hash (lower 32 bits)
    //   bits [39:32] = approxDepth (clamped to 255)
    //   bit  40      = hasFVar
    //   bit  41      = hasExprMVar
    //   bit  42      = hasLevelMVar
    //   bit  43      = hasLevelParam
    //   bits [63:44] = bvarRange (20-bit, max 1048575)
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_mk_data(
        hash: u64,
        bvar_range: *mut LeanObject, // boxed Nat, must be scalar
        mut approx_depth: u32,
        has_fvar: u8,
        has_expr_mvar: u8,
        has_level_mvar: u8,
        has_level_param: u8,
    ) -> u64 {
        if approx_depth > 255 {
            approx_depth = 255;
        }
        if !lean_is_scalar(bvar_range) {
            lean_internal_panic(b"too many bound variables\0".as_ptr() as *const i8);
        }
        let range = lean_unbox(bvar_range) as usize;
        if range > 1_048_575 {
            lean_internal_panic(b"too many bound variables\0".as_ptr() as *const i8);
        }
        let h = hash as u32 as u64;
        let r = range as u64;
        h | ((approx_depth as u64) << 32)
            | ((has_fvar as u64) << 40)
            | ((has_expr_mvar as u64) << 41)
            | ((has_level_mvar as u64) << 42)
            | ((has_level_param as u64) << 43)
            | (r << 44)
    }

    // -----------------------------------------------------------------------
    // lean_expr_mk_app_data — pure bit arithmetic, portable to Rust
    // -----------------------------------------------------------------------
    #[inline(always)]
    fn approx_depth(data: u64) -> u64 {
        (data >> 32) & 0xFF
    }
    #[inline(always)]
    fn bvar_range(data: u64) -> u64 {
        data >> 44
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_mk_app_data(f_data: u64, a_data: u64) -> u64 {
        let mut depth = approx_depth(f_data).max(approx_depth(a_data)) + 1;
        if depth > 255 {
            depth = 255;
        }
        let range = bvar_range(f_data).max(bvar_range(a_data));
        // hash(f_data, a_data) — same mix as the C++ runtime/hash.h
        let h = {
            let a = f_data as u32;
            let b = a_data as u32;
            let mut v = a.wrapping_add(b.wrapping_add(0xA3B1_95DB));
            v ^= v >> 16;
            v = v.wrapping_mul(0x45D9F3B3);
            v ^= v >> 16;
            v as u64
        };
        // flags: union of hasFVar | hasExprMVar | hasLevelMVar | hasLevelParam bits
        let flags = (f_data | a_data) & (0x0Fu64 << 40);
        flags | h | (depth << 32) | (range << 44)
    }

    // -----------------------------------------------------------------------
    // lean_expr_has_loose_bvar — delegate (uses for_each internally)
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_has_loose_bvar(
        e: *mut LeanObject,
        i: *mut LeanObject,
    ) -> u8 {
        lean_cxx_expr_has_loose_bvar(e, i)
    }

    // -----------------------------------------------------------------------
    // lean_expr_lower_loose_bvars / lean_expr_lift_loose_bvars
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_lower_loose_bvars(
        e: *mut LeanObject,
        s: *mut LeanObject,
        d: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_lower_loose_bvars(e, s, d)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_lift_loose_bvars(
        e: *mut LeanObject,
        s: *mut LeanObject,
        d: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_lift_loose_bvars(e, s, d)
    }

    // -----------------------------------------------------------------------
    // Module init / finalize
    // -----------------------------------------------------------------------
    #[export_name = "_ZN4lean15initialize_exprEv"]
    pub unsafe extern "C" fn initialize_expr() {
        lean_cxx_initialize_expr();
    }

    #[export_name = "_ZN4lean13finalize_exprEv"]
    pub unsafe extern "C" fn finalize_expr() {
        lean_cxx_finalize_expr();
    }
}
