/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of the LEAN_EXPORT functions in kernel/expr.cpp:
  lean_expr_mk_data, lean_expr_mk_app_data — pure bit-packing, fully in Rust
  lean_expr_has_loose_bvar, lean_expr_lower_loose_bvars, lean_expr_lift_loose_bvars
    — delegate to C++ shims (use lean::expr C++ template algorithms internally)
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_expr_impl {
    use super::*;
    use super::runtime_object_panic_impl::lean_internal_panic;

    extern "C" {
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

    // Mirror of lean::hash(h, k) from runtime/hash.h (MurmurHash-inspired 64-bit mixer).
    #[inline(always)]
    fn lean_hash_mix(h: u64, k: u64) -> u32 {
        const M: u64 = 0xc6a4a7935bd1e995;
        const R: u32 = 47;
        let k = k.wrapping_mul(M);
        let k = k ^ (k >> R);
        let k = k ^ M;
        let h = h ^ k;
        h.wrapping_mul(M) as u32
    }

    #[inline(always)]
    fn approx_depth(data: u64) -> u64 {
        (data >> 32) & 0xFF
    }

    #[inline(always)]
    fn bvar_range(data: u64) -> u64 {
        data >> 44
    }

    // Pack hash, bvarRange, approxDepth, flags into a u64 data word.
    // Layout:
    //   bits [31:0]  = hash (lower 32 bits)
    //   bits [39:32] = approxDepth (clamped to 255)
    //   bit  40      = hasFVar
    //   bit  41      = hasExprMVar
    //   bit  42      = hasLevelMVar
    //   bit  43      = hasLevelParam
    //   bits [63:44] = bvarRange (20-bit, max 1048575)
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_mk_data(
        hash: u64,
        bvar_range: *mut LeanObject,
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

    // Pack app data: inherit max depth+1, max range, union of flags, and hash of both data words.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_mk_app_data(f_data: u64, a_data: u64) -> u64 {
        let mut depth = approx_depth(f_data).max(approx_depth(a_data)) + 1;
        if depth > 255 {
            depth = 255;
        }
        let range = bvar_range(f_data).max(bvar_range(a_data));
        let h = lean_hash_mix(f_data, a_data) as u64;
        let flags = (f_data | a_data) & (0x0Fu64 << 40);
        flags | h | (depth << 32) | (range << 44)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_has_loose_bvar(
        e: *mut LeanObject,
        i: *mut LeanObject,
    ) -> u8 {
        lean_cxx_expr_has_loose_bvar(e, i)
    }

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
}
