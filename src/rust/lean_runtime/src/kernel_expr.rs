/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_expr_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_expr_mk_data(
            hash: u64,
            bvarRange: *mut LeanObject,
            approxDepth: u32,
            hasFVar: u8,
            hasExprMVar: u8,
            hasLevelMVar: u8,
            hasLevelParam: u8,
        ) -> u64;
        fn lean_cxx_expr_mk_app_data(fData: u64, aData: u64) -> u64;
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

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_mk_data(
        hash: u64,
        bvarRange: *mut LeanObject,
        approxDepth: u32,
        hasFVar: u8,
        hasExprMVar: u8,
        hasLevelMVar: u8,
        hasLevelParam: u8,
    ) -> u64 {
        lean_cxx_expr_mk_data(hash, bvarRange, approxDepth, hasFVar, hasExprMVar, hasLevelMVar, hasLevelParam)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_mk_app_data(fData: u64, aData: u64) -> u64 {
        lean_cxx_expr_mk_app_data(fData, aData)
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
