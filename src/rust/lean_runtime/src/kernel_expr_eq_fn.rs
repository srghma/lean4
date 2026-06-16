/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_expr_eq_fn_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_expr_eqv(a: *mut LeanObject, b: *mut LeanObject) -> u8;
        fn lean_cxx_expr_equal(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_eqv(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
        lean_cxx_expr_eqv(a, b)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_equal(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
        lean_cxx_expr_equal(a, b)
    }
}
