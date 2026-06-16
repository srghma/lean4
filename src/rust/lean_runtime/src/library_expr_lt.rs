/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_expr_lt_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_expr_quick_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8;
        fn lean_cxx_expr_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_quick_lt(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        lean_cxx_expr_quick_lt(a, b)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_lt(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        lean_cxx_expr_lt(a, b)
    }
}
