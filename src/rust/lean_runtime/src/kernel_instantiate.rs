/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_instantiate_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_expr_instantiate1(a: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_expr_instantiate(a: *mut LeanObject, subst: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_expr_instantiate_range(
            a: *mut LeanObject,
            begin: *mut LeanObject,
            end: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_expr_instantiate_rev(
            a: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_expr_instantiate_rev_range(
            a: *mut LeanObject,
            begin: *mut LeanObject,
            end: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate1(
        a: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate1(a, e)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate(a, subst)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate_range(a, begin, end, subst)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate_rev(a, subst)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate_rev_range(a, begin, end, subst)
    }
}
