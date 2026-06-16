/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_abstract_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_expr_abstract_range(
            e: *mut LeanObject,
            n: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_expr_abstract(
            e: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_abstract_range(
        e: *mut LeanObject,
        n: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_abstract_range(e, n, subst)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_abstract(
        e: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_abstract(e, subst)
    }
}
