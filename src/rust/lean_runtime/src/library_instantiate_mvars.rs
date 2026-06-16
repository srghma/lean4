/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_instantiate_mvars_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_instantiate_level_mvars(
            m: *mut LeanObject,
            l: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_instantiate_expr_mvars(
            m: *mut LeanObject,
            e: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_level_mvars(
        m: *mut LeanObject,
        l: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_instantiate_level_mvars(m, l)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_expr_mvars(
        m: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_instantiate_expr_mvars(m, e)
    }
}
