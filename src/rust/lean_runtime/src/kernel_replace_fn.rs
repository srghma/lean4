/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_replace_fn_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_replace_expr(f: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_replace_expr(
        f: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_replace_expr(f, e)
    }
}
