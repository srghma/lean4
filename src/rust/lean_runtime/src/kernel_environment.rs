/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_environment_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_add_decl(
            env: *mut LeanObject,
            max_heartbeat: usize,
            decl: *mut LeanObject,
            opt_cancel_tk: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_add_decl_without_checking(
            env: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_add_decl(
        env: *mut LeanObject,
        max_heartbeat: usize,
        decl: *mut LeanObject,
        opt_cancel_tk: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_add_decl(env, max_heartbeat, decl, opt_cancel_tk)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_add_decl_without_checking(env, decl)
    }
}
