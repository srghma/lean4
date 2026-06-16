/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_elab_environment_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_elab_add_decl(
            env: *mut LeanObject,
            max_heartbeat: usize,
            decl: *mut LeanObject,
            opt_cancel_tk: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_elab_add_decl_without_checking(
            env: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_kernel_is_def_eq(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
            b: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_kernel_whnf(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_kernel_check(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_elab_add_decl(
        env: *mut LeanObject,
        max_heartbeat: usize,
        decl: *mut LeanObject,
        opt_cancel_tk: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_elab_add_decl(env, max_heartbeat, decl, opt_cancel_tk)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_elab_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_elab_add_decl_without_checking(env, decl)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_is_def_eq(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_kernel_is_def_eq(env, lctx, a, b)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_whnf(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_kernel_whnf(env, lctx, a)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_check(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_kernel_check(env, lctx, a)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_internal_get_believer_trust_level(
        _io: *mut LeanObject,
    ) -> u32 {
        1024
    }
}
