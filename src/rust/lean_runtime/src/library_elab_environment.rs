/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_elab_environment_impl {
    use super::*;

    extern "C" {
        // Lean-implemented: extract kernel env from elab env (both owned)
        fn lean_elab_environment_to_kernel_env(env: *mut LeanObject) -> *mut LeanObject;
        // Lean-implemented: create new elab env with updated kernel env (all owned)
        fn lean_elab_environment_update_base_after_kernel_add(
            env: *mut LeanObject,
            kenv: *mut LeanObject,
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

        fn lean_cxx_add_axiom(env: *mut LeanObject, decl: *mut LeanObject, check: u8) -> *mut LeanObject;
        fn lean_cxx_add_definition(env: *mut LeanObject, decl: *mut LeanObject, check: u8) -> *mut LeanObject;
        fn lean_cxx_add_theorem(env: *mut LeanObject, decl: *mut LeanObject, check: u8) -> *mut LeanObject;
        fn lean_cxx_add_opaque(env: *mut LeanObject, decl: *mut LeanObject, check: u8) -> *mut LeanObject;
        fn lean_cxx_add_mutual(env: *mut LeanObject, decl: *mut LeanObject, check: u8) -> *mut LeanObject;
        fn lean_cxx_add_quot_to_env(env: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_add_inductive_only(env: *mut LeanObject, decl: *mut LeanObject) -> *mut LeanObject;
    }

    const DECL_AXIOM_TAG: u8 = 0;
    const DECL_DEFINITION_TAG: u8 = 1;
    const DECL_THEOREM_TAG: u8 = 2;
    const DECL_OPAQUE_TAG: u8 = 3;
    const DECL_QUOT_TAG: u8 = 4;
    const DECL_MUTUAL_DEFINITION_TAG: u8 = 5;
    const DECL_INDUCTIVE_TAG: u8 = 6;

    const EXCEPT_ERROR_TAG: u8 = 0;
    const EXCEPT_OK_TAG: u8 = 1;

    // Dispatch kernel-env add on declaration kind (check=1 → type-check, check=0 → skip).
    // CONSUMES kernel_env. BORROWS decl (caller must not use decl after this call returning Err).
    unsafe fn kernel_add_dispatch(
        kernel_env: *mut LeanObject,
        decl: *mut LeanObject,
        check: u8,
    ) -> *mut LeanObject {
        match lean_obj_tag(decl) {
            DECL_AXIOM_TAG             => lean_cxx_add_axiom(kernel_env, decl, check),
            DECL_DEFINITION_TAG        => lean_cxx_add_definition(kernel_env, decl, check),
            DECL_THEOREM_TAG           => lean_cxx_add_theorem(kernel_env, decl, check),
            DECL_OPAQUE_TAG            => lean_cxx_add_opaque(kernel_env, decl, check),
            DECL_QUOT_TAG              => lean_cxx_add_quot_to_env(kernel_env),
            DECL_MUTUAL_DEFINITION_TAG => lean_cxx_add_mutual(kernel_env, decl, check),
            DECL_INDUCTIVE_TAG         => lean_cxx_add_inductive_only(kernel_env, decl),
            _ => {
                lean_dec(kernel_env);
                let msg = lean_mk_string(b"unknown declaration kind\0".as_ptr().cast());
                let err_ctor = lean_runtime_alloc_ctor(12, 1, 0); // KernelException.other
                lean_runtime_ctor_set(err_ctor, 0, msg);
                let except_err = lean_runtime_alloc_ctor(EXCEPT_ERROR_TAG as u32, 1, 0);
                lean_runtime_ctor_set(except_err, 0, err_ctor);
                except_err
            }
        }
    }

    /// Common implementation for lean_elab_add_decl and lean_elab_add_decl_without_checking.
    ///
    /// CONSUMES elab_env. BORROWS decl (caller-side @& in Lean).
    unsafe fn elab_add_decl_impl(
        elab_env: *mut LeanObject,
        decl: *mut LeanObject,
        check: u8,
    ) -> *mut LeanObject {
        // Keep elab_env alive while we extract the kernel env.
        lean_inc_ref(elab_env);
        let kernel_env = lean_elab_environment_to_kernel_env(elab_env);
        // elab_env refcount is now back to its original value (lean_inc then lean_dec inside).

        let result = kernel_add_dispatch(kernel_env, decl, check);

        if lean_obj_tag(result) == EXCEPT_OK_TAG {
            // Unwrap Except.ok(new_kernel_env)
            let new_kernel_env = lean_ctor_get(result, 0);
            lean_inc(new_kernel_env);
            lean_dec(result);

            // decl is borrowed; lean_elab_environment_update_base_after_kernel_add expects owned.
            lean_inc(decl);

            let new_elab_env =
                lean_elab_environment_update_base_after_kernel_add(elab_env, new_kernel_env, decl);

            // Wrap new_elab_env in Except.ok
            let ok = lean_runtime_alloc_ctor(EXCEPT_OK_TAG as u32, 1, 0);
            lean_runtime_ctor_set(ok, 0, new_elab_env);
            ok
        } else {
            // Error path: release the elab_env we held onto.
            lean_dec(elab_env);
            result
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_elab_add_decl(
        env: *mut LeanObject,
        max_heartbeat: usize,
        decl: *mut LeanObject,
        opt_cancel_tk: *mut LeanObject,
    ) -> *mut LeanObject {
        let old_max = scope_max_heartbeat_push(max_heartbeat);
        let cancel_tk = if lean_is_scalar(opt_cancel_tk) {
            core::ptr::null_mut()
        } else {
            lean_ctor_get(opt_cancel_tk, 0)
        };
        let old_tk = scope_cancel_tk_push(cancel_tk);

        let result = elab_add_decl_impl(env, decl, 1);

        scope_max_heartbeat_pop(old_max);
        scope_cancel_tk_pop(old_tk);

        result
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_elab_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        elab_add_decl_impl(env, decl, 0)
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
