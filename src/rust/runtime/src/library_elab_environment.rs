/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod library_elab_environment_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

    unsafe extern "C" {
        // Lean-implemented: extract kernel env from elab env (both owned)
        fn lean_elab_environment_to_kernel_env(env: *mut LeanObject) -> *mut LeanObject;
        // Lean-implemented: create new elab env with updated kernel env (all owned)
        fn lean_elab_environment_update_base_after_kernel_add(
            env: *mut LeanObject,
            kenv: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;

        // Unified Rust dispatch (kernel_type_checker.rs): axiom/def/theorem/opaque checked +
        // added in Rust; quot/mutual/inductive still delegate to the C++ bridges internally.
        fn lean_rust_add_decl(
            env: *mut LeanObject,
            decl: *mut LeanObject,
            check: bool,
        ) -> *mut LeanObject;
    }

    const EXCEPT_ERROR_TAG: u8 = 0;
    const EXCEPT_OK_TAG: u8 = 1;

    // Dispatch kernel-env add on declaration kind (check=1 → type-check, check=0 → skip).
    // CONSUMES kernel_env. BORROWS decl (caller must not use decl after this call returning Err).
    #[inline(always)]
    unsafe fn kernel_add_dispatch(
        kernel_env: *mut LeanObject,
        decl: *mut LeanObject,
        check: bool,
    ) -> *mut LeanObject {
        lean_rust_add_decl(kernel_env, decl, check)
    }

    /// Common implementation for lean_elab_add_decl and lean_elab_add_decl_without_checking.
    ///
    /// CONSUMES elab_env. BORROWS decl (caller-side @& in Lean).
    unsafe fn elab_add_decl_impl(
        elab_env: *mut LeanObject,
        decl: *mut LeanObject,
        check: bool,
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
            let ok = lean_alloc_ctor(EXCEPT_OK_TAG as u32, 1, 0);
            lean_ctor_set(ok, 0, new_elab_env);
            ok
        } else {
            // Error path: release the elab_env we held onto.
            lean_dec(elab_env);
            result
        }
    }

    #[no_mangle]
    pub unsafe fn lean_elab_add_decl(
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

        let result = elab_add_decl_impl(env, decl, true);

        scope_max_heartbeat_pop(old_max);
        scope_cancel_tk_pop(old_tk);

        result
    }

    #[no_mangle]
    pub unsafe fn lean_elab_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        elab_add_decl_impl(env, decl, false)
    }

    // lean_kernel_is_def_eq / lean_kernel_whnf / lean_kernel_check now in kernel_type_checker.rs
    // using the Rust TypeChecker with elab→kernel env conversion.

    #[no_mangle]
    pub unsafe fn lean_internal_get_believer_trust_level(_io: *const LeanObject) -> u32 {
        1024
    }
}
