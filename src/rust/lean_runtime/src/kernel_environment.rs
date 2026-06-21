/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_environment_impl {
    use super::*;

    extern "C" {
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

    unsafe fn add_decl_dispatch(env: *mut LeanObject, decl: *mut LeanObject, check: u8) -> *mut LeanObject {
        match lean_obj_tag(decl) {
            DECL_AXIOM_TAG => lean_cxx_add_axiom(env, decl, check),
            DECL_DEFINITION_TAG => lean_cxx_add_definition(env, decl, check),
            DECL_THEOREM_TAG => lean_cxx_add_theorem(env, decl, check),
            DECL_OPAQUE_TAG => lean_cxx_add_opaque(env, decl, check),
            DECL_QUOT_TAG => lean_cxx_add_quot_to_env(env),
            DECL_MUTUAL_DEFINITION_TAG => lean_cxx_add_mutual(env, decl, check),
            DECL_INDUCTIVE_TAG => lean_cxx_add_inductive_only(env, decl),
            _ => {
                lean_dec(env);
                let msg = lean_mk_string(b"unknown declaration kind\0".as_ptr().cast());
                let err_ctor = lean_runtime_alloc_ctor(12, 1, 0); // KernelException.other
                lean_runtime_ctor_set(err_ctor, 0, msg);
                let except_err = lean_runtime_alloc_ctor(0, 1, 0); // Except.error
                lean_runtime_ctor_set(except_err, 0, err_ctor);
                except_err
            }
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_add_decl(
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

        let result = add_decl_dispatch(env, decl, 1);

        scope_max_heartbeat_pop(old_max);
        scope_cancel_tk_pop(old_tk);

        result
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        add_decl_dispatch(env, decl, 0)
    }
}
