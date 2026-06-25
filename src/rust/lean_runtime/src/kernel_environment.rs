/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
use crate::*;

#[cfg(feature = "export-runtime-ffi")]
pub(crate) mod kernel_environment_impl {
    use super::*;

    extern "C" {
        // Unified Rust dispatch (kernel_type_checker.rs): axiom/def/theorem/opaque are checked
        // and added in Rust; quot/mutual/inductive still delegate to the C++ bridges internally.
        fn lean_rust_add_decl(
            env: *mut LeanObject,
            decl: *mut LeanObject,
            check: u8,
        ) -> *mut LeanObject;
    }

    #[inline(always)]
    unsafe fn add_decl_dispatch(
        env: *mut LeanObject,
        decl: *mut LeanObject,
        check: u8,
    ) -> *mut LeanObject {
        lean_rust_add_decl(env, decl, check)
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
