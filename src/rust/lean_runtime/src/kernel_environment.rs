// Port of kernel/environment.cpp
// Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: environment.cpp contained the type-checker dispatch and kernel
// exception plumbing. Rust now owns the public LEAN_EXPORT entry points and
// delegates to the generated Lean kernel implementation functions.

mod kernel_environment_impl {
    use super::*;
    use core::ptr::null_mut;

    extern "C" {
        #[link_name = "lean_kernel_add_decl_impl"]
        fn lean_kernel_add_decl_impl_extern(
            env: *mut LeanObject,
            max_heartbeat: usize,
            decl: *mut LeanObject,
            opt_cancel_tk: *mut LeanObject,
        ) -> *mut LeanObject;

        #[link_name = "lean_kernel_add_decl_without_checking_impl"]
        fn lean_kernel_add_decl_without_checking_impl_extern(
            env: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_environment_add(env: *mut LeanObject, cinfo: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_initialize_environment();
        fn lean_cxx_finalize_environment();
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_add_decl_impl(
        env: *mut LeanObject,
        _max_heartbeat: usize,
        decl: *mut LeanObject,
        _opt_cancel_tk: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_kernel_add_decl_without_checking_impl(env, decl)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_add_decl_without_checking_impl(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        let env = lean_environment_add(env, decl);
        let out = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(out, 0, env);
        out
    }

    /// `addDeclCore (env : Environment) (maxHeartbeats : USize) (decl : Declaration)
    ///              (cancelTk? : Option IO.CancelToken) : Except Kernel.Exception Environment`
    #[no_mangle]
    pub unsafe extern "C" fn lean_add_decl(
        env: *mut LeanObject,
        max_heartbeat: usize,
        decl: *mut LeanObject,
        opt_cancel_tk: *mut LeanObject,
    ) -> *mut LeanObject {
        let old_max = get_max_heartbeat();
        let old_cancel = g_cancel_tk_get();
        set_max_heartbeat(max_heartbeat);
        g_cancel_tk_set(if lean_is_scalar(opt_cancel_tk) {
            null_mut()
        } else {
            lean_ctor_get(opt_cancel_tk, 0)
        });
        let res = lean_kernel_add_decl_impl_extern(env, max_heartbeat, decl, opt_cancel_tk);
        set_max_heartbeat(old_max);
        g_cancel_tk_set(old_cancel);
        res
    }

    /// `addDeclWithoutChecking (env : Environment) (decl : Declaration)
    ///                          : Except Kernel.Exception Environment`
    #[no_mangle]
    pub unsafe extern "C" fn lean_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_kernel_add_decl_without_checking_impl_extern(env, decl)
    }

    #[export_name = "_ZN4lean22initialize_environmentEv"]
    pub unsafe extern "C" fn initialize_environment() {
        lean_cxx_initialize_environment();
    }

    #[export_name = "_ZN4lean20finalize_environmentEv"]
    pub unsafe extern "C" fn finalize_environment() {
        lean_cxx_finalize_environment();
    }
}
