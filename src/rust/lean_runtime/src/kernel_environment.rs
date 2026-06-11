// Port of kernel/environment.cpp
// Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: environment.cpp contains the type-checker dispatch, kernel exception
// throwing, and scoped_diagnostics RAII — all deeply C++. Rust owns the two
// LEAN_EXPORT entry points (lean_add_decl, lean_add_decl_without_checking)
// plus the trivial module init pair, delegating to C++ shims.

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
        fn lean_cxx_initialize_environment();
        fn lean_cxx_finalize_environment();
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
        lean_cxx_add_decl(env, max_heartbeat, decl, opt_cancel_tk)
    }

    /// `addDeclWithoutChecking (env : Environment) (decl : Declaration)
    ///                          : Except Kernel.Exception Environment`
    #[no_mangle]
    pub unsafe extern "C" fn lean_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_add_decl_without_checking(env, decl)
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
