// Port of kernel/environment.cpp
// Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.

mod kernel_environment_impl {
    use super::*;

    extern "C" {
        // C++ implementations in src/kernel/environment.cpp.
        // They properly convert Declaration → ConstantInfo via the kernel type-checker.
        // Aliased to avoid symbol conflicts: Rust #[no_mangle] lean_add_decl would
        // create a circular reference if it called the same symbol name.
        #[link_name = "lean_add_decl"]
        fn lean_add_decl_cxx(
            env: *mut LeanObject,
            max_heartbeat: usize,
            decl: *mut LeanObject,
            opt_cancel_tk: *mut LeanObject,
        ) -> *mut LeanObject;

        #[link_name = "lean_add_decl_without_checking"]
        fn lean_add_decl_without_checking_cxx(
            env: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    /// Called from lean_elab_add_decl (library_elab_environment.rs) with a kernel env.
    /// Delegates to C++ lean_add_decl which type-checks Declaration and returns
    /// Except KernelException KernelEnvironment.
    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_add_decl_impl(
        env: *mut LeanObject,
        max_heartbeat: usize,
        decl: *mut LeanObject,
        opt_cancel_tk: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_add_decl_cxx(env, max_heartbeat, decl, opt_cancel_tk)
    }

    /// Called from lean_elab_add_decl_without_checking (library_elab_environment.rs).
    /// Delegates to C++ lean_add_decl_without_checking which converts Declaration → ConstantInfo
    /// without type-checking. Returns Except KernelException KernelEnvironment.
    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_add_decl_without_checking_impl(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_add_decl_without_checking_cxx(env, decl)
    }

    // lean_add_decl and lean_add_decl_without_checking are intentionally NOT defined here.
    // The C++ implementations in src/kernel/environment.cpp provide these symbols.
    // Defining Rust versions with #[no_mangle] would override the C++ ones and cause
    // a circular reference (lean_add_decl_cxx → lean_add_decl → lean_add_decl_cxx).

    // initialize_environment / finalize_environment are no-ops in C++ (environment.cpp).
    // When libleancpp.a is linked (lean_use_libleancpp), those symbols are provided
    // by C++ directly; otherwise the no-op stubs in lib.rs satisfy the extern block.
}
