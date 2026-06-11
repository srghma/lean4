// Port of kernel/local_ctx.cpp
// Copyright (c) 2018 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: local_ctx and local_decl are C++ classes that wrap Lean objects.
// initialize_local_ctx / finalize_local_ctx allocate persistent C++ globals
// (g_dummy_type, g_dummy_decl) that require C++ constructors. This file owns
// those two module-init exports and delegates to C++ shims.

mod kernel_local_ctx_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_initialize_local_ctx();
        fn lean_cxx_finalize_local_ctx();
    }

    #[export_name = "_ZN4lean20initialize_local_ctxEv"]
    pub unsafe extern "C" fn initialize_local_ctx() {
        lean_cxx_initialize_local_ctx();
    }

    #[export_name = "_ZN4lean18finalize_local_ctxEv"]
    pub unsafe extern "C" fn finalize_local_ctx() {
        lean_cxx_finalize_local_ctx();
    }
}
