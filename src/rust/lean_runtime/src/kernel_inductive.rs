// Port of kernel/inductive.cpp
// Copyright (c) 2018 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: inductive.cpp contains add_inductive_fn and elim_nested_inductive_fn —
// large C++ classes that build inductive type declarations. Rust owns
// initialize_inductive / finalize_inductive and delegates to C++ shims.

mod kernel_inductive_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_initialize_inductive();
        fn lean_cxx_finalize_inductive();
    }

    #[export_name = "_ZN4lean20initialize_inductiveEv"]
    pub unsafe extern "C" fn initialize_inductive() {
        lean_cxx_initialize_inductive();
    }

    #[export_name = "_ZN4lean18finalize_inductiveEv"]
    pub unsafe extern "C" fn finalize_inductive() {
        lean_cxx_finalize_inductive();
    }
}
