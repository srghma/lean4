// Port of kernel/quot.cpp
// Copyright (c) 2018 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: quot.cpp builds the Quot type axioms by constructing lean::expr / lean::level
// objects using C++ constructors. Rust owns initialize_quot / finalize_quot and
// delegates to C++ shims.

mod kernel_quot_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_initialize_quot();
        fn lean_cxx_finalize_quot();
    }

    #[export_name = "_ZN4lean15initialize_quotEv"]
    pub unsafe extern "C" fn initialize_quot() {
        lean_cxx_initialize_quot();
    }

    #[export_name = "_ZN4lean13finalize_quotEv"]
    pub unsafe extern "C" fn finalize_quot() {
        lean_cxx_finalize_quot();
    }
}
