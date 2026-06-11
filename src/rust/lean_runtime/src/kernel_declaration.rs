// Port of kernel/declaration.cpp
// Copyright (c) 2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: declaration.cpp constructs C++ value types (reducibility_hints,
// definition_val, constant_info, …) using C++ constructors and template
// helpers. Rust owns initialize_declaration / finalize_declaration and
// delegates to C++ shims.

mod kernel_declaration_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_initialize_declaration();
        fn lean_cxx_finalize_declaration();
    }

    #[export_name = "_ZN4lean22initialize_declarationEv"]
    pub unsafe extern "C" fn initialize_declaration() {
        lean_cxx_initialize_declaration();
    }

    #[export_name = "_ZN4lean20finalize_declarationEv"]
    pub unsafe extern "C" fn finalize_declaration() {
        lean_cxx_finalize_declaration();
    }
}
