// Port of kernel/type_checker.cpp
// Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: type_checker.cpp is the Lean kernel type checker — ~800 lines of C++
// templates and virtual dispatch over lean::expr. Rust owns initialize_type_checker
// / finalize_type_checker and delegates to C++ shims.

mod kernel_type_checker_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_initialize_type_checker();
        fn lean_cxx_finalize_type_checker();
    }

    #[export_name = "_ZN4lean23initialize_type_checkerEv"]
    pub unsafe extern "C" fn initialize_type_checker() {
        lean_cxx_initialize_type_checker();
    }

    #[export_name = "_ZN4lean21finalize_type_checkerEv"]
    pub unsafe extern "C" fn finalize_type_checker() {
        lean_cxx_finalize_type_checker();
    }
}
