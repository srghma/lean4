// Port of kernel/abstract.cpp
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: abstract() uses replace() on lean::expr with C++ lambdas. Rust cannot
// name those types. The two LEAN_EXPORT entry points delegate to C++ shims.

mod kernel_abstract_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_expr_abstract_range(
            e: *mut LeanObject,
            n: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_expr_abstract(
            e: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    /// `Expr.abstractRange (e : Expr) (n : Nat) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_abstract_range(
        e: *mut LeanObject,
        n: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_abstract_range(e, n, subst)
    }

    /// `Expr.abstract (e : Expr) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_abstract(
        e: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_abstract(e, subst)
    }
}
