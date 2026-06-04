// Port of kernel/instantiate.cpp
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: All instantiation logic operates on lean::expr / lean::nat / lean::names
// C++ value types. Rust owns the six LEAN_EXPORT entry points and delegates to
// C++ shims. The internal helpers (instantiate, instantiate_rev, apply_beta,
// instantiate_lparams, etc.) stay in C++.

mod kernel_instantiate_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_expr_instantiate1(
            a: *mut LeanObject,
            e: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_expr_instantiate(
            a: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_expr_instantiate_range(
            a: *mut LeanObject,
            begin: *mut LeanObject,
            end: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_expr_instantiate_rev(
            a: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_expr_instantiate_rev_range(
            a: *mut LeanObject,
            begin: *mut LeanObject,
            end: *mut LeanObject,
            subst: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    /// `Expr.instantiate1 (a e : Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate1(
        a: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate1(a, e)
    }

    /// `Expr.instantiate (a : Expr) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate(a, subst)
    }

    /// `Expr.instantiateRange (a : Expr) (begin end : Nat) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate_range(a, begin, end, subst)
    }

    /// `Expr.instantiateRev (a : Expr) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate_rev(a, subst)
    }

    /// `Expr.instantiateRevRange (a : Expr) (begin end : Nat) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_expr_instantiate_rev_range(a, begin, end, subst)
    }

}
