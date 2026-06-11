// Port of kernel/replace_fn.cpp
// Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: replace_fn / replace_rec_fn are C++ templates that pattern-match on
// lean::expr sum types (App, Lambda, Pi, Let, MData, Proj, …).  The traversal
// logic must stay in C++ because Rust cannot name those types.
//
// This file owns the single LEAN_EXPORT entry point `lean_replace_expr` and
// delegates to a C++ shim.

mod kernel_replace_fn_impl {
    use super::*;

    extern "C" {
        /// Calls replace_fn(f)(TO_REF(expr, e)) and returns the result.
        /// `f` is a borrowed Lean function object (b_obj_arg — not consumed).
        /// `e` is a borrowed lean::expr (b_obj_arg — not consumed).
        /// Returns an owned lean::expr (obj_res — callee must dec when done).
        fn lean_cxx_replace_expr(f: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
    }

    /// `lean_replace_expr (f : Expr → Option Expr) (e : Expr) : Expr`
    ///
    /// Applies `f` to every subexpression of `e`; if `f` returns `some e'`,
    /// the subexpression is replaced and its children are not visited.
    #[no_mangle]
    pub unsafe extern "C" fn lean_replace_expr(
        f: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_replace_expr(f, e)
    }
}
