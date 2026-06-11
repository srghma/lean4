// Port of kernel/for_each_fn.cpp
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: for_each_fn<> is a C++ template that pattern-matches on lean::expr.
// The two LEAN_EXPORT entry points (`lean_find_expr`, `lean_find_ext_expr`)
// delegate to C++ shims.  The traversal logic stays in C++.

mod kernel_for_each_fn_impl {
    use super::*;

    extern "C" {
        /// Calls for_each_fn<true> with predicate `p` over expression `e`.
        /// Returns `some(e')` (a ctor-1 object) if found, or `none` (box(0)).
        fn lean_cxx_find_expr(p: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;

        /// Like lean_cxx_find_expr but uses the three-valued FindStep predicate
        /// (found=0 / visit=1 / done=2) and for_each_fn<false> (no partial apps).
        fn lean_cxx_find_ext_expr(p: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
    }

    /// `findExpr? (p : Expr → Bool) (e : Expr) : Option Expr`
    ///
    /// Returns the first subexpression (including partial applications) for
    /// which `p` returns true, or `none`.
    #[no_mangle]
    pub unsafe extern "C" fn lean_find_expr(
        p: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_find_expr(p, e)
    }

    /// `findExtExpr? (p : Expr → FindStep) (e : Expr) : Option Expr`
    ///
    /// Like `lean_find_expr` but `p` returns a three-valued `FindStep`:
    ///   0 = found (stop, return this node)
    ///   1 = visit  (continue into children)
    ///   2 = done   (skip children)
    /// Does NOT visit partial applications.
    #[no_mangle]
    pub unsafe extern "C" fn lean_find_ext_expr(
        p: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_find_ext_expr(p, e)
    }
}
