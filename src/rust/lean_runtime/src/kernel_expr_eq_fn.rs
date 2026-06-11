// Port of kernel/expr_eq_fn.cpp
// Copyright (c) 2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: expr_eq_fn<> is a C++ template that pattern-matches on lean::expr
// sum types.  The comparison logic must stay in C++ because Rust cannot name
// lean::expr, lean::expr_kind, lean::level, etc.  This file owns the two
// LEAN_EXPORT entry points and delegates to C++ shims.

mod kernel_expr_eq_fn_impl {
    use super::*;

    extern "C" {
        /// Calls expr_eq_fn<false>()(a, b) — ignores binder info.
        fn lean_cxx_expr_eqv(a: *mut LeanObject, b: *mut LeanObject) -> u8;
        /// Calls expr_eq_fn<true>()(a, b) — includes binder info.
        fn lean_cxx_expr_equal(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    }

    /// `lean_expr_eqv` — structural equality ignoring binder info.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_eqv(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        lean_cxx_expr_eqv(a, b)
    }

    /// `lean_expr_equal` — structural equality including binder info.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_equal(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        lean_cxx_expr_equal(a, b)
    }
}
