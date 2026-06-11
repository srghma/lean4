// Port of kernel/expr_cache.cpp
// Copyright (c) 2015 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: expr_cache is a C++ class whose methods pattern-match on lean::expr
// and call is_bi_equal().  No LEAN_EXPORT symbols exist in this file — it is
// used only as an internal C++ helper by replace_fn, instantiate, etc.
// Therefore this Rust file is intentionally empty: the C++ translation unit
// (kernel/expr_cache.cpp) is kept as-is, and no symbols need to move here.
//
// This stub exists so the module inventory is complete and makes it obvious
// that expr_cache.cpp has been evaluated and consciously left in C++.

mod kernel_expr_cache_impl {
    // No LEAN_EXPORT symbols — nothing to port.
    // kernel/expr_cache.cpp stays in C++.
}
