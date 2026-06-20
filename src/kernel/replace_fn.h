/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "kernel/expr.h"

namespace lean {
extern "C" object * lean_replace_expr_with_callback(
    object * e,
    void * ctx,
    object * (* callback)(void * ctx, object * e, unsigned offset),
    uint8 use_cache);

namespace replace_detail {
inline object * callback(void * ctx, object * e, unsigned offset) {
    auto const & f = *static_cast<std::function<optional<expr>(expr const &, unsigned)> const *>(ctx);
    optional<expr> r = f(expr(e, true), offset);
    if (r)
        return mk_cnstr(1, *r).steal();
    return box(0);
}
}

/**
   \brief Apply <tt>f</tt> to the subexpressions of a given expression.

   f is invoked for each subexpression \c s of the input expression e.
   In a call <tt>f(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s. The replaces only visits children of \c e
   if f return none_expr.
*/
inline expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache = true) {
    void * ctx = const_cast<void *>(static_cast<void const *>(&f));
    return expr(lean_replace_expr_with_callback(e.raw(), ctx, replace_detail::callback, use_cache));
}

inline expr replace(expr const & e, std::function<optional<expr>(expr const &)> const & f, bool use_cache = true) {
    return replace(e, [&](expr const & e, unsigned) { return f(e); }, use_cache);
}
}
