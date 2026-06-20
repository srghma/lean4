/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "kernel/expr.h"

namespace lean {
extern "C" object * lean_expr_abstract_ptr(object * e, size_t n, object * const * subst);

/** \brief Replace the free variables s[0], ..., s[n-1] in e with bound variables bvar(n-1), ..., bvar(0). */
inline expr abstract(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return !has_loose_bvars(e) && is_fvar(e); }));
    if (!has_fvar(e))
        return e;
    static_assert(sizeof(expr) == sizeof(object *), "expr buffer layout must match object pointer buffer");
    return expr(lean_expr_abstract_ptr(e.raw(), n, reinterpret_cast<object * const *>(subst)));
}

inline expr abstract(expr const & e, expr const & s) { return abstract(e, 1, &s); }

}
