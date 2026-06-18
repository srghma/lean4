/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"

namespace lean {
expr abstract(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return !has_loose_bvars(e) && is_fvar(e); }));
    if (!has_fvar(e))
        return e;
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_fvar(m))
                return some_expr(m); // expression m does not contain free variables
            if (is_fvar(m)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (fvar_name(subst[i]) == fvar_name(m))
                        return some_expr(mk_bvar(offset + n - i - 1));
                }
                return none_expr();
            }
            return none_expr();
        });
}

}
