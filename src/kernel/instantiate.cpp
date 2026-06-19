/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/declaration.h"
#include "kernel/instantiate.h"

namespace lean {
extern "C" object * lean_expr_instantiate_at(object * a, size_t s, size_t n, object * const * subst);
extern "C" object * lean_expr_instantiate_rev_ptr(object * a, size_t n, object * const * subst);
extern "C" object * lean_expr_cheap_beta_reduce(object * e);
extern "C" object * lean_expr_instantiate_lparams(object * e, object * ps, object * ls);
extern "C" object * lean_instantiate_type_lparams(object * info, object * ls);
extern "C" object * lean_instantiate_value_lparams(object * info, object * ls);

expr instantiate(expr const & a, unsigned s, unsigned n, expr const * subst) {
    if (s >= get_loose_bvar_range(a) || n == 0)
        return a;
    static_assert(sizeof(expr) == sizeof(object *), "expr buffer layout must match object pointer buffer");
    return expr(lean_expr_instantiate_at(a.raw(), s, n, reinterpret_cast<object * const *>(subst)));
}

expr instantiate(expr const & e, unsigned n, expr const * s) { return instantiate(e, 0, n, s); }
expr instantiate(expr const & e, std::initializer_list<expr> const & l) {  return instantiate(e, l.size(), l.begin()); }
expr instantiate(expr const & e, unsigned i, expr const & s) { return instantiate(e, i, 1, &s); }
expr instantiate(expr const & e, expr const & s) { return instantiate(e, 0, s); }


expr instantiate_rev(expr const & a, unsigned n, expr const * subst) {
    if (!has_loose_bvars(a))
        return a;
    static_assert(sizeof(expr) == sizeof(object *), "expr buffer layout must match object pointer buffer");
    return expr(lean_expr_instantiate_rev_ptr(a.raw(), n, reinterpret_cast<object * const *>(subst)));
}

expr cheap_beta_reduce(expr const & e) {
    return expr(lean_expr_cheap_beta_reduce(e.raw()));
}

expr instantiate_lparams(expr const & e, names const & lps, levels const & ls) {
    return expr(lean_expr_instantiate_lparams(e.raw(), lps.raw(), ls.raw()));
}

expr instantiate_type_lparams(constant_info const & info, levels const & ls) {
    return expr(lean_instantiate_type_lparams(info.raw(), ls.raw()));
}

expr instantiate_value_lparams(constant_info const & info, levels const & ls) {
    return expr(lean_instantiate_value_lparams(info.raw(), ls.raw()));
}

}
