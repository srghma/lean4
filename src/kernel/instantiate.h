/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/declaration.h"

namespace lean {
extern "C" object * lean_expr_instantiate_at(object * a, size_t s, size_t n, object * const * subst);
extern "C" object * lean_expr_instantiate_rev_ptr(object * a, size_t n, object * const * subst);
extern "C" object * lean_expr_cheap_beta_reduce(object * e);
extern "C" object * lean_expr_instantiate_lparams(object * e, object * ps, object * ls);
extern "C" object * lean_instantiate_type_lparams(object * info, object * ls);
extern "C" object * lean_instantiate_value_lparams(object * info, object * ls);

/** \brief Replace the loose bound variables with indices 0, ..., n-1 with s[0], ..., s[n-1] in e. */
inline expr instantiate(expr const & e, unsigned start, unsigned n, expr const * subst) {
    if (start >= get_loose_bvar_range(e) || n == 0)
        return e;
    static_assert(sizeof(expr) == sizeof(object *), "expr buffer layout must match object pointer buffer");
    return expr(lean_expr_instantiate_at(e.raw(), start, n, reinterpret_cast<object * const *>(subst)));
}

inline expr instantiate(expr const & e, unsigned n, expr const * subst) {
    return instantiate(e, 0, n, subst);
}

inline expr instantiate(expr const & e, std::initializer_list<expr> const & l) {
    return instantiate(e, l.size(), l.begin());
}

/** \brief Replace loose bound variable \c i with \c s in \c e. */
inline expr instantiate(expr const & e, unsigned i, expr const & s) {
    return instantiate(e, i, 1, &s);
}

/** \brief Replace loose bound variable \c 0 with \c s in \c e. */
inline expr instantiate(expr const & e, expr const & s) {
    return instantiate(e, 0, s);
}

/** \brief Replace the free variables with indices 0, ..., n-1 with s[n-1], ..., s[0] in e. */
inline expr instantiate_rev(expr const & e, unsigned n, expr const * subst) {
    if (!has_loose_bvars(e))
        return e;
    static_assert(sizeof(expr) == sizeof(object *), "expr buffer layout must match object pointer buffer");
    return expr(lean_expr_instantiate_rev_ptr(e.raw(), n, reinterpret_cast<object * const *>(subst)));
}

inline expr instantiate_rev(expr const & e, buffer<expr> const & s) {
    return instantiate_rev(e, s.size(), s.data());
}

/* If `e` is of the form `(fun x, t) a` return `head_beta_const_fn(t)` if `t` does not depend on `x`,
   and `e` otherwise. We also reduce `(fun x_1 ... x_n, x_i) a_1 ... a_n` into `a_[n-i-1]` */
inline expr cheap_beta_reduce(expr const & e) {
    return expr(lean_expr_cheap_beta_reduce(e.raw()));
}

/** \brief Instantiate the universe level parameters \c ps occurring in \c e with the levels \c ls.
    \pre length(ps) == length(ls) */
inline expr instantiate_lparams(expr const & e, names const & ps, levels const & ls) {
    return expr(lean_expr_instantiate_lparams(e.raw(), ps.raw(), ls.raw()));
}

/** \brief Instantiate the universe level parameters of the type of the given constant.
    \pre d.get_num_lparams() == length(ls) */
inline expr instantiate_type_lparams(constant_info const & info, levels const & ls) {
    return expr(lean_instantiate_type_lparams(info.raw(), ls.raw()));
}

/** \brief Instantiate the universe level parameters of the value of the given constant.
    \pre d.get_num_lparams() == length(ls) */
inline expr instantiate_value_lparams(constant_info const & info, levels const & ls) {
    return expr(lean_instantiate_value_lparams(info.raw(), ls.raw()));
}
}
