/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief Return true iff \c t is of the form <tt>((f s1) s2)</tt> */
inline bool is_bin_app(expr const & t, expr const & f) {
    return is_app(t) && is_app(app_fn(t)) && app_fn(app_fn(t)) == f;
}
/** \brief Return true iff \c t is of the form <tt>((f s1) s2)</tt>, if the result is true, then store a1 -> lhs, a2 -> rhs */
inline bool is_bin_app(expr const & t, expr const & f, expr & lhs, expr & rhs) {
    if (!is_bin_app(t, f))
        return false;
    lhs = app_arg(app_fn(t));
    rhs = app_arg(t);
    return true;
}

/** \brief Return unit if <tt>num_args == 0</tt>, args[0] if <tt>num_args == 1</tt>, and
    <tt>(op args[0] (op args[1] (op ... )))</tt> */
inline expr mk_bin_rop(expr const & op, expr const & unit, unsigned num_args, expr const * args) {
    if (num_args == 0)
        return unit;
    expr r = args[num_args - 1];
    unsigned i = num_args - 1;
    while (i > 0) {
        --i;
        r = mk_app(op, args[i], r);
    }
    return r;
}
inline expr mk_bin_rop(expr const & op, expr const & unit, std::initializer_list<expr> const & l) {
    return mk_bin_rop(op, unit, l.size(), l.begin());
}

/** \brief Version of foldr that only uses unit when num_args == 0 */
template<typename MkBin, typename MkUnit>
expr foldr_compact(MkBin && mkb, MkUnit && mku, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return mku();
    } else {
        expr r = args[num_args - 1];
        unsigned i = num_args - 1;
        while (i > 0) {
            --i;
            r = mkb(args[i], r);
        }
        return r;
    }
}

/** \brief Version of foldr that only uses unit when num_args == 0 */
template<typename MkBin, typename MkUnit>
expr foldr(MkBin && mkb, MkUnit && mku, unsigned num_args, expr const * args) {
    expr r = mku();
    unsigned i = num_args;
    while (i > 0) {
        --i;
        r = mkb(args[i], r);
    }
    return r;
}

/** \brief Return unit if <tt>num_args == 0</tt>, args[0] if <tt>num_args == 1</tt>, and
    <tt>(op ... (op (op args[0] args[1]) args[2]) ...)</tt> */
inline expr mk_bin_lop(expr const & op, expr const & unit, unsigned num_args, expr const * args) {
    if (num_args == 0)
        return unit;
    expr r = args[0];
    for (unsigned i = 1; i < num_args; i++)
        r = mk_app(op, r, args[i]);
    return r;
}
inline expr mk_bin_lop(expr const & op, expr const & unit, std::initializer_list<expr> const & l) {
    return mk_bin_lop(op, unit, l.size(), l.begin());
}
}
