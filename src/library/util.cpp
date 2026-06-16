/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include <lean/version.h>
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/util.h"
#include "library/constants.h"
#include "githash.h" // NOLINT

namespace lean {
optional<expr> unfold_term(environment const & env, expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->has_value())
        return none_expr();
    expr d = instantiate_value_lparams(*decl, const_levels(f));
    buffer<expr> args;
    get_app_rev_args(e, args);
    return some_expr(apply_beta(d, args.size(), args.data()));
}

optional<expr> unfold_app(environment const & env, expr const & e) {
    if (!is_app(e))
        return none_expr();
    return unfold_term(env, e);
}

static expr * g_nat         = nullptr;
static expr * g_nat_zero    = nullptr;
static expr * g_nat_one     = nullptr;
static expr * g_nat_bit0_fn = nullptr;
static expr * g_nat_bit1_fn = nullptr;

static void initialize_nat() {
    g_nat            = new expr(mk_constant(get_nat_name()));
    mark_persistent(g_nat->raw());
    g_nat_zero       = new expr(mk_app(mk_constant(get_has_zero_zero_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_zero_name())}));
    mark_persistent(g_nat_zero->raw());
    g_nat_one        = new expr(mk_app(mk_constant(get_has_one_one_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_one_name())}));
    mark_persistent(g_nat_one->raw());
    g_nat_bit0_fn    = new expr(mk_app(mk_constant(get_bit0_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_add_name())}));
    mark_persistent(g_nat_bit0_fn->raw());
    g_nat_bit1_fn    = new expr(mk_app(mk_constant(get_bit1_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_one_name()), mk_constant(get_nat_has_add_name())}));
    mark_persistent(g_nat_bit1_fn->raw());
}

static void finalize_nat() {
    delete g_nat;
    delete g_nat_zero;
    delete g_nat_one;
    delete g_nat_bit0_fn;
    delete g_nat_bit1_fn;
}

expr mk_nat_zero() { return *g_nat_zero; }
expr mk_nat_one() { return *g_nat_one; }
expr mk_nat_bit0(expr const & e) { return mk_app(*g_nat_bit0_fn, e); }
expr mk_nat_bit1(expr const & e) { return mk_app(*g_nat_bit1_fn, e); }

static expr * g_bool = nullptr;
static expr * g_bool_true = nullptr;
static expr * g_bool_false = nullptr;

LEAN_EXPORT void initialize_bool() {
    g_bool = new expr(mk_constant(get_bool_name()));
    mark_persistent(g_bool->raw());
    g_bool_false = new expr(mk_constant(get_bool_false_name()));
    mark_persistent(g_bool_false->raw());
    g_bool_true = new expr(mk_constant(get_bool_true_name()));
    mark_persistent(g_bool_true->raw());
}

LEAN_EXPORT void finalize_bool() {
    delete g_bool;
    delete g_bool_false;
    delete g_bool_true;
}

expr mk_bool_true() { return *g_bool_true; }
expr mk_bool_false() { return *g_bool_false; }

static std::string * g_short_version_string = nullptr;
std::string const & get_short_version_string() { return *g_short_version_string; }

static name * g_util_fresh = nullptr;

LEAN_EXPORT void initialize_library_util() {
    initialize_nat();
    initialize_bool();
    g_short_version_string = new std::string(LEAN_VERSION_STRING);
    g_util_fresh = new name("_util_fresh");
    mark_persistent(g_util_fresh->raw());
    register_name_generator_prefix(*g_util_fresh);
}

LEAN_EXPORT void finalize_library_util() {
    delete g_util_fresh;
    finalize_bool();
    finalize_nat();
}
}
