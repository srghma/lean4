/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "runtime/utf8.h"
#include "kernel/environment.h"
#include "kernel/inductive.h"

namespace lean {
/** \brief Return recursor name for the given inductive datatype name */
name mk_rec_name(name const & I) {
    return I + name("rec");
}

/** \brief Return true if the given declaration is a non-recursive structure (an inductive type with one constructor and no indices). */
bool is_non_rec_structure(environment const & env, name const & decl_name) {
    constant_info I = env.get(decl_name);
    if (!I.is_inductive()) return false;
    inductive_val I_val = I.to_inductive_val();
    return I_val.get_ncnstrs() == 1 && I_val.get_nindices() == 0 && !I_val.is_rec();
}

bool is_inductive(environment const & env, name const & n) {
    if (optional<constant_info> info = env.find(n))
        return info->is_inductive();
    return false;
}

bool is_constructor(environment const & env, name const & n) {
    if (optional<constant_info> info = env.find(n))
        return info->is_constructor();
    return false;
}

bool is_recursor(environment const & env, name const & n) {
    if (optional<constant_info> info = env.find(n))
        return info->is_recursor();
    return false;
}

optional<name> is_constructor_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn) && is_constructor(env, const_name(fn)))
        return optional<name>(const_name(fn));
    return optional<name>();
}

/** \brief If \c d_name is the name of a non-empty inductive datatype, then return the
    name of the first constructor. Return none otherwise. */
static optional<name> get_first_cnstr(environment const & env, name const & d_name) {
    constant_info info = env.get(d_name);
    if (!info.is_inductive()) return optional<name>();
    names const & cnstrs = info.to_inductive_val().get_cnstrs();
    if (empty(cnstrs)) return optional<name>();
    return optional<name>(head(cnstrs));
}

optional<expr> mk_nullary_cnstr(environment const & env, expr const & type, unsigned num_params) {
    buffer<expr> args;
    expr const & d = get_app_args(type, args);
    if (!is_constant(d)) return none_expr();
    auto cnstr_name = get_first_cnstr(env, const_name(d));
    if (!cnstr_name) return none_expr();
    args.shrink(num_params);
    return some(mk_app(mk_constant(*cnstr_name, const_levels(d)), args));
}

expr expand_eta_struct(environment const & env, expr const & e_type, expr const & e) {
    buffer<expr> args;
    expr const & I = get_app_args(e_type, args);
    if (!is_constant(I)) return e;
    auto ctor_name = get_first_cnstr(env, const_name(I));
    if (!ctor_name) return e;
    constructor_val ctor_val = env.get(*ctor_name).to_constructor_val();
    args.shrink(ctor_val.get_nparams());
    expr result = mk_app(mk_constant(*ctor_name, const_levels(I)), args);
    for (unsigned i = 0; i < ctor_val.get_nfields(); i++) {
        result = mk_app(result, mk_proj(const_name(I), nat(i), e));
    }
    return result;
}

optional<recursor_rule> get_rec_rule_for(recursor_val const & rec_val, expr const & major) {
    expr const & fn = get_app_fn(major);
    if (!is_constant(fn)) return optional<recursor_rule>();
    for (recursor_rule const & rule : rec_val.get_rules()) {
        if (rule.get_cnstr() == const_name(fn))
            return optional<recursor_rule>(rule);
    }
    return optional<recursor_rule>();
}

static expr * g_nat_zero       = nullptr;
static expr * g_nat_succ       = nullptr;
static expr * g_string_mk      = nullptr;
static expr * g_list_cons_char = nullptr;
static expr * g_list_nil_char  = nullptr;
static expr * g_char_of_nat    = nullptr;

expr nat_lit_to_constructor(expr const & e) {
    lean_assert(is_nat_lit(e));
    nat const & v = lit_value(e).get_nat();
    if (v == 0u)
        return *g_nat_zero;
    return mk_app(*g_nat_succ, mk_lit(literal(v - nat(1))));
}

expr string_lit_to_constructor(expr const & e) {
    lean_assert(is_string_lit(e));
    string_ref const & s = lit_value(e).get_string();
    std::vector<unsigned> cs;
    utf8_decode(s.to_std_string(), cs);
    expr r = *g_list_nil_char;
    unsigned i = cs.size();
    while (i > 0) {
        i--;
        r = mk_app(*g_list_cons_char, mk_app(*g_char_of_nat, mk_lit(literal(cs[i]))), r);
    }
    return mk_app(*g_string_mk, r);
}

void initialize_inductive() {
    g_nat_zero       = new expr(mk_constant(name{"Nat", "zero"}));
    mark_persistent(g_nat_zero->raw());
    g_nat_succ       = new expr(mk_constant(name{"Nat", "succ"}));
    mark_persistent(g_nat_succ->raw());
    g_string_mk      = new expr(mk_constant(name{"String", "ofList"}));
    mark_persistent(g_string_mk->raw());
    expr char_type   = mk_constant(name{"Char"});
    g_list_cons_char = new expr(mk_app(mk_constant(name{"List", "cons"}, {level()}), char_type));
    mark_persistent(g_list_cons_char->raw());
    g_list_nil_char  = new expr(mk_app(mk_constant(name{"List", "nil"}, {level()}), char_type));
    mark_persistent(g_list_nil_char->raw());
    g_char_of_nat    = new expr(mk_constant(name{"Char", "ofNat"}));
    mark_persistent(g_char_of_nat->raw());
}

void finalize_inductive() {
    delete g_nat_succ;
    delete g_nat_zero;
    delete g_string_mk;
    delete g_list_cons_char;
    delete g_list_nil_char;
    delete g_char_of_nat;
}
}
