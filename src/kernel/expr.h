/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <limits>
#include "runtime/hash.h"
#include "runtime/buffer.h"
#include "util/name.h"
#include "util/kvmap.h"
#include "util/list_fn.h"
#include "kernel/level.h"
#include "kernel/expr_eq_fn.h"

namespace lean {
extern "C" {
    uint8_t lean_expr_eqv(object * a, object * b);
    uint8 lean_expr_binder_info(object * e);
    object * lean_lit_type(obj_arg e);
    uint64_t lean_expr_hash(obj_arg e);
    uint8 lean_expr_has_fvar(obj_arg e);
    uint8 lean_expr_has_expr_mvar(obj_arg e);
    uint8 lean_expr_has_level_mvar(obj_arg e);
    uint8 lean_expr_has_level_param(obj_arg e);
    unsigned lean_expr_loose_bvar_range(object * e);
    object * lean_expr_mk_lit(obj_arg l);
    object * lean_expr_mk_mdata(obj_arg m, obj_arg e);
    object * lean_expr_mk_proj(obj_arg s, obj_arg idx, obj_arg e);
    object * lean_expr_mk_bvar(obj_arg idx);
    object * lean_expr_mk_fvar(obj_arg n);
    object * lean_expr_mk_mvar(object * n);
    object * lean_expr_mk_const(obj_arg n, obj_arg ls);
    object * lean_expr_mk_app(obj_arg f, obj_arg a);
    object * lean_expr_mk_sort(obj_arg l);
    object * lean_expr_mk_lambda(obj_arg n, obj_arg t, obj_arg e, uint8 bi);
    object * lean_expr_mk_forall(obj_arg n, obj_arg t, obj_arg e, uint8 bi);
    object * lean_expr_mk_let(object * n, object * t, object * v, object * b, uint8 nondep);
    uint8 lean_expr_is_have(object * e);
    object * lean_expr_consume_type_annotations(obj_arg e);
    uint8 lean_expr_has_loose_bvar(object * e, object * i);
    object * lean_expr_lower_loose_bvars(object * e, object * s, object * d);
    object * lean_expr_lift_loose_bvars(object * e, object * s, object * d);
}

/* Binder annotations for Pi/lambda expressions */
enum class binder_info { Default, Implicit, StrictImplicit, InstImplicit, Rec };

inline binder_info mk_binder_info() { return binder_info::Default; }
inline binder_info mk_implicit_binder_info() { return binder_info::Implicit; }
inline bool is_explicit(binder_info bi) {
    return bi != binder_info::Implicit && bi != binder_info::StrictImplicit && bi != binder_info::InstImplicit;
}

/* Expression literal values */
enum class literal_kind { Nat, String };
class literal : public object_ref {
    explicit literal(b_obj_arg o, bool b):object_ref(o, b) {}
public:
    explicit literal(char const * v):object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::String), mk_string(v))) {}
    explicit literal(unsigned v):object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::Nat), mk_nat_obj(v))) {}
    explicit literal(mpz const & v):object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::Nat), mk_nat_obj(v))) {}
    explicit literal(nat const & v):object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::Nat), v)) {}
    literal():literal(0u) {}
    literal(literal const & other):object_ref(other) {}
    literal(literal && other) noexcept:object_ref(std::move(other)) {}
    literal & operator=(literal const & other) { object_ref::operator=(other); return *this; }
    literal & operator=(literal && other) noexcept { object_ref::operator=(std::move(other)); return *this; }

    static literal_kind kind(object * o) { return static_cast<literal_kind>(cnstr_tag(o)); }
    literal_kind kind() const { return kind(raw()); }
    string_ref const & get_string() const { lean_assert(kind() == literal_kind::String); return static_cast<string_ref const &>(cnstr_get_ref(*this, 0)); }
    nat const & get_nat() const { lean_assert(kind() == literal_kind::Nat); return static_cast<nat const &>(cnstr_get_ref(*this, 0)); }
    bool is_zero() const { return kind() == literal_kind::Nat && get_nat().is_zero(); }
    friend bool operator==(literal const & a, literal const & b);
    friend bool operator<(literal const & a, literal const & b);
};
inline bool operator==(literal const & a, literal const & b) {
    if (a.kind() != b.kind()) return false;
    switch (a.kind()) {
    case literal_kind::String: return a.get_string() == b.get_string();
    case literal_kind::Nat:    return a.get_nat() == b.get_nat();
    }
    lean_unreachable();
}
inline bool operator<(literal const & a, literal const & b) {
    if (a.kind() != b.kind()) return static_cast<unsigned>(a.kind()) < static_cast<unsigned>(b.kind());
    switch (a.kind()) {
    case literal_kind::String: return a.get_string() < b.get_string();
    case literal_kind::Nat:    return a.get_nat() < b.get_nat();
    }
    lean_unreachable();
}
inline bool operator!=(literal const & a, literal const & b) { return !(a == b); }

/* =======================================
   Expressions

inductive Expr
| bvar    : Nat → Expr                                -- bound variables
| fvar    : Name → Expr                               -- free variables
| mvar    : Name → Expr                               -- meta variables
| sort    : Level → Expr                              -- Sort
| const   : Name → List Level → Expr                  -- constants
| app     : Expr → Expr → Expr                        -- application
| lam     : Name → BinderInfo → Expr → Expr → Expr    -- lambda abstraction
| forallE : Name → BinderInfo → Expr → Expr → Expr    -- (dependent) arrow
| letE    : Name → Expr → Expr → Expr → Bool → Expr   -- let expressions
| lit     : Literal → Expr                            -- literals
| mdata   : MData → Expr → Expr                       -- metadata
| proj    : Name → Nat → Expr → Expr                  -- projection
*/
enum class expr_kind { BVar, FVar, MVar, Sort, Const, App, Lambda, Pi, Let, Lit, MData, Proj };
class expr : public object_ref {
    explicit expr(object_ref && o) noexcept:object_ref(o) {}

    friend expr mk_lit(literal const & lit);
    friend expr mk_mdata(kvmap const & d, expr const & e);
    friend expr mk_proj(name const & s, nat const & idx, expr const & e);
    friend expr mk_bvar(nat const & idx);
    friend expr mk_mvar(name const & n);
    friend expr mk_fvar(name const & n);
    friend expr mk_const(name const & n, levels const & ls);
    friend expr mk_app(expr const & f, expr const & a);
    friend expr mk_sort(level const & l);
    friend expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info bi);
    friend expr mk_pi(name const & n, expr const & t, expr const & e, binder_info bi);
    friend expr mk_let(name const & n, expr const & t, expr const & v, expr const & b);
public:
    expr();
    expr(expr const & other):object_ref(other) {}
    expr(expr && other) noexcept:object_ref(std::move(other)) {}
    explicit expr(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit expr(obj_arg o):object_ref(o) {}
    static expr_kind kind(object * o) { return static_cast<expr_kind>(cnstr_tag(o)); }
    expr_kind kind() const { return kind(raw()); }

    expr & operator=(expr const & other) { object_ref::operator=(other); return *this; }
    expr & operator=(expr && other) noexcept { object_ref::operator=(std::move(other)); return *this; }

    friend bool is_eqp(expr const & e1, expr const & e2) { return e1.raw() == e2.raw(); }
};
inline bool is_equal(expr const & a, expr const & b) {
    return lean_expr_eqv(a.raw(), b.raw()) != 0;
}

typedef list_ref<expr> exprs;
typedef pair<expr, expr> expr_pair;

inline optional<expr> none_expr() { return optional<expr>(); }
inline optional<expr> some_expr(expr const & e) { return optional<expr>(e); }
inline optional<expr> some_expr(expr && e) { return optional<expr>(std::forward<expr>(e)); }

inline uint64_t get_data(expr const & e) {
    return lean_ctor_get_uint64(e.raw(), lean_ctor_num_objs(e.raw())*sizeof(object*));
}
/* This is the implementation in Lean */
inline unsigned hash_core(expr const & e) { return lean_expr_hash(e.to_obj_arg()); }
inline unsigned hash(expr const & e) {
    unsigned r = static_cast<unsigned>(get_data(e));
    lean_assert(r == hash_core(e));
    return r;
}
/* This is the implementation in Lean */
inline bool has_expr_mvar_core(expr const & e) { return lean_expr_has_expr_mvar(e.to_obj_arg()); }
inline bool has_expr_mvar(expr const & e) {
    bool r = ((get_data(e) >> 41) & 1) == 1;
    lean_assert(r == has_expr_mvar_core(e)); // ensure the C++ implementation matches the Lean one.
    return r;
}
inline bool has_univ_mvar_core(expr const & e) { return lean_expr_has_level_mvar(e.to_obj_arg()); }
inline bool has_univ_mvar(expr const & e) {
    bool r = ((get_data(e) >> 42) & 1) == 1;
    lean_assert(r == has_univ_mvar_core(e)); // ensure the C++ implementation matches the Lean one.
    return r;
}
inline bool has_mvar(expr const & e) { return has_expr_mvar(e) || has_univ_mvar(e); }
/* This is the implementation in Lean */
inline bool has_fvar_core(expr const & e) { return lean_expr_has_fvar(e.to_obj_arg()); }
inline bool has_fvar(expr const & e) {
    bool r = ((get_data(e) >> 40) & 1) == 1;
    lean_assert(r == has_fvar_core(e)); // ensure the C++ implementation matches the Lean one.
    return r;
}
inline bool has_univ_param(expr const & e) { return lean_expr_has_level_param(e.to_obj_arg()); }
inline unsigned get_loose_bvar_range(expr const & e) { return lean_expr_loose_bvar_range(e.to_obj_arg()); }

struct expr_hash { unsigned operator()(expr const & e) const { return hash(e); } };
struct expr_pair_hash {
    unsigned operator()(expr_pair const & p) const { return hash(hash(p.first), hash(p.second)); }
};
struct expr_pair_eq {
    bool operator()(expr_pair const & p1, expr_pair const & p2) const { return p1.first == p2.first && p1.second == p2.second; }
};

// =======================================
// Testers
static expr_kind expr_kind_core(object * o) { return static_cast<expr_kind>(cnstr_tag(o)); }
inline bool is_bvar(expr const & e)        { return e.kind() == expr_kind::BVar; }
inline bool is_fvar_core(object * o)       { return expr_kind_core(o) == expr_kind::FVar; }
inline bool is_mvar_core(object * o)       { return expr_kind_core(o) == expr_kind::MVar; }
inline bool is_fvar(expr const & e)        { return e.kind() == expr_kind::FVar; }
inline bool is_const(expr const & e)       { return e.kind() == expr_kind::Const; }
inline bool is_mvar(expr const & e)        { return e.kind() == expr_kind::MVar; }
inline bool is_app(expr const & e)         { return e.kind() == expr_kind::App; }
inline bool is_lambda(expr const & e)      { return e.kind() == expr_kind::Lambda; }
inline bool is_pi(expr const & e)          { return e.kind() == expr_kind::Pi; }
inline bool is_let(expr const & e)         { return e.kind() == expr_kind::Let; }
inline bool is_sort(expr const & e)        { return e.kind() == expr_kind::Sort; }
inline bool is_lit(expr const & e)         { return e.kind() == expr_kind::Lit; }
inline bool is_mdata(expr const & e)       { return e.kind() == expr_kind::MData; }
inline bool is_proj(expr const & e)        { return e.kind() == expr_kind::Proj; }
inline bool is_binding(expr const & e)     { return is_lambda(e) || is_pi(e); }

bool is_arrow(expr const & t);
// =======================================

// =======================================
// Constructors
inline expr mk_lit(literal const & l) { return expr(lean_expr_mk_lit(l.to_obj_arg())); }
inline expr mk_mdata(kvmap const & m, expr const & e) { return expr(lean_expr_mk_mdata(m.to_obj_arg(), e.to_obj_arg())); }
inline expr mk_proj(name const & s, nat const & idx, expr const & e) { return expr(lean_expr_mk_proj(s.to_obj_arg(), idx.to_obj_arg(), e.to_obj_arg())); }
inline expr mk_proj(name const & s, unsigned idx, expr const & e) { return mk_proj(s, nat(idx), e); }
inline expr mk_bvar(nat const & idx) { return expr(lean_expr_mk_bvar(idx.to_obj_arg())); }
inline expr mk_bvar(unsigned idx) { return mk_bvar(nat(idx)); }
inline expr mk_fvar(name const & n) { return expr(lean_expr_mk_fvar(n.to_obj_arg())); }
inline expr mk_const(name const & n, levels const & ls) { return expr(lean_expr_mk_const(n.to_obj_arg(), ls.to_obj_arg())); }
inline expr mk_const(name const & n) { return mk_const(n, levels()); }
inline expr mk_mvar(name const & n) { return expr(lean_expr_mk_mvar(n.to_obj_arg())); }
inline expr mk_app(expr const & f, expr const & a) { return expr(lean_expr_mk_app(f.to_obj_arg(), a.to_obj_arg())); }
inline expr mk_app(expr const & f, unsigned num_args, expr const * args) {
    expr r = f;
    for (unsigned i = 0; i < num_args; i++)
        r = mk_app(r, args[i]);
    return r;
}
inline expr mk_app(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 2);
    return mk_app(mk_app(args[0], args[1]), num_args - 2, args+2);
}
inline expr mk_app(std::initializer_list<expr> const & l) { return mk_app(l.size(), l.begin()); }
inline expr mk_app(buffer<expr> const & args) { return mk_app(args.size(), args.data()); }
inline expr mk_app(expr const & f, buffer<expr> const & args) { return mk_app(f, args.size(), args.data()); }
inline expr mk_app(expr const & f, list<expr> const & args) {
    buffer<expr> _args;
    to_buffer(args, _args);
    return mk_app(f, _args);
}
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3) { return mk_app({e1, e2, e3}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({e1, e2, e3, e4}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({e1, e2, e3, e4, e5}); }
inline expr mk_rev_app(expr const & f, unsigned num_args, expr const * args) {
    expr r = f;
    unsigned i = num_args;
    while (i > 0) {
        --i;
        r = mk_app(r, args[i]);
    }
    return r;
}
inline expr mk_rev_app(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 2);
    return mk_rev_app(mk_app(args[num_args-1], args[num_args-2]), num_args-2, args);
}
inline expr mk_rev_app(buffer<expr> const & args) { return mk_rev_app(args.size(), args.data()); }
inline expr mk_rev_app(expr const & f, buffer<expr> const & args) { return mk_rev_app(f, args.size(), args.data()); }
inline expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info bi = mk_binder_info()) {
    return expr(lean_expr_mk_lambda(n.to_obj_arg(), t.to_obj_arg(), e.to_obj_arg(), static_cast<uint8>(bi)));
}
inline expr mk_pi(name const & n, expr const & t, expr const & e, binder_info bi = mk_binder_info()) {
    return expr(lean_expr_mk_forall(n.to_obj_arg(), t.to_obj_arg(), e.to_obj_arg(), static_cast<uint8>(bi)));
}
inline expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info bi = mk_binder_info()) {
    return k == expr_kind::Pi ? mk_pi(n, t, e, bi) : mk_lambda(n, t, e, bi);
}
expr mk_arrow(expr const & t, expr const & e);
inline expr mk_let(name const & n, expr const & t, expr const & v, expr const & b, bool nondep) {
    return expr(lean_expr_mk_let(n.to_obj_arg(), t.to_obj_arg(), v.to_obj_arg(), b.to_obj_arg(), nondep));
}
inline expr mk_let(name const & n, expr const & t, expr const & v, expr const & b) { return mk_let(n, t, v, b, false); };
inline expr mk_sort(level const & l) { return expr(lean_expr_mk_sort(l.to_obj_arg())); }
expr mk_Prop();
expr mk_Type();
// =======================================

// =======================================
// Accessors
inline literal const & lit_value(expr const & e)             { lean_assert(is_lit(e)); return static_cast<literal const &>(cnstr_get_ref(e, 0)); }
inline bool is_nat_lit(expr const & e)                       { return is_lit(e) && lit_value(e).kind() == literal_kind::Nat; }
inline bool is_string_lit(expr const & e)                    { return is_lit(e) && lit_value(e).kind() == literal_kind::String; }
inline expr lit_type(literal const & lit) { return expr(lean_lit_type(lit.to_obj_arg())); }
inline kvmap const &   mdata_data(expr const & e)            { lean_assert(is_mdata(e)); return static_cast<kvmap const &>(cnstr_get_ref(e, 0)); }
inline expr const &    mdata_expr(expr const & e)            { lean_assert(is_mdata(e)); return static_cast<expr const &>(cnstr_get_ref(e, 1)); }
inline name const &    proj_sname(expr const & e)            { lean_assert(is_proj(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline nat const &     proj_idx(expr const & e)              { lean_assert(is_proj(e)); return static_cast<nat const &>(cnstr_get_ref(e, 1)); }
inline expr const &    proj_expr(expr const & e)             { lean_assert(is_proj(e)); return static_cast<expr const &>(cnstr_get_ref(e, 2)); }
inline nat const &     bvar_idx(expr const & e)              { lean_assert(is_bvar(e)); return static_cast<nat const &>(cnstr_get_ref(e, 0)); }
inline bool            is_bvar(expr const & e, unsigned i)   { return is_bvar(e) && bvar_idx(e) == i; }
inline name const &    fvar_name_core(object * o)            { lean_assert(is_fvar_core(o)); return static_cast<name const &>(cnstr_get_ref(o, 0)); }
inline name const &    fvar_name(expr const & e)             { lean_assert(is_fvar(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline level const &   sort_level(expr const & e)            { lean_assert(is_sort(e)); return static_cast<level const &>(cnstr_get_ref(e, 0)); }
inline name const &    mvar_name_core(object * o)            { lean_assert(is_mvar_core(o)); return static_cast<name const &>(cnstr_get_ref(o, 0)); }
inline name const &    mvar_name(expr const & e)             { lean_assert(is_mvar(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline name const &    const_name(expr const & e)            { lean_assert(is_const(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline levels const &  const_levels(expr const & e)          { lean_assert(is_const(e)); return static_cast<levels const &>(cnstr_get_ref(e, 1)); }
inline bool is_const(expr const & e, name const & n)         { return is_const(e) && const_name(e) == n; }
inline expr const &    app_fn(expr const & e)                { lean_assert(is_app(e));   return static_cast<expr const &>(cnstr_get_ref(e, 0)); }
inline expr const &    app_arg(expr const & e)               { lean_assert(is_app(e));   return static_cast<expr const &>(cnstr_get_ref(e, 1)); }
inline name const &    binding_name(expr const & e)          { lean_assert(is_binding(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline expr const &    binding_domain(expr const & e)        { lean_assert(is_binding(e)); return static_cast<expr const &>(cnstr_get_ref(e, 1)); }
inline expr const &    binding_body(expr const & e)          { lean_assert(is_binding(e)); return static_cast<expr const &>(cnstr_get_ref(e, 2)); }
inline binder_info binding_info(expr const & e) { return static_cast<binder_info>(lean_expr_binder_info(e.to_obj_arg())); }
inline name const &    let_name(expr const & e)              { lean_assert(is_let(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline expr const &    let_type(expr const & e)              { lean_assert(is_let(e)); return static_cast<expr const &>(cnstr_get_ref(e, 1)); }
inline expr const &    let_value(expr const & e)             { lean_assert(is_let(e)); return static_cast<expr const &>(cnstr_get_ref(e, 2)); }
inline expr const &    let_body(expr const & e)              { lean_assert(is_let(e)); return static_cast<expr const &>(cnstr_get_ref(e, 3)); }
inline bool            let_nondep_core(expr const & e) {
    lean_assert(is_let(e));
    return lean_expr_is_have(e.to_obj_arg());
}
inline bool            let_nondep(expr const & e) {
    lean_assert(is_let(e));
    bool r = lean_ctor_get_uint8(e.raw(), 4*sizeof(object*) + sizeof(uint64_t));
    lean_assert(r == let_nondep_core(e)); // ensure the C++ implementation matches the Lean one.
    return r;
}
inline bool            is_shared(expr const & e)             { return !is_exclusive(e.raw()); }
//

// =======================================
// Update
inline expr update_app(expr const & e, expr const & new_fn, expr const & new_arg) {
    return !is_eqp(app_fn(e), new_fn) || !is_eqp(app_arg(e), new_arg) ? mk_app(new_fn, new_arg) : e;
}
inline expr update_binding(expr const & e, expr const & new_domain, expr const & new_body) {
    return !is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body)
        ? mk_binding(e.kind(), binding_name(e), new_domain, new_body, binding_info(e))
        : e;
}
inline expr update_binding(expr const & e, expr const & new_domain, expr const & new_body, binder_info bi) {
    return !is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body) || bi != binding_info(e)
        ? mk_binding(e.kind(), binding_name(e), new_domain, new_body, bi)
        : e;
}
inline expr update_sort(expr const & e, level const & new_level) {
    return !is_eqp(sort_level(e), new_level) ? mk_sort(new_level) : e;
}
inline expr update_const(expr const & e, levels const & new_levels) {
    return !is_eqp(const_levels(e), new_levels) ? mk_const(const_name(e), new_levels) : e;
}
inline expr update_let(expr const & e, expr const & new_type, expr const & new_value, expr const & new_body) {
    return !is_eqp(let_type(e), new_type) || !is_eqp(let_value(e), new_value) || !is_eqp(let_body(e), new_body)
        ? mk_let(let_name(e), new_type, new_value, new_body, let_nondep(e))
        : e;
}
inline expr update_mdata(expr const & e, expr const & new_e) {
    return !is_eqp(mdata_expr(e), new_e) ? mk_mdata(mdata_data(e), new_e) : e;
}
inline expr update_proj(expr const & e, expr const & new_e) {
    return !is_eqp(proj_expr(e), new_e) ? mk_proj(proj_sname(e), proj_idx(e), new_e) : e;
}
// =======================================


/** \brief Given \c e of the form <tt>(...(f a1) ... an)</tt>, store a1 ... an in args.
    If \c e is not an application, then nothing is stored in args.

    It returns the f. */
expr const & get_app_args(expr const & e, buffer<expr> & args);
/** \brief Similar to \c get_app_args, but arguments are stored in reverse order in \c args.
    If e is of the form <tt>(...(f a1) ... an)</tt>, then the procedure stores [an, ..., a1] in \c args. */
expr const & get_app_rev_args(expr const & e, buffer<expr> & args);
/** \brief Given \c e of the form <tt>(...(f a_1) ... a_n)</tt>, return \c f. If \c e is not an application, then return \c e. */
expr const & get_app_fn(expr const & e);
/** \brief Given \c e of the form <tt>(...(f a_1) ... a_n)</tt>, return \c n. If \c e is not an application, then return 0. */
unsigned get_app_num_args(expr const & e);

inline expr const & get_app_args(expr const & e, buffer<expr> & args) {
    unsigned sz = args.size();
    expr const * it = &e;
    while (is_app(*it)) {
        args.push_back(app_arg(*it));
        it = &(app_fn(*it));
    }
    std::reverse(args.begin() + sz, args.end());
    return *it;
}

inline expr const & get_app_rev_args(expr const & e, buffer<expr> & args) {
    expr const * it = &e;
    while (is_app(*it)) {
        args.push_back(app_arg(*it));
        it = &(app_fn(*it));
    }
    return *it;
}

inline expr const & get_app_fn(expr const & e) {
    expr const * it = &e;
    while (is_app(*it)) {
        it = &(app_fn(*it));
    }
    return *it;
}

inline unsigned get_app_num_args(expr const & e) {
    expr const * it = &e;
    unsigned n = 0;
    while (is_app(*it)) {
        it = &(app_fn(*it));
        n++;
    }
    return n;
}

inline expr consume_type_annotations(expr const & e) { return expr(lean_expr_consume_type_annotations(e.to_obj_arg())); }

// =======================================
// Loose bound variable management

/** \brief Return true iff the given expression has loose bound variables. */
inline bool has_loose_bvars(expr const & e) { return get_loose_bvar_range(e) > 0; }

/** \brief Return true iff \c e contains the loose bound variable <tt>(var i)</tt>. */
bool has_loose_bvar(expr const & e, unsigned i);

/** \brief Lower the loose bound variables >= s in \c e by \c d. That is, a loose bound variable <tt>(var i)</tt> s.t.
    <tt>i >= s</tt> is mapped into <tt>(var i-d)</tt>.

    \pre s >= d */
expr lower_loose_bvars(expr const & e, unsigned s, unsigned d);
expr lower_loose_bvars(expr const & e, unsigned d);

/** \brief Lift loose bound variables >= s in \c e by d. */
expr lift_loose_bvars(expr const & e, unsigned s, unsigned d);
expr lift_loose_bvars(expr const & e, unsigned d);
// =======================================

inline bool has_loose_bvar(expr const & e, unsigned i) {
    if (!has_loose_bvars(e))
        return false;
    return lean_expr_has_loose_bvar(e.to_obj_arg(), lean_box(i)) != 0;
}

inline expr lower_loose_bvars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_loose_bvar_range(e))
        return e;
    lean_assert(s >= d);
    return expr(lean_expr_lower_loose_bvars(e.to_obj_arg(), lean_box(s), lean_box(d)));
}

inline expr lower_loose_bvars(expr const & e, unsigned d) {
    return lower_loose_bvars(e, d, d);
}

inline expr lift_loose_bvars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_loose_bvar_range(e))
        return e;
    return expr(lean_expr_lift_loose_bvars(e.to_obj_arg(), lean_box(s), lean_box(d)));
}

inline expr lift_loose_bvars(expr const & e, unsigned d) {
    return lift_loose_bvars(e, 0, d);
}


// =======================================
// Implicit argument inference
/**
   \brief Given \c t of the form <tt>Pi (x_1 : A_1) ... (x_k : A_k), B</tt>,
   mark the first \c num_params as implicit if they are not already marked, and
   they occur in the remaining arguments. If \c strict is false, then we
   also mark it implicit if it occurs in \c B.
*/
expr infer_implicit(expr const & t, unsigned num_params, bool strict);
expr infer_implicit(expr const & t, bool strict);
// =======================================

namespace expr_detail {
inline name const & default_name() {
    static name * n = [] {
        name * r = new name("a");
        mark_persistent(r->raw());
        return r;
    }();
    return *n;
}

inline expr const & dummy_expr() {
    static expr * e = [] {
        expr * r = new expr(mk_const("__expr_for_default_constructor__"));
        mark_persistent(r->raw());
        return r;
    }();
    return *e;
}

inline expr const & prop_expr() {
    static expr * e = [] {
        expr * r = new expr(mk_sort(mk_level_zero()));
        mark_persistent(r->raw());
        return r;
    }();
    return *e;
}

inline expr const & type0_expr() {
    static expr * e = [] {
        expr * r = new expr(mk_sort(mk_level_one()));
        mark_persistent(r->raw());
        return r;
    }();
    return *e;
}

inline bool has_loose_bvars_in_domain(expr const & b, unsigned vidx, bool strict) {
    if (is_pi(b)) {
        if (has_loose_bvar(binding_domain(b), vidx)) {
            if (is_explicit(binding_info(b))) {
                return true;
            } else if (has_loose_bvars_in_domain(binding_body(b), 0, strict)) {
                return true;
            }
        }
        return has_loose_bvars_in_domain(binding_body(b), vidx+1, strict);
    } else if (!strict) {
        return has_loose_bvar(b, vidx);
    } else {
        return false;
    }
}
}

inline expr::expr():expr(expr_detail::dummy_expr()) {}

inline expr mk_arrow(expr const & t, expr const & e) {
    return mk_pi(expr_detail::default_name(), t, e, mk_binder_info());
}

inline expr mk_Prop() { return expr_detail::prop_expr(); }
inline expr mk_Type() { return expr_detail::type0_expr(); }

inline bool is_arrow(expr const & t) {
    if (!is_pi(t)) return false;
    if (has_loose_bvars(t)) {
        return !has_loose_bvar(binding_body(t), 0);
    } else {
        lean_assert(has_loose_bvars(binding_body(t)) == has_loose_bvar(binding_body(t), 0));
        return !has_loose_bvars(binding_body(t));
    }
}

inline expr infer_implicit(expr const & t, unsigned num_params, bool strict) {
    if (num_params == 0) {
        return t;
    } else if (is_pi(t)) {
        expr new_body = infer_implicit(binding_body(t), num_params-1, strict);
        if (!is_explicit(binding_info(t))) {
            return update_binding(t, binding_domain(t), new_body);
        } else if (expr_detail::has_loose_bvars_in_domain(new_body, 0, strict)) {
            return update_binding(t, binding_domain(t), new_body, mk_implicit_binder_info());
        } else {
            return update_binding(t, binding_domain(t), new_body);
        }
    } else {
        return t;
    }
}

inline expr infer_implicit(expr const & t, bool strict) {
    return infer_implicit(t, std::numeric_limits<unsigned>::max(), strict);
}

// =======================================
// Low level (raw) printing
std::ostream & operator<<(std::ostream & out, expr const & e);
// =======================================

void initialize_expr();
void finalize_expr();

/* ================= LEGACY ============== */
inline bool has_expr_metavar(expr const & e) { return has_expr_mvar(e); }
inline bool has_metavar(expr const & e) { return has_mvar(e); }
inline bool has_param_univ(expr const & e) { return has_univ_param(e); }
inline bool is_var(expr const & e) { return is_bvar(e); }
inline bool is_var(expr const & e, unsigned idx) { return is_bvar(e, idx); }
inline expr mk_constant(name const & n, levels const & ls) { return mk_const(n, ls); }
inline expr mk_constant(name const & n) { return mk_constant(n, levels()); }
inline bool is_constant(expr const & e) { return is_const(e); }
inline expr update_constant(expr const & e, levels const & new_levels) { return update_const(e, new_levels); }
inline bool is_constant(expr const & e, name const & n) { return is_const(e, n); }

/* Like `is_exclusive`, but also consider unique MT references as unshared, which ensures we get
 * similar performance on the cmdline and server (more precisely, for either option value of
 * `internal.cmdlineSnapshots`). Note that as `e` is merely *borrowed* (e.g. from the mctx in
 * the case of `instantiate_mvars` where the performance issue resolved here manifested, #5614),
 * it is in fact possible that another thread could simultaneously add a new direct reference to
 * `e`, so it is not definitely unshared in all cases if the below check is true.
 *
 * However, as we use this predicate merely as a conservative heuristic for detecting
 * expressions that are unshared *within the expression tree* at hand, the approximation is
 * still correct in this case. Furthermore, as we only use it for deciding when to cache
 * results, it ultimately does not affect the correctness of the overall procedure in any case.
 * This should however be kept in mind if we start using `is_likely_unshared` in other contexts.
 */
inline bool is_likely_unshared(expr const & e) {
    return e.raw()->m_rc == 1 || e.raw()->m_rc == -1;
}

}
