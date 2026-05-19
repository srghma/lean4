/*
Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"

namespace lean {
extern "C" object * lean_kernel_env_is_def_eq_impl(object * env, object * lctx, object * unsafe_decl,
    object * a, object * b);
extern "C" object * lean_kernel_env_whnf_impl(object * env, object * lctx, object * unsafe_decl,
    object * a);
extern "C" object * lean_kernel_env_check_impl(object * env, object * lctx, object * unsafe_decl,
    object * lparams, object * a);

static object * mk_safety_flag(definition_safety ds) {
    return box(ds == definition_safety::unsafe ? 1 : 0);
}

static bool get_bool_or_throw_kernel_exception(obj_arg r) {
    if (cnstr_tag(r) == 1) {
        bool b = unbox(cnstr_get(r, 0)) != 0;
        dec(r);
        return b;
    }
    object * ex = cnstr_get(r, 0);
    inc(ex);
    dec(r);
    throw_kernel_exception_object(ex);
}

static expr ensure_sort_result(environment const & env, local_ctx const & lctx, expr const & s, expr const & type) {
    if (is_sort(type))
        return type;
    throw type_expected_exception(env, lctx, s);
}

static expr ensure_pi_result(environment const & env, local_ctx const & lctx, expr const & s, expr const & type) {
    if (is_pi(type))
        return type;
    throw function_expected_exception(env, lctx, s);
}

type_checker::state::state(environment const & env):
    m_env(env), m_ngen(name("_kernel_fresh")) {}

expr type_checker::infer_type(expr const & e) {
    return get_or_throw_kernel_exception<expr>(
        lean_kernel_env_check_impl(env().to_obj_arg(), m_lctx.to_obj_arg(), mk_safety_flag(m_definition_safety),
            box(0), e.to_obj_arg()));
}

expr type_checker::check(expr const & e, names const & lps) {
    return get_or_throw_kernel_exception<expr>(
        lean_kernel_env_check_impl(env().to_obj_arg(), m_lctx.to_obj_arg(), mk_safety_flag(m_definition_safety),
            lps.to_obj_arg(), e.to_obj_arg()));
}

expr type_checker::check_ignore_undefined_universes(expr const & e) {
    return infer_type(e);
}

expr type_checker::ensure_sort(expr const & e, expr const & s) {
    return ensure_sort_result(env(), m_lctx, s, whnf(check_ignore_undefined_universes(e)));
}

expr type_checker::ensure_pi(expr const & e, expr const & s) {
    return ensure_pi_result(env(), m_lctx, s, whnf(check_ignore_undefined_universes(e)));
}

bool type_checker::is_prop(expr const & e) {
    return whnf(check_ignore_undefined_universes(e)) == mk_Prop();
}

expr type_checker::whnf(expr const & e) {
    return get_or_throw_kernel_exception<expr>(
        lean_kernel_env_whnf_impl(env().to_obj_arg(), m_lctx.to_obj_arg(), mk_safety_flag(m_definition_safety),
            e.to_obj_arg()));
}

bool type_checker::is_def_eq(expr const & t, expr const & s) {
    return get_bool_or_throw_kernel_exception(
        lean_kernel_env_is_def_eq_impl(env().to_obj_arg(), m_lctx.to_obj_arg(),
            mk_safety_flag(m_definition_safety), t.to_obj_arg(), s.to_obj_arg()));
}

expr type_checker::eta_expand(expr const & e) {
    return e;
}

type_checker::type_checker(environment const & env, local_ctx const & lctx, diagnostics * diag, definition_safety ds):
    m_st_owner(true), m_st(new state(env)), m_diag(diag), m_lctx(lctx), m_definition_safety(ds), m_lparams(nullptr) {}

type_checker::type_checker(state & st, local_ctx const & lctx, definition_safety ds):
    m_st_owner(false), m_st(&st), m_diag(nullptr), m_lctx(lctx), m_definition_safety(ds), m_lparams(nullptr) {}

type_checker::type_checker(type_checker && src) noexcept:
    m_st_owner(src.m_st_owner), m_st(src.m_st), m_diag(src.m_diag), m_lctx(std::move(src.m_lctx)),
    m_definition_safety(src.m_definition_safety), m_eager_reduce(src.m_eager_reduce), m_lparams(src.m_lparams) {
    src.m_st_owner = false;
    src.m_st       = nullptr;
}

type_checker::~type_checker() {
    if (m_st_owner)
        delete m_st;
}

void initialize_type_checker() {
}

void finalize_type_checker() {
}
}
