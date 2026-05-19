/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <limits>
#include "runtime/sstream.h"
#include "runtime/thread.h"
#include "util/map_foreach.h"
#include "util/io.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"

namespace lean {
extern "C" obj_res initialize_Lean_Kernel(uint8_t builtin);

static void ensure_lean_kernel_initialized() {
    static bool initialized = false;
    if (initialized)
        return;
    object * res = initialize_Lean_Kernel(/*builtin*/ false);
    lean_assert(lean_io_result_is_ok(res));
    dec_ref(res);
    initialized = true;
}

extern "C" object* lean_environment_add(object*, object*);
extern "C" object* lean_environment_find(object*, object*);
extern "C" object* lean_environment_mark_quot_init(object*);
extern "C" uint8 lean_environment_quot_init(object*);
extern "C" object* lean_kernel_record_unfold (object*, object*);
extern "C" object* lean_kernel_get_diag(object*);
extern "C" object* lean_kernel_set_diag(object*, object*);
extern "C" uint8* lean_kernel_diag_is_enabled(object*);
extern "C" object * lean_kernel_add_decl_impl(object * env, object * max_heartbeat, object * decl,
    object * opt_cancel_tk);
extern "C" object * lean_kernel_add_decl_without_checking_impl(object * env, object * decl);

void diagnostics::record_unfold(name const & decl_name) {
    m_obj = lean_kernel_record_unfold(m_obj, decl_name.to_obj_arg());
}

scoped_diagnostics::scoped_diagnostics(environment const & env, bool collect) {
    if (collect) {
        diagnostics d(env.get_diag());
        if (lean_kernel_diag_is_enabled(d.to_obj_arg())) {
            m_diag = new diagnostics(d);
        } else
            m_diag = nullptr;
    } else {
        m_diag = nullptr;
    }
}

scoped_diagnostics::~scoped_diagnostics() {
    if (m_diag)
        delete m_diag;
}

environment scoped_diagnostics::update(environment const & env) const {
    if (m_diag)
        return env.set_diag(*m_diag);
    else
        return env;
}

diagnostics environment::get_diag() const {
    return diagnostics(lean_kernel_get_diag(to_obj_arg()));
}

environment environment::set_diag(diagnostics const & diag) const {
    return environment(lean_kernel_set_diag(to_obj_arg(), diag.to_obj_arg()));
}

bool environment::is_quot_initialized() const {
    return lean_environment_quot_init(to_obj_arg()) != 0;
}

void environment::mark_quot_initialized() {
    m_obj = lean_environment_mark_quot_init(m_obj);
}

optional<constant_info> environment::find(name const & n) const {
    return to_optional<constant_info>(lean_environment_find(to_obj_arg(), n.to_obj_arg()));
}

constant_info environment::get(name const & n) const {
    object * o = lean_environment_find(to_obj_arg(), n.to_obj_arg());
    if (is_scalar(o))
        throw unknown_constant_exception(*this, n);
    constant_info r(cnstr_get(o, 0), true);
    dec(o);
    return r;
}

static void check_no_metavar(environment const & env, name const & n, expr const & e) {
    if (has_metavar(e))
        throw declaration_has_metavars_exception(env, n, e);
}

static void check_no_fvar(environment const & env, name const & n, expr const & e) {
    if (has_fvar(e))
        throw declaration_has_free_vars_exception(env, n, e);
}

void check_no_metavar_no_fvar(environment const & env, name const & n, expr const & e) {
    check_no_metavar(env, n, e);
    check_no_fvar(env, n, e);
}

static void check_name(environment const & env, name const & n) {
    if (env.find(n))
        throw already_declared_exception(env, n);
}

void environment::check_name(name const & n) const {
    ::lean::check_name(*this, n);
}

static void check_duplicated_univ_params(environment const & env, names ls) {
    while (!is_nil(ls)) {
        auto const & p = head(ls);
        ls = tail(ls);
        if (std::find(ls.begin(), ls.end(), p) != ls.end()) {
            throw kernel_exception(env, sstream() << "failed to add declaration to environment, "
                                   << "duplicate universe level parameter: '"
                                   << p << "'");
        }
    }
}

void environment::check_duplicated_univ_params(names ls) const {
    ::lean::check_duplicated_univ_params(*this, ls);
}

void environment::add_core(constant_info const & info) {
    m_obj = lean_environment_add(m_obj, info.to_obj_arg());
}

environment environment::add(constant_info const & info) const {
    return environment(lean_environment_add(to_obj_arg(), info.to_obj_arg()));
}

environment environment::add(declaration const & d, bool check) const {
    ensure_lean_kernel_initialized();
    if (check)
        return get_or_throw_kernel_exception<environment>(
            lean_kernel_add_decl_impl(to_obj_arg(), box(static_cast<size_t>(0)), d.to_obj_arg(), box(0)));
    return get_or_throw_kernel_exception<environment>(
        lean_kernel_add_decl_without_checking_impl(to_obj_arg(), d.to_obj_arg()));
}
/*
addDeclCore (env : Environment) (maxHeartbeats : USize) (decl : @& Declaration)
  (cancelTk? : @& Option IO.CancelToken) : Except Kernel.Exception Environment
*/
extern "C" LEAN_EXPORT object * lean_add_decl(object * env, size_t max_heartbeat, object * decl,
    object * opt_cancel_tk) {
    ensure_lean_kernel_initialized();
    return lean_kernel_add_decl_impl(env, box(max_heartbeat), decl, opt_cancel_tk);
}

extern "C" LEAN_EXPORT object * lean_add_decl_without_checking(object * env, object * decl) {
    ensure_lean_kernel_initialized();
    return lean_kernel_add_decl_without_checking_impl(env, decl);
}

void environment::for_each_constant(std::function<void(constant_info const & d)> const & f) const {
    smap_foreach(cnstr_get(raw(), 1), [&](object *, object * v) {
            constant_info cinfo(v, true);
            f(cinfo);
        });
}

void initialize_environment() {
}

void finalize_environment() {
}
}
