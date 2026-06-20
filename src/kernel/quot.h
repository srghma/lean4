/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Quotient types.
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/local_ctx.h"

namespace lean {
class quot_consts {
    static name const & persistent_name(char const * n) {
        if (std::strcmp(n, "Quot") == 0) {
            static name * r = []() {
                auto * n = new name{"Quot"};
                mark_persistent(n->raw());
                return n;
            }();
            return *r;
        } else if (std::strcmp(n, "Quot.lift") == 0) {
            static name * r = []() {
                auto * n = new name{"Quot", "lift"};
                mark_persistent(n->raw());
                return n;
            }();
            return *r;
        } else if (std::strcmp(n, "Quot.ind") == 0) {
            static name * r = []() {
                auto * n = new name{"Quot", "ind"};
                mark_persistent(n->raw());
                return n;
            }();
            return *r;
        } else {
            static name * r = []() {
                auto * n = new name{"Quot", "mk"};
                mark_persistent(n->raw());
                return n;
            }();
            return *r;
        }
    }

    template<typename WHNF> friend optional<expr> quot_reduce_rec(expr const & e, WHNF const & whnf);
    friend class environment;
    friend void initialize_quot();
    friend void finalize_quot();
public:
    static name const & quot() { return persistent_name("Quot"); }
    static name const & lift() { return persistent_name("Quot.lift"); }
    static name const & ind() { return persistent_name("Quot.ind"); }
    static name const & mk() { return persistent_name("Quot.mk"); }
};

/** \brief Try to reduce a `quot` recursor application (i.e., `quot.lift` or `quot.ind` application).

    `whnf : expr -> expr` */
template<typename WHNF> optional<expr> quot_reduce_rec(expr const & e, WHNF const & whnf) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return none_expr();
    unsigned mk_pos;
    unsigned arg_pos;
    if (const_name(fn) == quot_consts::lift()) {
        mk_pos  = 5;
        arg_pos = 3;
    } else if (const_name(fn) == quot_consts::ind()) {
        mk_pos  = 4;
        arg_pos = 3;
    } else {
        return none_expr();
    }
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= mk_pos)
        return none_expr();

    expr mk = whnf(args[mk_pos]);
    expr const & mk_fn = get_app_fn(mk);
    if (!is_constant(mk_fn) || const_name(mk_fn) != quot_consts::mk() || get_app_num_args(mk) != 3)
        return none_expr();

    expr const & f = args[arg_pos];
    expr r = mk_app(f, app_arg(mk));
    unsigned elim_arity = mk_pos+1;
    if (args.size() > elim_arity)
        r = mk_app(r, args.size() - elim_arity, args.begin() + elim_arity);
    return some_expr(r);
}

namespace quot_detail {
inline void check_eq_type(environment const & env) {
    constant_info eq_info = env.get("Eq");
    if (!eq_info.is_inductive()) throw exception("failed to initialize quot module, environment does not have 'Eq' type");
    inductive_val eq_val  = eq_info.to_inductive_val();
    if (length(eq_info.get_lparams()) != 1)
        throw exception("failed to initialize quot module, unexpected number of universe params at 'Eq' type");
    if (length(eq_val.get_cnstrs()) != 1)
        throw exception("failed to initialize quot module, unexpected number of constructors for 'Eq' type");
    local_ctx lctx;
    name_generator g;
    {
        level u = mk_univ_param(head(eq_info.get_lparams()));
        expr alpha = lctx.mk_local_decl(g, "α", mk_sort(u), mk_implicit_binder_info());
        expr expected_eq_type = lctx.mk_pi(alpha, mk_arrow(alpha, mk_arrow(alpha, mk_Prop())));
        if (expected_eq_type != eq_info.get_type())
            throw exception("failed to initialize quot module, 'Eq' has an expected type");
    }
    {
        constant_info eq_refl_info = env.get(head(eq_val.get_cnstrs()));
        level u = mk_univ_param(head(eq_refl_info.get_lparams()));
        expr alpha = lctx.mk_local_decl(g, "α", mk_sort(u), mk_implicit_binder_info());
        expr a = lctx.mk_local_decl(g, "a", alpha);
        expr expected_eq_refl_type = lctx.mk_pi({alpha, a}, mk_app(mk_constant("Eq", {u}), alpha, a, a));
        if (eq_refl_info.get_type() != expected_eq_refl_type)
            throw exception("failed to initialize quot module, unexpected type for 'Eq' type constructor");
    }
}
}

inline environment environment::add_quot() const {
    if (is_quot_initialized())
        return *this;
    quot_detail::check_eq_type(*this);
    environment new_env = *this;
    name u_name("u");
    local_ctx lctx;
    name_generator g;
    level u         = mk_univ_param(u_name);
    expr Sort_u     = mk_sort(u);
    expr alpha      = lctx.mk_local_decl(g, "α", Sort_u, mk_implicit_binder_info());
    expr r          = lctx.mk_local_decl(g, "r", mk_arrow(alpha, mk_arrow(alpha, mk_Prop())));
    new_env.add_core(constant_info(quot_val(quot_consts::quot(), {u_name}, lctx.mk_pi({alpha, r}, Sort_u), quot_kind::Type)));
    expr quot_r     = mk_app(mk_constant(quot_consts::quot(), {u}), alpha, r);
    expr a          = lctx.mk_local_decl(g, "a", alpha);
    new_env.add_core(constant_info(quot_val(quot_consts::mk(), {u_name}, lctx.mk_pi({alpha, r, a}, quot_r), quot_kind::Mk)));
    lctx = local_ctx();
    alpha           = lctx.mk_local_decl(g, "α", Sort_u, mk_implicit_binder_info());
    r               = lctx.mk_local_decl(g, "r", mk_arrow(alpha, mk_arrow(alpha, mk_Prop())), mk_implicit_binder_info());
    quot_r          = mk_app(mk_constant(quot_consts::quot(), {u}), alpha, r);
    a               = lctx.mk_local_decl(g, "a", alpha);
    name v_name("v");
    level v         = mk_univ_param(v_name);
    expr Sort_v     = mk_sort(v);
    expr beta       = lctx.mk_local_decl(g, "β", Sort_v, mk_implicit_binder_info());
    expr f          = lctx.mk_local_decl(g, "f", mk_arrow(alpha, beta));
    expr b          = lctx.mk_local_decl(g, "b", alpha);
    expr r_a_b      = mk_app(r, a, b);
    expr f_a_eq_f_b = mk_app(mk_constant("Eq", {v}), beta, mk_app(f, a), mk_app(f, b));
    expr sanity     = lctx.mk_pi({a, b}, mk_arrow(r_a_b, f_a_eq_f_b));
    new_env.add_core(constant_info(quot_val(quot_consts::lift(), {u_name, v_name},
                                            lctx.mk_pi({alpha, r, beta, f}, mk_arrow(sanity, mk_arrow(quot_r, beta))), quot_kind::Lift)));
    beta            = lctx.mk_local_decl(g, "β", mk_arrow(quot_r, mk_Prop()), mk_implicit_binder_info());
    expr quot_mk_a  = mk_app(mk_constant(quot_consts::mk(), {u}), alpha, r, a);
    expr all_quot   = lctx.mk_pi(a, mk_app(beta, quot_mk_a));
    expr q          = lctx.mk_local_decl(g, "q", quot_r);
    expr beta_q     = mk_app(beta, q);
    new_env.add_core(constant_info(quot_val(quot_consts::ind(), {u_name},
                                            lctx.mk_pi({alpha, r, beta}, mk_pi("mk", all_quot, lctx.mk_pi(q, beta_q))), quot_kind::Ind)));
    new_env.mark_quot_initialized();
    return new_env;
}

void initialize_quot();
void finalize_quot();
}
