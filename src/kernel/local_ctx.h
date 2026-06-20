/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <limits>
#include "runtime/exception.h"
#include "runtime/sstream.h"
#include "util/name_generator.h"
#include "kernel/abstract.h"
#include "kernel/expr.h"

namespace lean {
extern "C" object * lean_mk_local_decl(object * index, object * fvarid, object * user_name, object * type, uint8 bi);
extern "C" object * lean_mk_let_decl(object * index, object * fvarid, object * user_name, object * type, object * val);
extern "C" uint8 lean_local_decl_binder_info(object * d);
extern "C" object * lean_mk_empty_local_ctx(object*);
extern "C" object * lean_local_ctx_num_indices(object*);
extern "C" uint8 lean_local_ctx_is_empty(object*);
extern "C" object * lean_local_ctx_mk_local_decl(object * lctx, object * name, object * user_name, object * expr, uint8 bi);
extern "C" object * lean_local_ctx_mk_let_decl(object * lctx, object * name, object * user_name, object * type, object * value, uint8 non_dep);
extern "C" object * lean_local_ctx_find(object * lctx, object * name);

/*
inductive LocalDecl
| cdecl (index : Nat) (name : Name) (userName : Name) (type : Expr) (bi : BinderInfo)
| ldecl (index : Nat) (name : Name) (userName : Name) (type : Expr) (value : Expr)
*/
class local_decl : public object_ref {
    friend class local_ctx;
    friend class local_context;
    friend void initialize_local_ctx();
    local_decl(unsigned idx, name const & n, name const & un, expr const & t, expr const & v);
    local_decl(local_decl const & d, expr const & t, expr const & v);
    local_decl(unsigned idx, name const & n, name const & un, expr const & t, binder_info bi);
    local_decl(local_decl const & d, expr const & t);
public:
    local_decl();
    local_decl(local_decl const & other):object_ref(other) {}
    local_decl(local_decl && other) noexcept:object_ref(std::move(other)) {}
    local_decl(obj_arg o):object_ref(o) {}
    local_decl(b_obj_arg o, bool):object_ref(o, true) {}
    local_decl & operator=(local_decl const & other) { object_ref::operator=(other); return *this; }
    local_decl & operator=(local_decl && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    friend bool is_eqp(local_decl const & d1, local_decl const & d2) { return d1.raw() == d2.raw(); }
    unsigned get_idx() const { return static_cast<nat const &>(cnstr_get_ref(raw(), 0)).get_small_value(); }
    name const & get_name() const { return static_cast<name const &>(cnstr_get_ref(raw(), 1)); }
    name const & get_user_name() const { return static_cast<name const &>(cnstr_get_ref(raw(), 2)); }
    expr const & get_type() const { return static_cast<expr const &>(cnstr_get_ref(raw(), 3)); }
    optional<expr> get_value() const {
        if (cnstr_tag(raw()) == 0) return none_expr();
        return some_expr(static_cast<expr const &>(cnstr_get_ref(raw(), 4)));
    }
    binder_info get_info() const {
        return static_cast<binder_info>(lean_local_decl_binder_info(to_obj_arg()));
    }
    expr mk_ref() const {
        return mk_fvar(get_name());
    }
};

namespace local_ctx_detail {
inline object * mk_dummy_local_decl() {
    static object * r = []() {
        object * d = lean_mk_local_decl(nat(std::numeric_limits<unsigned>::max()).to_obj_arg(),
                                        name("__local_decl_for_default_constructor").to_obj_arg(),
                                        name("__local_decl_for_default_constructor").to_obj_arg(),
                                        mk_Prop().to_obj_arg(),
                                        static_cast<uint8>(mk_binder_info()));
        mark_persistent(d);
        return d;
    }();
    return r;
}
}

inline local_decl::local_decl():object_ref(local_ctx_detail::mk_dummy_local_decl(), true) {}

inline local_decl::local_decl(unsigned idx, name const & n, name const & un, expr const & t, expr const & v):
    object_ref(lean_mk_let_decl(nat(idx).to_obj_arg(), n.to_obj_arg(), un.to_obj_arg(), t.to_obj_arg(), v.to_obj_arg())) {
}

inline local_decl::local_decl(unsigned idx, name const & n, name const & un, expr const & t, binder_info bi):
    object_ref(lean_mk_local_decl(nat(idx).to_obj_arg(), n.to_obj_arg(), un.to_obj_arg(), t.to_obj_arg(), static_cast<uint8>(bi))) {
}

inline local_decl::local_decl(local_decl const & d, expr const & t, expr const & v):
    local_decl(d.get_idx(), d.get_name(), d.get_user_name(), t, v) {}

inline local_decl::local_decl(local_decl const & d, expr const & t):
    local_decl(d.get_idx(), d.get_name(), d.get_user_name(), t, d.get_info()) {}

/* Plain local context object used by the kernel type checker. */
class local_ctx : public object_ref {
protected:
    template<bool is_lambda> expr mk_binding(unsigned num, expr const * fvars, expr const & b, bool remove_dead_let = false) const;
public:
    local_ctx();
    explicit local_ctx(obj_arg o):object_ref(o) {}
    local_ctx(b_obj_arg o, bool):object_ref(o, true) {}
    local_ctx(local_ctx const & other):object_ref(other) {}
    local_ctx(local_ctx && other) noexcept:object_ref(std::move(other)) {}
    local_ctx & operator=(local_ctx const & other) { object_ref::operator=(other); return *this; }
    local_ctx & operator=(local_ctx && other) noexcept { object_ref::operator=(std::move(other)); return *this; }

    bool empty() const {
        return lean_local_ctx_is_empty(to_obj_arg());
    }

    /* Low level `mk_local_decl` */
    local_decl mk_local_decl(name const & n, name const & un, expr const & type, binder_info bi) {
        unsigned idx = unbox(lean_local_ctx_num_indices(to_obj_arg()));
        m_obj = lean_local_ctx_mk_local_decl(raw(), n.to_obj_arg(), un.to_obj_arg(), type.to_obj_arg(), static_cast<uint8>(bi));
        return local_decl(idx, n, un, type, bi);
    }

    /* Low level `mk_local_decl` */
    local_decl mk_local_decl(name const & n, name const & un, expr const & type, expr const & value) {
        unsigned idx = unbox(lean_local_ctx_num_indices(to_obj_arg()));
        m_obj = lean_local_ctx_mk_let_decl(raw(), n.to_obj_arg(), un.to_obj_arg(), type.to_obj_arg(), value.to_obj_arg(), false);
        return local_decl(idx, n, un, type, value);
    }

    expr mk_local_decl(name_generator & g, name const & un, expr const & type, binder_info bi = mk_binder_info()) {
        return mk_local_decl(g.next(), un, type, bi).mk_ref();
    }

    expr mk_local_decl(name_generator & g, name const & un, expr const & type, expr const & value) {
        return mk_local_decl(g.next(), un, type, value).mk_ref();
    }

    /** \brief Return the local declarations for the given reference. */
    optional<local_decl> find_local_decl(name const & n) const {
        return to_optional<local_decl>(lean_local_ctx_find(to_obj_arg(), n.to_obj_arg()));
    }

    optional<local_decl> find_local_decl(expr const & e) const { return find_local_decl(fvar_name(e)); }

    local_decl get_local_decl(name const & n) const {
        if (optional<local_decl> r = find_local_decl(n)) {
            return *r;
        } else {
            throw exception(sstream() << "unknown free variable: " << n);
        }
    }

    local_decl get_local_decl(expr const & e) const { return get_local_decl(fvar_name(e)); }

    /* \brief Return type of the given free variable.
       \pre is_fvar(e) */
    expr get_type(expr const & e) const { return get_local_decl(e).get_type(); }

    expr mk_lambda(unsigned num, expr const * fvars, expr const & e, bool remove_dead_let = false) const {
        return mk_binding<true>(num, fvars, e, remove_dead_let);
    }

    expr mk_pi(unsigned num, expr const * fvars, expr const & e, bool remove_dead_let = false) const {
        return mk_binding<false>(num, fvars, e, remove_dead_let);
    }

    expr mk_lambda(buffer<expr> const & fvars, expr const & e, bool remove_dead_let = false) const { return mk_lambda(fvars.size(), fvars.data(), e, remove_dead_let); }
    expr mk_pi(buffer<expr> const & fvars, expr const & e, bool remove_dead_let = false) const { return mk_pi(fvars.size(), fvars.data(), e, remove_dead_let); }
    expr mk_lambda(expr const & fvar, expr const & e) { return mk_lambda(1, &fvar, e); }
    expr mk_pi(expr const & fvar, expr const & e) { return mk_pi(1, &fvar, e); }
    expr mk_lambda(std::initializer_list<expr> const & fvars, expr const & e) { return mk_lambda(fvars.size(), fvars.begin(), e); }
    expr mk_pi(std::initializer_list<expr> const & fvars, expr const & e) { return mk_pi(fvars.size(), fvars.begin(), e); }
};

void initialize_local_ctx();
void finalize_local_ctx();

inline local_ctx::local_ctx():object_ref(lean_mk_empty_local_ctx(box(0))) {
}

template<bool is_lambda>
inline expr local_ctx::mk_binding(unsigned num, expr const * fvars, expr const & b, bool remove_dead_let) const {
    expr r     = abstract(b, num, fvars);
    unsigned i = num;
    while (i > 0) {
        --i;
        local_decl const & decl = get_local_decl(fvar_name(fvars[i]));
        if (optional<expr> const & opt_val = decl.get_value()) {
            if (!remove_dead_let || has_loose_bvar(r, 0)) {
                expr type  = abstract(decl.get_type(), i, fvars);
                expr value = abstract(*opt_val, i, fvars);
                r = ::lean::mk_let(decl.get_user_name(), type, value, r);
            } else {
                r = lower_loose_bvars(r, 1, 1);
            }
        } else if (is_lambda) {
            expr type = abstract(decl.get_type(), i, fvars);
            r = ::lean::mk_lambda(decl.get_user_name(), type, r, decl.get_info());
        } else {
            expr type = abstract(decl.get_type(), i, fvars);
            r = ::lean::mk_pi(decl.get_user_name(), type, r, decl.get_info());
        }
    }
    return r;
}
}
