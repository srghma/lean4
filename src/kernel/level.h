/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <functional>
#include <ostream>
#include "runtime/list_ref.h"
#include "runtime/interrupt.h"
#include "util/name.h"

namespace lean {
extern "C" {
    unsigned lean_level_hash(obj_arg l);
    unsigned lean_level_depth(obj_arg l);
    uint8 lean_level_has_mvar(obj_arg l);
    uint8 lean_level_has_param(obj_arg l);
    object * lean_level_mk_zero(object*);
    object * lean_level_mk_succ(obj_arg);
    object * lean_level_mk_mvar(obj_arg);
    object * lean_level_mk_param(obj_arg);
    object * lean_level_mk_max(obj_arg, obj_arg);
    object * lean_level_mk_imax(obj_arg, obj_arg);
}
class environment;
struct level_cell;
/**
inductive level
| zero   : level
| succ   : level → level
| max    : level → level → level
| imax   : level → level → level
| param  : name → level
| mvar   : name → level

We level.imax to handle Pi-types.
*/
enum class level_kind { Zero, Succ, Max, IMax, Param, MVar };

/** \brief Universe level. */
class level : public object_ref {
    friend level mk_succ(level const & l);
    friend level mk_max_core(level const & l1, level const & l2);
    friend level mk_imax_core(level const & l1, level const & l2);
    friend level mk_univ_param(name const & n);
    friend level mk_univ_mvar(name const & n);
    explicit level(object_ref && o) noexcept:object_ref(o) {}
public:
    /** \brief Universe zero */
    level();
    explicit level(obj_arg o):object_ref(o) {}
    explicit level(b_obj_arg o, bool b):object_ref(o, b) {}
    level(level const & other):object_ref(other) {}
    level(level && other) noexcept:object_ref(std::move(other)) {}
    level_kind kind() const {
      return lean_is_scalar(raw()) ? level_kind::Zero : static_cast<level_kind>(lean_ptr_tag(raw()));
    }
    unsigned hash() const;

    level & operator=(level const & other) { object_ref::operator=(other); return *this; }
    level & operator=(level && other) noexcept { object_ref::operator=(std::move(other)); return *this; }

    friend bool is_eqp(level const & l1, level const & l2) { return l1.raw() == l2.raw(); }

    bool is_zero() const { return kind() == level_kind::Zero; }
    bool is_succ() const { return kind() == level_kind::Succ; }
    bool is_max() const { return kind() == level_kind::Max; }
    bool is_imax() const { return kind() == level_kind::IMax; }
    bool is_param() const { return kind() == level_kind::Param; }
    bool is_mvar() const { return kind() == level_kind::MVar; }

    friend inline level const & max_lhs(level const & l) { lean_assert(l.is_max()); return static_cast<level const &>(cnstr_get_ref(l, 0)); }
    friend inline level const & max_rhs(level const & l) { lean_assert(l.is_max()); return static_cast<level const &>(cnstr_get_ref(l, 1)); }
    friend inline level const & imax_lhs(level const & l) { lean_assert(l.is_imax()); return static_cast<level const &>(cnstr_get_ref(l, 0)); }
    friend inline level const & imax_rhs(level const & l) { lean_assert(l.is_imax()); return static_cast<level const &>(cnstr_get_ref(l, 1)); }
    friend inline level const & level_lhs(level const & l) { lean_assert(l.is_max() || l.is_imax()); return static_cast<level const &>(cnstr_get_ref(l, 0)); }
    friend inline level const & level_rhs(level const & l) { lean_assert(l.is_max() || l.is_imax()); return static_cast<level const &>(cnstr_get_ref(l, 1)); }
    friend inline level const & succ_of(level const & l) { lean_assert(l.is_succ()); return static_cast<level const &>(cnstr_get_ref(l, 0)); }
    friend inline name const & param_id(level const & l) { lean_assert(l.is_param()); return static_cast<name const &>(cnstr_get_ref(l, 0)); }
    friend inline name const & mvar_id(level const & l)  { lean_assert(l.is_mvar()); return static_cast<name const &>(cnstr_get_ref(l, 0)); }
    friend inline name const & level_id(level const & l) { lean_assert(l.is_param() || l.is_mvar()); return static_cast<name const &>(cnstr_get_ref(l, 0)); }
};

typedef list_ref<level> levels;

inline bool is_shared(level const & l) { return !is_exclusive(l.raw()); }

bool operator==(level const & l1, level const & l2);
inline bool operator!=(level const & l1, level const & l2) { return !operator==(l1, l2); }

level const & mk_level_zero();
level const & mk_level_one();
level mk_max_core(level const & l1, level const & l2);
level mk_imax_core(level const & l1, level const & l2);
level mk_max(level const & l1, level const & l2);
level mk_imax(level const & l1, level const & l2);
level mk_succ(level const & l);
level mk_univ_param(name const & n);
level mk_univ_mvar(name const & n);

inline unsigned hash(level const & l) { return l.hash(); }
inline level_kind kind(level const & l) { return l.kind(); }
inline bool is_zero(level const & l)   { return l.is_zero(); }
inline bool is_param(level const & l)  { return l.is_param(); }
inline bool is_mvar(level const & l)   { return l.is_mvar(); }
inline bool is_succ(level const & l)   { return l.is_succ(); }
inline bool is_max(level const & l)    { return l.is_max(); }
inline bool is_imax(level const & l)   { return l.is_imax(); }
/** \brief Return true iff \c l is an explicit level.
    We say a level l is explicit iff
    1) l is zero OR
    2) l = succ(l') and l' is explicit */
bool is_explicit(level const & l);
/** \brief Return true iff \c l contains placeholder (aka meta parameters). */
bool has_mvar(level const & l);
/** \brief Return true iff \c l contains parameters */
bool has_param(level const & l);

/** \brief Return a new level expression based on <tt>l == succ(arg)</tt>, where \c arg is replaced with
    \c new_arg.
    \pre is_succ(l) */
level update_succ(level const & l, level const & new_arg);
/** \brief Return a new level expression based on <tt>l == max(lhs, rhs)</tt>, where \c lhs is replaced with
    \c new_lhs and \c rhs is replaced with \c new_rhs.

    \pre is_max(l) || is_imax(l) */
level update_max(level const & l, level const & new_lhs, level const & new_rhs);

/** \brief Return true if lhs and rhs denote the same level.
    The check is done by normalization. */
bool is_equivalent(level const & lhs, level const & rhs);
/** \brief Return the given level expression normal form */
level normalize(level const & l);

bool is_geq(level const & l1, level const & l2);

bool has_mvar(levels const & ls);
bool has_param(levels const & ls);

/** \brief If \c l contains a parameter that is not in \c ps, then return it. Otherwise, return none. */
optional<name> get_undef_param(level const & l, names const & lparams);

/** \brief Instantiate the universe level parameters \c ps occurring in \c l with the levels \c ls.
    \pre length(ps) == length(ls) */
level instantiate(level const & l, names const & ps, levels const & ls);

/** \brief Printer for debugging purposes */
std::ostream & operator<<(std::ostream & out, level const & l);

/** \brief If the result is true, then forall assignments \c A that assigns all parameters and metavariables occurring
    in \c l, l[A] != zero. */
bool is_not_zero(level const & l);

/** \brief Convert a list of universe level parameter names into a list of levels. */
levels lparams_to_levels(names const & ps);

void initialize_level();
void finalize_level();

namespace level_detail {
class for_each_level_fn {
    std::function<bool(level const &)> m_f;
    void apply(level const & l) {
        if (!m_f(l))
            return;
        switch (l.kind()) {
        case level_kind::Succ:
            apply(succ_of(l)); break;
        case level_kind::Max: case level_kind::IMax:
            apply(level_lhs(l)); apply(level_rhs(l)); break;
        case level_kind::Zero: case level_kind::Param:
        case level_kind::MVar:
            break;
        }
    }
public:
    template<typename F> explicit for_each_level_fn(F const & f):m_f(f) {}
    void operator()(level const & l) { apply(l); }
};

template<typename F> void for_each(level const & l, F const & f) { return for_each_level_fn(f)(l); }

class replace_level_fn {
    std::function<optional<level>(level const &)> m_f;
    level apply(level const & l) {
        optional<level> r = m_f(l);
        if (r)
            return *r;
        switch (l.kind()) {
        case level_kind::Succ:
            return update_succ(l, apply(succ_of(l)));
        case level_kind::Max: case level_kind::IMax: {
            level l1 = apply(level_lhs(l));
            level l2 = apply(level_rhs(l));
            return update_max(l, l1, l2);
        }
        case level_kind::Zero: case level_kind::Param: case level_kind::MVar:
            return l;
        }
        lean_unreachable();
    }
public:
    template<typename F> explicit replace_level_fn(F const & f):m_f(f) {}
    level operator()(level const & l) { return apply(l); }
};

template<typename F> level replace(level const & l, F const & f) { return replace_level_fn(f)(l); }

inline level const & zero() {
    static level * z = [] {
        level * r = new level(lean_level_mk_zero(box(0)));
        mark_persistent(r->raw());
        return r;
    }();
    return *z;
}

inline level const & one() {
    static level * o = [] {
        level * r = new level(mk_succ(zero()));
        mark_persistent(r->raw());
        return r;
    }();
    return *o;
}

inline unsigned get_depth(level const & l) {
    return lean_level_depth(l.to_obj_arg());
}
}

inline level::level():level(level_detail::zero()) {}
inline unsigned level::hash() const { return lean_level_hash(to_obj_arg()); }

inline level mk_succ(level const & l) { return level(lean_level_mk_succ(l.to_obj_arg())); }
inline level mk_max_core(level const & l1, level const & l2) { return level(lean_level_mk_max(l1.to_obj_arg(), l2.to_obj_arg())); }
inline level mk_imax_core(level const & l1, level const & l2) { return level(lean_level_mk_imax(l1.to_obj_arg(), l2.to_obj_arg())); }
inline level mk_univ_param(name const & n) { return level(lean_level_mk_param(n.to_obj_arg())); }
inline level mk_univ_mvar(name const & n) { return level(lean_level_mk_mvar(n.to_obj_arg())); }

inline level const & mk_level_zero() { return level_detail::zero(); }
inline level const & mk_level_one() { return level_detail::one(); }
inline bool is_one(level const & l) { return l == mk_level_one(); }
inline bool has_param(level const & l) { return lean_level_has_param(l.to_obj_arg()); }
inline bool has_mvar(level const & l) { return lean_level_has_mvar(l.to_obj_arg()); }

inline bool is_explicit(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero:
        return true;
    case level_kind::Param: case level_kind::MVar: case level_kind::Max: case level_kind::IMax:
        return false;
    case level_kind::Succ:
        return is_explicit(succ_of(l));
    }
    lean_unreachable();
}

inline pair<level, unsigned> to_offset(level l) {
    unsigned k = 0;
    while (is_succ(l)) {
        l = succ_of(l);
        k++;
    }
    return mk_pair(l, k);
}

inline level mk_max(level const & l1, level const & l2)  {
    if (is_explicit(l1) && is_explicit(l2)) {
        return level_detail::get_depth(l1) >= level_detail::get_depth(l2) ? l1 : l2;
    } else if (l1 == l2) {
        return l1;
    } else if (is_zero(l1)) {
        return l2;
    } else if (is_zero(l2)) {
        return l1;
    } else if (is_max(l2) && (max_lhs(l2) == l1 || max_rhs(l2) == l1)) {
        return l2;
    } else if (is_max(l1) && (max_lhs(l1) == l2 || max_rhs(l1) == l2)) {
        return l1;
    } else {
        auto p1 = to_offset(l1);
        auto p2 = to_offset(l2);
        if (p1.first == p2.first) {
            lean_assert(p1.second != p2.second);
            return p1.second > p2.second ? l1 : l2;
        } else {
            return mk_max_core(l1, l2);
        }
    }
}

inline level mk_imax(level const & l1, level const & l2) {
    if (is_not_zero(l2))
        return mk_max(l1, l2);
    else if (is_zero(l2))
        return l2;
    else if (is_zero(l1) || is_one(l1))
        return l2;
    else if (l1 == l2)
        return l1;
    else
        return mk_imax_core(l1, l2);
}

inline bool operator==(level const & l1, level const & l2) {
    if (kind(l1) != kind(l2)) return false;
    if (hash(l1) != hash(l2)) return false;
    if (is_eqp(l1, l2))       return true;
    switch (kind(l1)) {
    case level_kind::Zero:
        return true;
    case level_kind::Param: case level_kind::MVar:
        return level_id(l1) == level_id(l2);
    case level_kind::Max: case level_kind::IMax: case level_kind::Succ:
        if (level_detail::get_depth(l1) != level_detail::get_depth(l2))
            return false;
        break;
    }
    switch (kind(l1)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::MVar:
        lean_unreachable();
    case level_kind::Max: case level_kind::IMax:
        return level_lhs(l1) == level_lhs(l2) && level_rhs(l1) == level_rhs(l2);
    case level_kind::Succ:
        return succ_of(l1) == succ_of(l2);
    }
    lean_unreachable();
}

inline bool is_not_zero(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::MVar:
        return false;
    case level_kind::Succ:
        return true;
    case level_kind::Max:
        return is_not_zero(max_lhs(l)) || is_not_zero(max_rhs(l));
    case level_kind::IMax:
        return is_not_zero(imax_rhs(l));
    }
    lean_unreachable();
}

inline bool is_lt(level const & a, level const & b, bool use_hash) {
    if (is_eqp(a, b))              return false;
    unsigned da = level_detail::get_depth(a);
    unsigned db = level_detail::get_depth(b);
    if (da < db)                   return true;
    if (da > db)                   return false;
    if (kind(a) != kind(b))        return kind(a) < kind(b);
    if (use_hash) {
        if (hash(a) < hash(b))     return true;
        if (hash(a) > hash(b))     return false;
    }
    if (a == b)                    return false;
    switch (kind(a)) {
    case level_kind::Zero:
        lean_unreachable();
    case level_kind::Param: case level_kind::MVar:
        return level_id(a) < level_id(b);
    case level_kind::Max: case level_kind::IMax:
        if (level_lhs(a) != level_lhs(b))
            return is_lt(level_lhs(a), level_lhs(b), use_hash);
        else
            return is_lt(level_rhs(a), level_rhs(b), use_hash);
    case level_kind::Succ:
        return is_lt(succ_of(a), succ_of(b), use_hash);
    }
    lean_unreachable();
}

inline bool is_lt(levels const & as, levels const & bs, bool use_hash) {
    if (is_nil(as))
        return !is_nil(bs);
    if (is_nil(bs))
        return false;
    if (car(as) == car(bs))
        return is_lt(cdr(as), cdr(bs), use_hash);
    else
        return is_lt(car(as), car(bs), use_hash);
}

inline bool levels_has_param(b_obj_arg ls) {
    while (!is_scalar(ls)) {
        if (lean_level_has_param(cnstr_get(ls, 0))) return true;
        ls = cnstr_get(ls, 1);
    }
    return false;
}

inline bool levels_has_mvar(b_obj_arg ls) {
    while (!is_scalar(ls)) {
        if (lean_level_has_mvar(cnstr_get(ls, 0))) return true;
        ls = cnstr_get(ls, 1);
    }
    return false;
}

inline bool has_param(levels const & ls) { return levels_has_param(ls.raw()); }
inline bool has_mvar(levels const & ls) { return levels_has_mvar(ls.raw()); }

inline optional<name> get_undef_param(level const & l, names const & ps) {
    optional<name> r;
    level_detail::for_each(l, [&](level const & l) {
            if (!has_param(l) || r)
                return false;
            if (is_param(l) && std::find(ps.begin(), ps.end(), param_id(l)) == ps.end())
                r = param_id(l);
            return true;
        });
    return r;
}

inline level update_succ(level const & l, level const & new_arg) {
    if (is_eqp(succ_of(l), new_arg))
        return l;
    else
        return mk_succ(new_arg);
}

inline level update_max(level const & l, level const & new_lhs, level const & new_rhs) {
    if (is_eqp(level_lhs(l), new_lhs) && is_eqp(level_rhs(l), new_rhs))
        return l;
    else if (is_max(l))
        return mk_max(new_lhs, new_rhs);
    else
        return mk_imax(new_lhs, new_rhs);
}

inline level instantiate(level const & l, names const & ps, levels const & ls) {
    lean_assert(length(ps) == length(ls));
    return level_detail::replace(l, [=](level const & l) {
            if (!has_param(l)) {
                return optional<level>(l);
            } else if (is_param(l)) {
                name const & id = param_id(l);
                names const *it1  = &ps;
                levels const *it2 = &ls;
                while (!is_nil(*it1) && !is_nil(*it2)) {
                    if (head(*it1) == id)
                        return optional<level>(head(*it2));
                    it1 = &tail(*it1);
                    it2 = &tail(*it2);
                }
                return optional<level>(l);
            } else {
                return optional<level>();
            }
        });
}

namespace level_detail {
inline void print(std::ostream & out, level l);
inline void print_child(std::ostream & out, level const & l) {
    if (is_explicit(l) || is_param(l) || is_mvar(l)) {
        print(out, l);
    } else {
        out << "(";
        print(out, l);
        out << ")";
    }
}

inline void print(std::ostream & out, level l) {
    if (is_explicit(l)) {
        out << get_depth(l);
    } else {
        switch (kind(l)) {
        case level_kind::Zero:
            lean_unreachable();
        case level_kind::Param:
            out << param_id(l); break;
        case level_kind::MVar:
            out << "?" << mvar_id(l); break;
        case level_kind::Succ:
            out << "succ "; print_child(out, succ_of(l)); break;
        case level_kind::Max: case level_kind::IMax:
            if (is_max(l))
                out << "max ";
            else
                out << "imax ";
            print_child(out, level_lhs(l));
            while (kind(level_rhs(l)) == kind(l)) {
                l = level_rhs(l);
                out << " ";
                print_child(out, level_lhs(l));
            }
            out << " ";
            print_child(out, level_rhs(l));
            break;
        }
    }
}

inline bool is_norm_lt(level const & a, level const & b) {
    if (is_eqp(a, b)) return false;
    auto p1 = to_offset(a);
    auto p2 = to_offset(b);
    level const & l1 = p1.first;
    level const & l2 = p2.first;
    if (l1 != l2) {
        if (kind(l1) != kind(l2)) return kind(l1) < kind(l2);
        switch (kind(l1)) {
        case level_kind::Zero: case level_kind::Succ:
            lean_unreachable();
        case level_kind::Param: case level_kind::MVar:
            return level_id(l1) < level_id(l2);
        case level_kind::Max: case level_kind::IMax:
            if (level_lhs(l1) != level_lhs(l2))
                return is_norm_lt(level_lhs(l1), level_lhs(l2));
            else
                return is_norm_lt(level_rhs(l1), level_rhs(l2));
        }
        lean_unreachable();
    } else {
        return p1.second < p2.second;
    }
}
}

inline std::ostream & operator<<(std::ostream & out, level const & l) {
    level_detail::print(out, l);
    return out;
}

inline void push_max_args(level const & l, buffer<level> & r) {
    if (is_max(l)) {
        push_max_args(max_lhs(l), r);
        push_max_args(max_rhs(l), r);
    } else {
        r.push_back(l);
    }
}

inline level mk_max(buffer<level> const & args) {
    lean_assert(!args.empty());
    unsigned nargs = args.size();
    if (nargs == 1) {
        return args[0];
    } else {
        lean_assert(nargs >= 2);
        level r = mk_max(args[nargs-2], args[nargs-1]);
        unsigned i = nargs-2;
        while (i > 0) {
            --i;
            r = mk_max(args[i], r);
        }
        return r;
    }
}

inline level mk_succ(level l, unsigned k) {
    while (k > 0) {
        --k;
        l = mk_succ(l);
    }
    return l;
}

inline level normalize(level const & l) {
    auto p = to_offset(l);
    level const & r = p.first;
    switch (kind(r)) {
    case level_kind::Succ:
        lean_unreachable();
    case level_kind::Zero:   case level_kind::Param:
    case level_kind::MVar:
        return l;
    case level_kind::IMax: {
        auto l1 = normalize(imax_lhs(r));
        auto l2 = normalize(imax_rhs(r));
        return mk_succ(mk_imax(l1, l2), p.second);
    }
    case level_kind::Max: {
        buffer<level> todo;
        buffer<level> args;
        push_max_args(r, todo);
        for (level const & a : todo)
            push_max_args(normalize(a), args);
        std::sort(args.begin(), args.end(), level_detail::is_norm_lt);
        buffer<level> & rargs = todo;
        rargs.clear();
        unsigned i = 0;
        if (is_explicit(args[i])) {
            while (i+1 < args.size() && is_explicit(args[i+1]))
                i++;
            lean_assert(is_explicit(args[i]));
            unsigned k = to_offset(args[i]).second;
            unsigned j = i+1;
            for (; j < args.size(); j++) {
                if (to_offset(args[j]).second >= k)
                    break;
            }
            if (j < args.size()) {
                i++;
            }
        }
        rargs.push_back(args[i]);
        auto p_prev = to_offset(args[i]);
        i++;
        for (; i < args.size(); i++) {
            auto p_curr = to_offset(args[i]);
            if (p_prev.first == p_curr.first) {
                if (p_prev.second < p_curr.second) {
                    p_prev = p_curr;
                    rargs.pop_back();
                    rargs.push_back(args[i]);
                }
            } else {
                p_prev = p_curr;
                rargs.push_back(args[i]);
            }
        }
        for (level & a : rargs)
            a = mk_succ(a, p.second);
        return mk_max(rargs);
    }}
    lean_unreachable();
}

inline bool is_equivalent(level const & lhs, level const & rhs) {
    check_system("level constraints");
    return lhs == rhs || normalize(lhs) == normalize(rhs);
}

inline bool is_geq_core(level l1, level l2) {
    if (l1 == l2 || is_zero(l2))
        return true;
    if (is_max(l2))
        return is_geq(l1, max_lhs(l2)) && is_geq(l1, max_rhs(l2));
    if (is_max(l1) && (is_geq(max_lhs(l1), l2) || is_geq(max_rhs(l1), l2)))
        return true;
    if (is_imax(l2))
        return is_geq(l1, imax_lhs(l2)) && is_geq(l1, imax_rhs(l2));
    if (is_imax(l1))
        return is_geq(imax_rhs(l1), l2);
    auto p1 = to_offset(l1);
    auto p2 = to_offset(l2);
    if (p1.first == p2.first || is_zero(p2.first))
        return p1.second >= p2.second;
    if (p1.second == p2.second && p1.second > 0)
        return is_geq(p1.first, p2.first);
    return false;
}

inline bool is_geq(level const & l1, level const & l2) {
    return is_geq_core(normalize(l1), normalize(l2));
}

inline levels lparams_to_levels(names const & ps) {
    buffer<level> ls;
    for (auto const & p : ps)
        ls.push_back(mk_univ_param(p));
    return levels(ls);
}
}
