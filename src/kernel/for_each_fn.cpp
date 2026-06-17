/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "runtime/memory.h"
#include "util/alloc.h"
#include "runtime/interrupt.h"
#include "runtime/flet.h"
#include "kernel/for_each_fn.h"

namespace lean {

class for_each_offset_fn {
    struct key_hasher {
        std::size_t operator()(std::pair<lean_object *, unsigned> const & p) const {
            return hash((size_t)p.first, p.second);
        }
    };
    lean::unordered_set<std::pair<lean_object *, unsigned>, key_hasher> m_cache;
    std::function<bool(expr const &, unsigned)> m_f; // NOLINT

    bool visited(expr const & e, unsigned offset) {
        if (is_likely_unshared(e)) return false;
        if (m_cache.find(std::make_pair(e.raw(), offset)) != m_cache.end()) return true;
        m_cache.insert(std::make_pair(e.raw(), offset));
        return false;
    }

    void apply(expr const & e, unsigned offset) {
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar: case expr_kind::Sort:
            m_f(e, offset);
            return;
        default:
            break;
        }

        if (visited(e, offset))
            return;

        if (!m_f(e, offset))
            return;

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar:
        case expr_kind::Sort:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return;
        case expr_kind::MData:
            apply(mdata_expr(e), offset);
            return;
        case expr_kind::Proj:
            apply(proj_expr(e), offset);
            return;
        case expr_kind::App:
            apply(app_fn(e), offset);
            apply(app_arg(e), offset);
            return;
        case expr_kind::Lambda: case expr_kind::Pi:
            apply(binding_domain(e), offset);
            apply(binding_body(e), offset+1);
            return;
        case expr_kind::Let:
            apply(let_type(e), offset);
            apply(let_value(e), offset);
            apply(let_body(e), offset+1);
            return;
        }
    }

public:
    for_each_offset_fn(std::function<bool(expr const &, unsigned)> && f):m_f(f) {}        // NOLINT
    for_each_offset_fn(std::function<bool(expr const &, unsigned)> const & f):m_f(f) {}   // NOLINT
    void operator()(expr const & e) { apply(e, 0); }
};

void for_each(expr const & e, std::function<bool(expr const &, unsigned)> && f) { // NOLINT
    return for_each_offset_fn(f)(e);
}

}
