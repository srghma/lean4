/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {

extern "C" {
    void * lean_equiv_manager_new();
    void lean_equiv_manager_free(void * mgr);
    uint8 lean_equiv_manager_is_equiv(void * mgr, object * a, object * b, uint8 use_hash);
    void lean_equiv_manager_add_equiv(void * mgr, object * e1, object * e2);
}

class equiv_manager {
    void * m_impl;
public:
    equiv_manager() : m_impl(lean_equiv_manager_new()) {}
    ~equiv_manager() { lean_equiv_manager_free(m_impl); }
    bool is_equiv(expr const & e1, expr const & e2, bool use_hash = false) {
        return lean_equiv_manager_is_equiv(m_impl, e1.raw(), e2.raw(), use_hash ? 1 : 0) != 0;
    }
    void add_equiv(expr const & e1, expr const & e2) {
        lean_equiv_manager_add_equiv(m_impl, e1.raw(), e2.raw());
    }
};

}
