/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "runtime/object_ref.h"
#include "util/alloc.h"

extern "C" void * lean_sharecommon_persistent_create(bool check_set);
extern "C" void lean_sharecommon_persistent_free(void * state);
extern "C" void lean_sharecommon_persistent_set_check_set(void * state, bool check_set);
extern "C" lean_object * lean_sharecommon_persistent_run(void * state, lean_object * obj);
extern "C" lean_object * lean_sharecommon_quick_with_check_set(lean_object * obj, bool check_set);

namespace lean {
extern "C" LEAN_EXPORT uint8 lean_sharecommon_eq(b_obj_arg o1, b_obj_arg o2);
extern "C" LEAN_EXPORT uint64_t lean_sharecommon_hash(b_obj_arg o);
extern "C" LEAN_EXPORT lean_object * lean_sharecommon_quick(lean_object * a);

class LEAN_EXPORT sharecommon_quick_fn {
    bool m_check_set;
public:
    sharecommon_quick_fn(bool s = false): m_check_set(s) {}
    void set_check_set(bool f) { m_check_set = f; }
    lean_object * operator()(lean_object * a) {
        return lean_sharecommon_quick_with_check_set(a, m_check_set);
    }
};

class LEAN_EXPORT sharecommon_persistent_fn {
    void * m_state;
public:
    sharecommon_persistent_fn(bool s = false) {
        m_state = lean_sharecommon_persistent_create(s);
    }
    ~sharecommon_persistent_fn() {
        lean_sharecommon_persistent_free(m_state);
    }
    void set_check_set(bool f) {
        lean_sharecommon_persistent_set_check_set(m_state, f);
    }
    lean_object * operator()(lean_object * e) {
        return lean_sharecommon_persistent_run(m_state, e);
    }
};

};
