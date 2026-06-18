/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name.h"
#include "util/kvmap.h"

#ifndef LEAN_DEFAULT_VERBOSE
#define LEAN_DEFAULT_VERBOSE true
#endif

namespace lean {
/** \brief Configuration options. */
class options : public object_ref {
public:
    options();
    explicit options(obj_arg o): object_ref(o) {}
    bool get_bool(name const & n, bool default_value = false) const;
    options update(name const & n, bool v) const;
    friend bool is_eqp(options const & a, options const & b) { return a.raw() == b.raw(); }
};

extern "C" LEAN_EXPORT obj_res lean_options_get_empty(obj_arg u);
extern "C" LEAN_EXPORT bool lean_options_get_bool(obj_arg opts, obj_arg n, bool default_value);
extern "C" LEAN_EXPORT obj_res lean_options_update_bool(obj_arg opts, obj_arg n, bool v);

void initialize_options();
void finalize_options();
}
