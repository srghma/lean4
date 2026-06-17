/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <lean/version.h>
#include "kernel/expr.h"
#include "library/util.h"
#include "library/constants.h"
#include "util/name_generator.h"

namespace lean {

static expr * g_bool       = nullptr;
static expr * g_bool_true  = nullptr;
static expr * g_bool_false = nullptr;

static void initialize_bool() {
    g_bool = new expr(mk_constant(get_bool_name()));
    mark_persistent(g_bool->raw());
    g_bool_false = new expr(mk_constant(get_bool_false_name()));
    mark_persistent(g_bool_false->raw());
    g_bool_true = new expr(mk_constant(get_bool_true_name()));
    mark_persistent(g_bool_true->raw());
}

static void finalize_bool() {
    delete g_bool;
    delete g_bool_false;
    delete g_bool_true;
}

expr mk_bool_true()  { return *g_bool_true;  }
expr mk_bool_false() { return *g_bool_false; }

static std::string * g_short_version_string = nullptr;
std::string const & get_short_version_string() { return *g_short_version_string; }

static name * g_util_fresh = nullptr;

LEAN_EXPORT void initialize_library_util() {
    initialize_bool();
    g_short_version_string = new std::string(LEAN_VERSION_STRING);
    g_util_fresh = new name("_util_fresh");
    mark_persistent(g_util_fresh->raw());
    register_name_generator_prefix(*g_util_fresh);
}

LEAN_EXPORT void finalize_library_util() {
    delete g_util_fresh;
    delete g_short_version_string;
    finalize_bool();
}
}
