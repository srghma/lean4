/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_generator.h"

namespace lean {
LEAN_EXPORT void initialize_name_generator() {
    g_ngen_prefixes = new name_set();
    g_tmp_prefix    = new name("_uniq");
    mark_persistent(g_tmp_prefix->raw());
    register_name_generator_prefix(*g_tmp_prefix);
}

LEAN_EXPORT void finalize_name_generator() {
    delete g_tmp_prefix;
    delete g_ngen_prefixes;
}
}
