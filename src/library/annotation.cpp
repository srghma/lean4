/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/annotation.h"

namespace lean {
static name * g_annotation = nullptr;

LEAN_EXPORT void initialize_annotation() {
    g_annotation = new name("annotation");
    mark_persistent(g_annotation->raw());
}

LEAN_EXPORT void finalize_annotation() {
    delete g_annotation;
}
}
