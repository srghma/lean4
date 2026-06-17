/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stdint.h>
#include <lean/lean.h>

namespace lean {
LEAN_EXPORT void add_heartbeats(uint64_t count);
void initialize_alloc();
void finalize_alloc();
}
