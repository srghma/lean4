/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "runtime/debug.h"

namespace lean {
extern "C" unsigned lean_util_log2(unsigned v);

inline bool is_power_of_two(unsigned v) { return !(v & (v - 1)) && v; }
inline unsigned log2(unsigned v) { return lean_util_log2(v); }
inline double log2(int v) {
    (void)v;
    lean_unreachable();
}
}
