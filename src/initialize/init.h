/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

extern "C" void lean_initialize();
extern "C" void lean_finalize();

namespace lean {
inline void initialize() { lean_initialize(); }
inline void finalize() { lean_finalize(); }
/** \brief Helper object for initializing Lean */
class initializer {
public:
    initializer() { lean_initialize(); }
    ~initializer() { lean_finalize(); }
};
}
