/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "util/alloc.h"
#include "kernel/expr.h"

namespace lean {
template<typename T>
using expr_map = typename lean::unordered_map<expr, T, expr_hash, std::equal_to<expr>>;
};
