/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "kernel/expr.h"

namespace lean {

extern "C" void lean_for_each_expr_with_callback(
    object * e,
    void * ctx,
    uint8 (* callback)(void * ctx, object * e, unsigned offset));

namespace for_each_detail {
inline uint8 callback(void * ctx, object * e, unsigned offset) {
    auto const & f = *static_cast<std::function<bool(expr const &, unsigned)> const *>(ctx);
    return f(expr(e, true), offset) ? 1 : 0;
}
}

/**
   \brief Expression visitor.

   The argument \c f must be a callable with signature:
       bool(expr const & e, unsigned offset)
   where \c offset is the number of binders enclosing \c e.
   Return true to recurse into children, false to stop.
*/
inline void for_each(expr const & e, std::function<bool(expr const &, unsigned)> && f) { // NOLINT
    void * ctx = const_cast<void *>(static_cast<void const *>(&f));
    lean_for_each_expr_with_callback(e.raw(), ctx, for_each_detail::callback);
}

}
