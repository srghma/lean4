/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "runtime/object.h"

namespace lean {
/* Helper functions for iterating over Lean maps. */
namespace detail {
using map_foreach_fn = void (*)(b_obj_arg, b_obj_arg, void *);

extern "C" inline void map_foreach_callback(b_obj_arg k, b_obj_arg v, void * ctx) {
    (*static_cast<std::function<void(b_obj_arg, b_obj_arg)> *>(ctx))(k, v);
}
}

extern "C" void lean_rbmap_foreach(b_obj_arg m, detail::map_foreach_fn fn, void * ctx);
extern "C" void lean_phashmap_foreach(b_obj_arg m, detail::map_foreach_fn fn, void * ctx);
extern "C" void lean_hashmap_foreach(b_obj_arg m, detail::map_foreach_fn fn, void * ctx);
extern "C" void lean_smap_foreach(b_obj_arg m, detail::map_foreach_fn fn, void * ctx);

inline void rbmap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn) {
    lean_rbmap_foreach(m, detail::map_foreach_callback, const_cast<std::function<void(b_obj_arg, b_obj_arg)> *>(&fn));
}

inline void phashmap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn) {
    lean_phashmap_foreach(m, detail::map_foreach_callback, const_cast<std::function<void(b_obj_arg, b_obj_arg)> *>(&fn));
}

inline void hashmap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn) {
    lean_hashmap_foreach(m, detail::map_foreach_callback, const_cast<std::function<void(b_obj_arg, b_obj_arg)> *>(&fn));
}

inline void smap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn) {
    lean_smap_foreach(m, detail::map_foreach_callback, const_cast<std::function<void(b_obj_arg, b_obj_arg)> *>(&fn));
}
}
