/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include <memory>
#include <utility>
#include "kernel/expr.h"
#include "runtime/exception.h"
#include "util/options.h"

namespace lean {
inline std::function<void(std::ostream &, expr const &)> *& get_print_fn_storage() {
    static std::function<void(std::ostream &, expr const &)> * g_print = nullptr;
    return g_print;
}

inline void set_print_fn(std::function<void(std::ostream &, expr const &)> const & fn) {
    delete get_print_fn_storage();
    get_print_fn_storage() = new std::function<void(std::ostream &, expr const &)>(fn);
}

inline std::ostream & operator<<(std::ostream & out, expr const & e) {
    if (auto g_print = get_print_fn_storage()) {
        (*g_print)(out, e);
    } else {
        throw exception("print function is not available, Lean was not initialized correctly");
    }
    return out;
}

void initialize_formatter();
void finalize_formatter();
}
