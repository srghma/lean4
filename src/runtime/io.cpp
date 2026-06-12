/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#include "runtime/io.h"
#include "runtime/object.h"

namespace lean {

obj_res io_result_mk_error(char const * msg) {
    return io_result_mk_error(lean_mk_io_user_error(mk_string(msg)));
}

obj_res io_result_mk_error(std::string const & msg) {
    return io_result_mk_error(lean_mk_io_user_error(mk_string(msg)));
}

// =======================================
// ST ref primitives


}
