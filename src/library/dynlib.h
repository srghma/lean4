/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Mac Malone
*/
#pragma once
#include <string>
#include "util/io.h"

namespace lean {
LEAN_EXPORT void initialize_dynlib();
extern "C" obj_res lean_load_dynlib(obj_arg path);
extern "C" obj_res lean_load_plugin(obj_arg path, obj_arg init_fn);
inline void load_dynlib(std::string path) {
    consume_io_result(lean_load_dynlib(mk_string(path)));
}
inline void load_plugin(std::string path) {
    consume_io_result(lean_load_plugin(mk_string(path), box(0)));
}
}
