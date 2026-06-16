/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

C++ shim for trace functions that cannot be ported to Rust:
- register_trace_class: throws C++ exceptions via register_option
- tout::~tout(): uses sstream (C++ type)
- operator<<(ostream&, tclass): uses ostream (C++ type)

All other trace functions are implemented in Rust (kernel_trace.rs).
*/
#include <string>
#include "util/io.h"
#include "util/option_declarations.h"
#include "kernel/trace.h"

namespace lean {

void register_trace_class(name const & n, name const & decl_name) {
    register_option(name("trace") + n, decl_name, data_value_kind::Bool, "false",
                    "(trace) enable/disable tracing for the given module and submodules");
}

extern "C" obj_res lean_io_eprint(obj_arg s);
static void io_eprint(obj_arg s) {
    object * r = lean_io_eprint(s);
    if (!lean_io_result_is_ok(r))
        lean_io_result_show_error(r);
    lean_dec(r);
}

tout::~tout() {
    io_eprint(mk_string(m_out.str()));
}

std::ostream & operator<<(std::ostream & ios, tclass const & c) {
    ios << "[" << c.m_cls << "] ";
    return ios;
}

}
