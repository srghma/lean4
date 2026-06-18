/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

C++ shim for trace functions that cannot be ported to Rust:
- tout::~tout(): uses sstream (C++ type)
- operator<<(ostream&, tclass): uses ostream (C++ type)

register_trace_class is now implemented in Rust (kernel_trace.rs).
*/
#include "kernel/trace.h"

namespace lean {

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
