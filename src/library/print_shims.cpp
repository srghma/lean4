/*
 * print_shims.cpp
 *
 * Expose initialize_print / finalize_print / lean_expr_dbg_to_string to Rust.
 *
 * Place in: src/library/print_shims.cpp
 * Add to library CMakeLists target alongside print.cpp.
 * Remove initialize_print / finalize_print / lean_expr_dbg_to_string bodies
 * from print.cpp (or guard with #ifndef LEAN_RUST_RUNTIME).
 */
#include "library/print.h"
#include "kernel/expr.h"
#include "runtime/object.h"
#include <sstream>

extern "C" {

void lean_cxx_initialize_print() {
    lean::initialize_print();
}

void lean_cxx_finalize_print() {
    lean::finalize_print();
}

lean_object * lean_cxx_expr_dbg_to_string(lean_object * e) {
    std::ostringstream out;
    out << lean::expr(e, true);
    return lean::mk_string(out.str());
}

} // extern "C"
