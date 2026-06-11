/*
 * formatter_shims.cpp
 *
 * Expose initialize/finalize_formatter to Rust.
 *
 * Place in: src/library/formatter_shims.cpp
 * Add to the library CMakeLists target.
 */
#include "library/formatter.h"

extern "C" {

void lean_cxx_initialize_formatter() {
    lean::initialize_formatter();
}

void lean_cxx_finalize_formatter() {
    lean::finalize_formatter();
}

} // extern "C"
