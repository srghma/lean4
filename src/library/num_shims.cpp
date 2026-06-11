/*
 * num_shims.cpp
 *
 * Expose initialize_num / finalize_num to Rust.
 * Both are no-ops in the original; the shims exist so Rust can call through
 * without embedding C++ headers.
 *
 * Place in: src/library/num_shims.cpp
 * Add to library CMakeLists target alongside num.cpp.
 * Remove initialize_num / finalize_num bodies from num.cpp
 * (or guard with #ifndef LEAN_RUST_RUNTIME).
 */
#include "library/num.h"

extern "C" {

void lean_cxx_initialize_num() {
    lean::initialize_num();
}

void lean_cxx_finalize_num() {
    lean::finalize_num();
}

} // extern "C"
