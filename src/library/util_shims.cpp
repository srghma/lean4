/*
 * util_shims.cpp
 *
 * Expose initialize_library_util / finalize_library_util (and the sub-pair
 * initialize_bool / finalize_bool) to Rust via C linkage.
 *
 * Place in: src/library/util_shims.cpp
 * Add to library CMakeLists target alongside util.cpp.
 * Remove initialize_library_util / finalize_library_util /
 *        initialize_bool / finalize_bool
 * bodies from util.cpp (or guard with #ifndef LEAN_RUST_RUNTIME).
 */
#include "library/util.h"

namespace lean {
void initialize_bool();
void finalize_bool();
}

extern "C" {

void lean_cxx_initialize_library_util() {
    lean::initialize_library_util();
}

void lean_cxx_finalize_library_util() {
    lean::finalize_library_util();
}

void lean_cxx_initialize_bool() {
    lean::initialize_bool();
}

void lean_cxx_finalize_bool() {
    lean::finalize_bool();
}

} // extern "C"
