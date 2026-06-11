/*
 * annotation_shims.cpp
 *
 * Expose initialize/finalize_annotation to Rust.
 * The full annotation logic (register_annotation, mk_annotation, etc.) stays
 * in annotation.cpp and is called directly from Lean-generated C code via the
 * existing lean_object ABI — no Rust involvement needed.
 *
 * Place in: src/library/annotation_shims.cpp
 * Add to the library CMakeLists target.
 */
#include "library/annotation.h"

extern "C" {

void lean_cxx_initialize_annotation() {
    lean::initialize_annotation();
}

void lean_cxx_finalize_annotation() {
    lean::finalize_annotation();
}

} // extern "C"
