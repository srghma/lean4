/*
C++ shims for kernel_level.rs
These are thin wrappers that let Rust call into lean::level C++ logic.
*/
#include "kernel/level.h"
#include "kernel/environment.h"

using namespace lean;

extern "C" {

uint8 lean_cxx_level_eqv(lean_object * l1, lean_object * l2) {
    return is_equivalent(TO_REF(level, l1), TO_REF(level, l2));
}

uint8 lean_cxx_level_eq(lean_object * l1, lean_object * l2) {
    return TO_REF(level, l1) == TO_REF(level, l2);
}

void lean_cxx_initialize_level() {
    initialize_level();
}

void lean_cxx_finalize_level() {
    finalize_level();
}

} // extern "C"
