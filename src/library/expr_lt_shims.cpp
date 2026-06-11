/*
 * expr_lt_shims.cpp
 *
 * Expose lean_expr_quick_lt / lean_expr_lt to Rust via C linkage.
 * The Rust port owns the `#[no_mangle] extern "C"` symbols; these shims
 * add a `_cxx` suffix so Rust can call through to the C++ implementations.
 *
 * Place in: src/library/expr_lt_shims.cpp
 * Add to the library CMakeLists target.
 * Remove `lean_expr_quick_lt` / `lean_expr_lt` bodies from expr_lt.cpp
 * (or guard them with #ifndef LEAN_RUST_RUNTIME).
 */
#include "library/expr_lt.h"

extern "C" {

uint8_t lean_cxx_expr_quick_lt(lean_object * a, lean_object * b) {
    return lean::is_lt(lean::expr(a, true), lean::expr(b, true), true, nullptr);
}

uint8_t lean_cxx_expr_lt(lean_object * a, lean_object * b) {
    return lean::is_lt(lean::expr(a, true), lean::expr(b, true), false, nullptr);
}

} // extern "C"
