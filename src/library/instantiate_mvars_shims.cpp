/*
 * instantiate_mvars_shims.cpp
 *
 * Expose lean_instantiate_level_mvars / lean_instantiate_expr_mvars to Rust.
 *
 * Place in: src/library/instantiate_mvars_shims.cpp
 * Add to library CMakeLists target alongside instantiate_mvars.cpp.
 * Remove lean_instantiate_level_mvars / lean_instantiate_expr_mvars bodies
 * from instantiate_mvars.cpp (or guard with #ifndef LEAN_RUST_RUNTIME).
 */
#include "kernel/expr.h"
#include "runtime/object.h"

/* Forward declarations of the implementations in instantiate_mvars.cpp. */
extern "C" lean_object * lean_instantiate_level_mvars_impl(lean_object * m, lean_object * l);
extern "C" lean_object * lean_instantiate_expr_mvars_impl(lean_object * m, lean_object * e);

extern "C" {

lean_object * lean_cxx_instantiate_level_mvars(lean_object * m, lean_object * l) {
    return lean_instantiate_level_mvars_impl(m, l);
}

lean_object * lean_cxx_instantiate_expr_mvars(lean_object * m, lean_object * e) {
    return lean_instantiate_expr_mvars_impl(m, e);
}

} // extern "C"
