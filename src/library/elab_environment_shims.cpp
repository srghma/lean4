/*
 * elab_environment_shims.cpp
 *
 * Expose lean_elab_add_decl / lean_elab_add_decl_without_checking /
 * lean_kernel_is_def_eq / lean_kernel_whnf / lean_kernel_check /
 * lean_internal_get_believer_trust_level to Rust via C linkage.
 *
 * Place in: src/library/elab_environment_shims.cpp
 * Add to library CMakeLists target alongside elab_environment.cpp.
 * Remove the six extern "C" LEAN_EXPORT bodies from elab_environment.cpp
 * (or guard with #ifndef LEAN_RUST_RUNTIME).
 */
#include "library/elab_environment.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "runtime/interrupt.h"

extern "C" {

lean_object * lean_cxx_elab_add_decl(lean_object * env, size_t max_heartbeat,
                                     lean_object * decl, lean_object * opt_cancel_tk) {
    lean::scope_max_heartbeat s(max_heartbeat);
    lean::scope_cancel_tk s2(lean::is_scalar(opt_cancel_tk) ? nullptr : lean::cnstr_get(opt_cancel_tk, 0));
    return lean::catch_kernel_exceptions<lean::elab_environment>([&]() {
        return lean::elab_environment(env).add(lean::declaration(decl, true));
    });
}

lean_object * lean_cxx_elab_add_decl_without_checking(lean_object * env,
                                                       lean_object * decl) {
    return lean::catch_kernel_exceptions<lean::elab_environment>([&]() {
        return lean::elab_environment(env).add(lean::declaration(decl, true), false);
    });
}

lean_object * lean_cxx_kernel_is_def_eq(lean_object * obj_env, lean_object * lctx,
                                         lean_object * a, lean_object * b) {
    lean::elab_environment env(obj_env);
    return lean::catch_kernel_exceptions<lean_object *>([&]() {
        return lean::box(lean::type_checker(env.to_kernel_env(), lean::local_ctx(lctx))
                             .is_def_eq(lean::expr(a), lean::expr(b)));
    });
}

lean_object * lean_cxx_kernel_whnf(lean_object * obj_env, lean_object * lctx,
                                    lean_object * a) {
    lean::elab_environment env(obj_env);
    return lean::catch_kernel_exceptions<lean_object *>([&]() {
        return lean::type_checker(env.to_kernel_env(), lean::local_ctx(lctx))
                   .whnf(lean::expr(a)).steal();
    });
}

lean_object * lean_cxx_kernel_check(lean_object * obj_env, lean_object * lctx,
                                     lean_object * a) {
    lean::elab_environment env(obj_env);
    return lean::catch_kernel_exceptions<lean_object *>([&]() {
        return lean::type_checker(env.to_kernel_env(), lean::local_ctx(lctx))
                   .check(lean::expr(a)).steal();
    });
}

uint32_t lean_cxx_internal_get_believer_trust_level(lean_object * /* w */) {
    return LEAN_BELIEVER_TRUST_LEVEL;
}

} // extern "C"
