/*
C++ shims for kernel batch 3:
  kernel_quot.rs, kernel_type_checker.rs, kernel_inductive.rs,
  kernel_expr.rs, kernel_trace.rs
*/
#include "kernel/quot.h"
#include "kernel/type_checker.h"
#include "kernel/inductive.h"
#include "kernel/expr.h"
#include "kernel/replace_fn.h"
#include <lean/lean.h>

using namespace lean;

extern "C" {

// ---------------------------------------------------------------------------
// quot
// ---------------------------------------------------------------------------

void lean_cxx_initialize_quot() { initialize_quot(); }
void lean_cxx_finalize_quot()   { finalize_quot(); }

// ---------------------------------------------------------------------------
// type_checker
// ---------------------------------------------------------------------------

void lean_cxx_initialize_type_checker() { initialize_type_checker(); }
void lean_cxx_finalize_type_checker()   { finalize_type_checker(); }

// ---------------------------------------------------------------------------
// inductive
// ---------------------------------------------------------------------------

void lean_cxx_initialize_inductive() { initialize_inductive(); }
void lean_cxx_finalize_inductive()   { finalize_inductive(); }

// ---------------------------------------------------------------------------
// expr — lean_expr_has_loose_bvar
// The Rust port of lean_expr_mk_data / lean_expr_mk_app_data is pure arithmetic
// and doesn't need a shim.  has_loose_bvar calls for_each which needs C++.
// ---------------------------------------------------------------------------

uint8 lean_cxx_expr_has_loose_bvar(lean_object * e, lean_object * i) {
    if (!lean_is_scalar(i)) return false;
    return has_loose_bvar(TO_REF(expr, e), lean_unbox(i));
}

lean_object * lean_cxx_expr_lower_loose_bvars(lean_object * e, lean_object * s, lean_object * d) {
    if (!lean_is_scalar(s) || !lean_is_scalar(d) || lean_unbox(s) < lean_unbox(d)) {
        lean_inc(e);
        return e;
    }
    return lower_loose_bvars(TO_REF(expr, e), lean_unbox(s), lean_unbox(d)).steal();
}

lean_object * lean_cxx_expr_lift_loose_bvars(lean_object * e, lean_object * s, lean_object * d) {
    if (!lean_is_scalar(s) || !lean_is_scalar(d)) {
        lean_inc(e);
        return e;
    }
    return lift_loose_bvars(TO_REF(expr, e), lean_unbox(s), lean_unbox(d)).steal();
}

} // extern "C"
