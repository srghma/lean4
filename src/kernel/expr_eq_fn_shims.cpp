/*
C++ shims for kernel_expr_eq_fn.rs
*/
#include "kernel/expr.h"
#include "kernel/expr_eq_fn.h"

using namespace lean;

extern "C" {

uint8 lean_cxx_expr_eqv(lean_object * a, lean_object * b) {
    return is_equal(TO_REF(expr, a), TO_REF(expr, b));
}

uint8 lean_cxx_expr_equal(lean_object * a, lean_object * b) {
    return is_bi_equal(TO_REF(expr, a), TO_REF(expr, b));
}

} // extern "C"
