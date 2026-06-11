/*
C++ shims for kernel_instantiate.rs
*/
#include "kernel/instantiate.h"
#include "kernel/expr.h"
#include <lean/lean.h>

using namespace lean;

extern "C" {

lean_object * lean_expr_instantiate(lean_object * a, lean_object * subst);
lean_object * lean_expr_instantiate_range(lean_object * a, lean_object * begin,
                                          lean_object * end, lean_object * subst);
lean_object * lean_expr_instantiate_rev(lean_object * a, lean_object * subst);
lean_object * lean_expr_instantiate_rev_range(lean_object * a, lean_object * begin,
                                              lean_object * end, lean_object * subst);

lean_object * lean_cxx_expr_instantiate1(lean_object * a0, lean_object * e0) {
    expr const & a = reinterpret_cast<expr const &>(a0);
    if (!has_loose_bvars(a)) {
        lean_inc(a0);
        return a0;
    }
    expr const & e = reinterpret_cast<expr const &>(e0);
    expr r = instantiate(a, 1, &e);
    return r.steal();
}

lean_object * lean_cxx_expr_instantiate(lean_object * a, lean_object * subst) {
    return ::lean_expr_instantiate(a, subst);
}

lean_object * lean_cxx_expr_instantiate_range(lean_object * a, lean_object * begin,
                                               lean_object * end, lean_object * subst) {
    return ::lean_expr_instantiate_range(a, begin, end, subst);
}

lean_object * lean_cxx_expr_instantiate_rev(lean_object * a, lean_object * subst) {
    return ::lean_expr_instantiate_rev(a, subst);
}

lean_object * lean_cxx_expr_instantiate_rev_range(lean_object * a, lean_object * begin,
                                                   lean_object * end, lean_object * subst) {
    return ::lean_expr_instantiate_rev_range(a, begin, end, subst);
}

} // extern "C"
