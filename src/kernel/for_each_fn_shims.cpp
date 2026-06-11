/*
C++ shims for kernel_for_each_fn.rs
*/
#include "kernel/expr.h"
#include "kernel/for_each_fn.h"

using namespace lean;

extern "C" {

lean_object * lean_cxx_find_expr(lean_object * p, lean_object * e_) {
    lean_object * found = nullptr;
    expr const & e = TO_REF(expr, e_);
    for_each(e, [&](expr const & e, unsigned) {
        if (found != nullptr) return false;
        lean_inc(p);
        lean_inc(e.raw());
        if (lean_unbox(lean_apply_1(p, e.raw()))) {
            found = e.raw();
            return false;
        }
        return true;
    });
    if (found) {
        lean_inc(found);
        lean_object * r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, found);
        return r;
    } else {
        return lean_box(0);
    }
}

lean_object * lean_cxx_find_ext_expr(lean_object * p, lean_object * e_) {
    lean_object * found = nullptr;
    expr const & e = TO_REF(expr, e_);
    for_each(e, [&](expr const & e, unsigned) {
        if (found != nullptr) return false;
        lean_inc(p);
        lean_inc(e.raw());
        switch (lean_unbox(lean_apply_1(p, e.raw()))) {
        case 0: // found
            found = e.raw();
            return false;
        case 1: // visit
            return true;
        case 2: // done
            return false;
        default:
            lean_unreachable();
        }
    });
    if (found) {
        lean_inc(found);
        lean_object * r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, found);
        return r;
    } else {
        return lean_box(0);
    }
}

} // extern "C"
