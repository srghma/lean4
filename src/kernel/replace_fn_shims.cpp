/*
C++ shims for kernel_replace_fn.rs
*/
#include "kernel/expr.h"
#include "kernel/replace_fn.h"
#include "runtime/object.h"

using namespace lean;

extern "C" {

lean_object * lean_cxx_replace_expr(lean_object * f, lean_object * e) {
    expr const & ee = TO_REF(expr, e);
    expr r = replace(ee, [=](expr const & s, unsigned) -> optional<expr> {
        lean_inc(f);
        lean_inc(s.raw());
        lean_object * r = lean_apply_1(f, s.raw());
        if (!lean_is_scalar(r)) {
            expr e_new(lean_ctor_get(r, 0), true);
            lean_dec_ref(r);
            return optional<expr>(e_new);
        }
        lean_dec_ref(r);
        return optional<expr>();
    });
    return r.steal();
}

} // extern "C"
