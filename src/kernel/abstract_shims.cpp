/*
C++ shims for kernel_abstract.rs
*/
#include "kernel/abstract.h"
#include "kernel/expr.h"
#include "kernel/replace_fn.h"
#include <lean/lean.h>
#include <algorithm>

using namespace lean;

extern "C" {

lean_object * lean_cxx_expr_abstract_range(lean_object * e, lean_object * n, lean_object * subst) {
    // Mirror logic of lean_expr_abstract_range in abstract.cpp
    static auto core = [](lean_object * e0, size_t sz, lean_object * subst_arr) -> lean_object * {
        expr const & e = reinterpret_cast<expr const &>(e0);
        if (!has_fvar(e) && !has_mvar(e)) {
            lean_inc(e0);
            return e0;
        }
        expr r = replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_fvar(m) && !has_mvar(m))
                return some_expr(m);
            bool fv = is_fvar(m);
            bool mv = is_mvar(m);
            if (fv || mv) {
                size_t i = sz;
                while (i > 0) {
                    --i;
                    lean_object * v = lean_array_get_core(subst_arr, i);
                    if (fv && is_fvar_core(v) && fvar_name_core(v) == fvar_name(m))
                        return some_expr(mk_bvar(offset + sz - i - 1));
                    if (mv && is_mvar_core(v) && mvar_name_core(v) == mvar_name(m))
                        return some_expr(mk_bvar(offset + sz - i - 1));
                }
            }
            return none_expr();
        });
        return r.steal();
    };

    if (!lean_is_scalar(n))
        return core(e, lean_array_size(subst), subst);
    else
        return core(e, std::min(lean_unbox(n), lean_array_size(subst)), subst);
}

lean_object * lean_cxx_expr_abstract(lean_object * e, lean_object * subst) {
    return lean_cxx_expr_abstract_range(e, lean_box(lean_array_size(subst)), subst);
}

} // extern "C"
