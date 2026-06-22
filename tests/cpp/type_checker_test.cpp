/*
Copyright (c) 2026 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Antigravity
*/
#include <iostream>
#include <cassert>
#include "initialize/init.h"
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/expr.h"
#include "kernel/level.h"
#include "util/name.h"
#include "runtime/io.h"

using namespace lean;

extern "C" object* lean_mk_empty_environment(uint32_t trust_level, object* w);

environment mk_empty_env() {
    object* r = lean_mk_empty_environment(0, io_mk_world());
    assert(io_result_is_ok(r));
    return environment(io_result_get_value(r));
}

int main() {
    // 1. Initialize Lean environment and runtime
    initializer init;

    // 2. Create an empty environment
    environment env = mk_empty_env();

    // 3. Create a type checker instance with an empty local context
    local_ctx lctx;
    type_checker tc(env, lctx);

    // 4. Perform basic checks on Sorts
    // Type of Prop (Sort 0) is Type 0 (Sort 1)
    expr prop = mk_Prop();
    expr type = mk_Type();
    expr inferred_prop = tc.infer(prop);
    assert(tc.is_def_eq(inferred_prop, type));

    // Type of Type (Sort 1) is Sort 2
    expr type_one = mk_sort(mk_succ(mk_level_one()));
    expr inferred_type = tc.infer(type);
    assert(tc.is_def_eq(inferred_type, type_one));

    // 5. Test lambdas, Pi-types, and beta reduction
    // λ x : Prop, x
    name x_name("x");
    expr identity = mk_lambda(x_name, prop, mk_bvar(0));
    expr identity_type = tc.infer(identity);
    expr expected_identity_type = mk_pi(x_name, prop, prop);
    assert(tc.is_def_eq(identity_type, expected_identity_type));

    // Check definitional equality of beta reduction: (λ x : Prop, x) Prop = Prop
    expr app = mk_app(identity, prop);
    expr reduced = tc.whnf(app);
    assert(tc.is_def_eq(reduced, prop));
    assert(tc.is_def_eq(app, prop)); // type checker is_def_eq should handle beta reduction

    // 6. Test ensure_pi and ensure_sort
    expr pi_val = tc.ensure_pi(expected_identity_type);
    assert(is_pi(pi_val));

    expr sort_val = tc.ensure_sort(type);
    assert(is_sort(sort_val));

    // check that ensure_pi throws on non-pi
    try {
        tc.ensure_pi(prop);
        assert(false && "ensure_pi should throw on non-pi");
    } catch (kernel_exception const &) {
        // Expected exception
    }

    // check that ensure_sort throws on non-sort
    try {
        tc.ensure_sort(identity);
        assert(false && "ensure_sort should throw on non-sort");
    } catch (kernel_exception const &) {
        // Expected exception
    }

    // 7. Test local context and eta expansion
    // Add f : Prop -> Prop to local context
    local_ctx lctx2;
    expr fvar = lctx2.mk_local_decl(name("f_decl"), name("f"), expected_identity_type, mk_binder_info()).mk_ref();
    
    type_checker tc2(env, lctx2);
    expr type_of_fvar = tc2.infer(fvar);
    assert(tc2.is_def_eq(type_of_fvar, expected_identity_type));

    // Test eta expansion of fvar
    expr eta_fvar = tc2.eta_expand(fvar);
    assert(is_lambda(eta_fvar));
    assert(tc2.is_def_eq(binding_domain(eta_fvar), prop));
    assert(is_app(binding_body(eta_fvar)));
    assert(app_fn(binding_body(eta_fvar)) == fvar);
    assert(is_bvar(app_arg(binding_body(eta_fvar)), 0));

    // Check that type checker handles eta equivalence: f = λ y : Prop, f y
    assert(tc2.is_def_eq(fvar, eta_fvar));

    // 8. Test exceptions for unknown free variables
    try {
        expr bad_fvar = mk_fvar(name("not_in_lctx"));
        tc.infer(bad_fvar);
        assert(false && "infer should throw on unknown fvar");
    } catch (kernel_exception const &) {
        // Expected exception
    }

    std::cout << "All C++ type_checker tests passed successfully!" << std::endl;
    return 0;
}
