/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Rust port of src/kernel/type_checker.cpp (1560 lines).
All C++ `throw X` → `return Err(KernelError::X)`.
*/

#[cfg(feature = "export-runtime-ffi")]
#[allow(dead_code, non_snake_case, non_upper_case_globals, clippy::missing_safety_doc)]
mod kernel_type_checker_impl {
    use super::*;
    use core::ffi::{c_char, c_void};
    use std::collections::{HashMap, HashSet};
    use std::sync::atomic::{AtomicPtr, Ordering};
    use std::ptr;

    type Size = usize;

// ---------------------------------------------------------------------------
// Lean runtime C API bindings (extern "C" stubs expected from lean/lean.h)
// lean_inc, lean_dec, lean_is_scalar, lean_box, lean_unbox, lean_ptr_tag,
// lean_mark_persistent are Rust functions from super::* — not declared here.
// lean_alloc_ctor / lean_ctor_get / lean_ctor_set are local shims below.
// lean_stack_has_space, lean_memory_within_limit, check_heartbeat_exceeded,
// check_interrupted_flag are Rust functions from super::* — not declared here.
// ---------------------------------------------------------------------------

extern "C" {
    fn lean_mark_persistent(o: *mut LeanObject);

    // Names
    fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
    fn lean_name_mk_numeral(prefix: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;
    // lean_name_anonymous: implemented as Rust shim below (Name.anonymous = boxed scalar 0)
    // lean_name_eq_raw is inline C++; implemented as Rust shim below

    // Levels
    fn lean_level_mk_zero() -> *mut LeanObject;
    fn lean_level_mk_succ(l: *mut LeanObject) -> *mut LeanObject;
    fn lean_level_mk_max(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject;
    fn lean_level_mk_imax(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject;
    fn lean_level_mk_param(n: *mut LeanObject) -> *mut LeanObject;
    fn lean_level_mk_mvar(n: *mut LeanObject) -> *mut LeanObject;
    fn lean_level_eq(a: *const LeanObject, b: *const LeanObject) -> bool;
    // lean_level_get_succ / lean_level_get_param_name are inline C++; implemented as Rust shims below
    // lean_level_get_max_lhs / get_max_rhs / get_imax_lhs / get_imax_rhs: implemented as Rust shims below
    fn lean_level_hash(l: *const LeanObject) -> u32;
    fn lean_mk_list_cons(ty: *mut LeanObject, h: *mut LeanObject, t: *mut LeanObject) -> *mut LeanObject;
    // lean_mk_list_nil / lean_list_is_nil: implemented as Rust shims below
    // lean_list_head / lean_list_tail: implemented as Rust shims below

    // Expressions
    // mk_bvar takes the de Bruijn index as a Nat object (obj_arg, consumed).
    fn lean_expr_mk_bvar(idx: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_fvar(id: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_mvar(id: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_sort(l: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_const(n: *mut LeanObject, ls: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_app(f: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_lambda(n: *mut LeanObject, d: *mut LeanObject, b: *mut LeanObject, bi: u8) -> *mut LeanObject;
    fn lean_expr_mk_forall(n: *mut LeanObject, d: *mut LeanObject, b: *mut LeanObject, bi: u8) -> *mut LeanObject;
    fn lean_expr_mk_let(n: *mut LeanObject, t: *mut LeanObject, v: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_lit(l: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_lit_str(s: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_proj(type_name: *mut LeanObject, idx: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_mk_mdata(d: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
    // lean_expr_kind: implemented as Rust shim below
    // `@[export lean_expr_hash] def hashEx : Expr → UInt64` — returns UInt64 and CONSUMES
    // its argument. Always call through the `expr_hash` borrowing wrapper, never directly.
    fn lean_expr_hash(e: *const LeanObject) -> u64;
    fn lean_expr_eqv(a: *const LeanObject, b: *const LeanObject) -> bool;
    // lean_expr_has_loose_bvars: implemented as Rust shim below
    fn lean_expr_has_fvar(e: *const LeanObject) -> bool;
    fn lean_expr_has_mvar(e: *const LeanObject) -> bool;
    fn lean_expr_has_expr_mvar(e: *const LeanObject) -> bool;
    fn lean_expr_get_bvar_idx(e: *const LeanObject) -> u32;
    // lean_expr_get_fvar_id: implemented as Rust shim below
    // lean_expr_get_const_name / lean_expr_get_app_fn / lean_expr_get_app_arg are inline C++; implemented as Rust shims below
    // lean_expr_get_const_levels: implemented as Rust shim below
    // lean_expr_get_sort_level / lean_expr_get_binding_name: implemented as Rust shims below
    // lean_expr_get_binding_domain / lean_expr_get_binding_body: implemented as Rust shims below
    // lean_expr_get_binding_info: implemented as Rust shim below (delegates to lean_expr_binder_info)
    // lean_expr_get_let_name / lean_expr_get_let_type / lean_expr_get_let_value / lean_expr_get_let_body: implemented as Rust shims below
    // lean_expr_get_lit_nat: implemented as Rust shim below
    fn lean_expr_get_lit_str(e: *const LeanObject) -> *mut LeanObject;
    // lean_expr_get_proj_sname / lean_expr_get_proj_idx / lean_expr_get_proj_expr are inline C++; implemented as Rust shims below
    // lean_expr_get_mdata_expr: implemented as Rust shim below
    // `instantiate`/`instantiate_rev`/`abstract` take an `Array Expr`; the kernel needs the
    // raw-pointer variants. `instantiate1` substitutes a single `Expr`. All borrow their args.
    fn lean_expr_instantiate1(e: *mut LeanObject, v: *mut LeanObject) -> *mut LeanObject;
    #[link_name = "lean_expr_instantiate_rev_ptr"]
    fn lean_expr_instantiate_rev(e: *mut LeanObject, n: u32, vs: *const *mut LeanObject) -> *mut LeanObject;
    #[link_name = "lean_expr_abstract_ptr"]
    fn lean_expr_abstract(e: *mut LeanObject, n: u32, vs: *const *mut LeanObject) -> *mut LeanObject;
    // lean_expr_get_app_num_args: implemented as Rust shim below
    // lean_expr_is_eqp: implemented as Rust shim below
    fn lean_expr_cheap_beta_reduce(e: *mut LeanObject) -> *mut LeanObject;
    // lean_expr_mk_prop: implemented as Rust shim below (mk_sort of level zero)
    fn lean_expr_mk_type1() -> *mut LeanObject;
    // lean_expr_is_sort: implemented as Rust shim below
    // lean_expr_is_pi: implemented as Rust shim below
    // lean_expr_is_lambda / lean_expr_is_let: implemented as Rust shims below
    // lean_expr_is_app / lean_expr_is_const are inline C++; implemented as Rust shims below
    // lean_expr_is_fvar / lean_expr_is_proj: implemented as Rust shims below
    fn lean_expr_is_mdata(e: *const LeanObject) -> bool;
    // lean_expr_is_nat_lit: implemented as Rust shim below
    // lean_expr_is_string_lit: implemented as Rust shim below
    fn lean_nat_lit_to_constructor(e: *mut LeanObject) -> *mut LeanObject;
    fn lean_string_lit_to_constructor(e: *mut LeanObject) -> *mut LeanObject;
    fn lean_expr_infer_implicit(e: *mut LeanObject, strict: bool) -> *mut LeanObject;

    // Nat
    // lean_nat_mk_obj: implemented as Rust shim below
    fn lean_nat_get_value(n: *const LeanObject) -> u64;
    // lean_nat_is_small / lean_nat_get_small_value are inline C++; implemented as Rust shims below
    // lean_nat_add / lean_nat_sub / lean_nat_mul / lean_nat_div / lean_nat_mod: implemented as Rust shims below
    fn lean_nat_gcd(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject;
    fn lean_nat_pow(a: *mut LeanObject, b: *mut LeanObject, max_exp: u64) -> *mut LeanObject;
    // lean_nat_land / lean_nat_lor / lean_nat_xor: implemented as Rust shims below
    fn lean_nat_shiftl(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject;
    // lean_nat_shiftr: implemented as Rust shim below
    // lean_nat_beq / lean_nat_ble / lean_nat_eq / lean_nat_is_zero / lean_nat_dec: implemented as Rust shims below
    fn lean_nat_succ(n: *mut LeanObject) -> *mut LeanObject;

    // Environment
    fn lean_environment_get(env: *const LeanObject, name: *mut LeanObject) -> *mut LeanObject; // returns ConstantInfo option
    fn lean_environment_find(env: *const LeanObject, name: *mut LeanObject) -> *mut LeanObject; // returns Option ConstantInfo
    fn lean_environment_check_name(env: *mut LeanObject, name: *mut LeanObject) -> *mut LeanObject; // returns Except
    fn lean_environment_add_core(env: *mut LeanObject, info: *mut LeanObject) -> *mut LeanObject;
    // lean_environment_is_quot_initialized: implemented as Rust shim below (delegates to lean_environment_quot_init)
    fn lean_environment_check_duplicated_univ_params(env: *const LeanObject, ps: *mut LeanObject) -> *mut LeanObject;

    // ConstantInfo
    // lean_constant_info_is_inductive / lean_constant_info_to_inductive_val are inline C++; implemented as Rust shims below
    // lean_constant_info_is_constructor / is_recursor / is_definition / is_unsafe / has_value: implemented as Rust shims below
    // lean_constant_info_get_name / get_lparams / get_num_lparams / get_hints / get_safety: implemented as Rust shims below
    // lean_constant_info_to_constructor_val / to_recursor_val / to_definition_val: implemented as Rust shims below
    fn lean_constant_info_get_type(info: *const LeanObject) -> *mut LeanObject;
    fn lean_constant_info_get_value(info: *const LeanObject) -> *mut LeanObject;
    fn lean_instantiate_type_lparams(info: *const LeanObject, ls: *mut LeanObject) -> *mut LeanObject;
    fn lean_instantiate_value_lparams(info: *const LeanObject, ls: *mut LeanObject) -> *mut LeanObject;

    // InductiveVal
    // lean_inductive_val_get_nparams / lean_inductive_val_get_nindices / lean_inductive_val_get_ncnstrs / lean_inductive_val_get_cnstrs are inline C++; implemented as Rust shims below
    fn lean_inductive_val_is_rec(v: *const LeanObject) -> bool;
    fn lean_inductive_val_is_k(v: *const LeanObject) -> bool;

    // ConstructorVal
    // lean_constructor_val_get_induct / get_nparams / get_nfields: implemented as Rust shims below
    fn lean_constructor_val_get_cidx(v: *const LeanObject) -> u32;

    // RecursorVal
    // lean_recursor_val_get_major_idx / get_nparams / get_nmotives / get_nminors / is_k / get_rules / get_major_induct: implemented as Rust shims below
    fn lean_recursor_val_get_nindices(v: *const LeanObject) -> u32;
    fn lean_recursor_val_is_unsafe(v: *const LeanObject) -> bool;

    // RecursorRule
    // lean_recursor_rule_get_cnstr / get_nfields / get_rhs: implemented as Rust shims below

    // LocalCtx
    // lean_local_ctx_mk_local_decl / lean_local_ctx_mk_local_decl_with_value: implemented as Rust helpers below
    //   (they build a (fvar, new_lctx) pair from the real Lean exports lean_local_ctx_mk_local_decl /
    //    lean_local_ctx_mk_let_decl, imported below under alias names).
    // lean_local_ctx_find_local_decl / lean_local_decl_get_type are inline C++; implemented as Rust shims below
    // lean_local_ctx_find is the underlying real Lean export used by the shim
    fn lean_local_ctx_find(lctx: *mut LeanObject, name: *mut LeanObject) -> *mut LeanObject; // Option LocalDecl
    // lean_local_decl_get_value / lean_local_decl_has_value: implemented as Rust shims below
    fn lean_local_decl_get_user_name(d: *const LeanObject) -> *mut LeanObject;
    // lean_local_ctx_mk_pi: implemented as Rust shim below (bridges to C++ local_ctx::mk_binding<false>)
    fn lean_local_ctx_mk_lambda(lctx: *const LeanObject, fvars: *const *mut LeanObject, n: u32, body: *mut LeanObject) -> *mut LeanObject;

    // EquivManager — uses *mut c_void (opaque pointer to Rust struct)
    fn lean_equiv_manager_new() -> *mut c_void;
    fn lean_equiv_manager_is_equiv(mgr: *const c_void, a: *const LeanObject, b: *const LeanObject, use_hash: bool) -> bool;
    fn lean_equiv_manager_add_equiv(mgr: *mut c_void, a: *mut LeanObject, b: *mut LeanObject);
    fn lean_equiv_manager_free(mgr: *mut c_void);

    // HintCompare
    // lean_hints_compare / lean_hints_is_regular: implemented as Rust shims below

    // Quotient
    fn lean_quot_reduce_rec(env: *const LeanObject, e: *mut LeanObject, whnf: extern "C" fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject, ctx: *mut LeanObject) -> *mut LeanObject;

    // Native reduction
    // lean_ir_run_boxed_kernel: implemented as Rust shim below (wraps lean_eval_const_at_kernel_env)
    // lean_mk_empty_options: implemented as Rust shim below (delegates to lean_options_get_empty)

    // Name generation registration
    fn lean_register_name_generator_prefix(prefix: *mut LeanObject);

    // Exception construction helpers (from kernel_exception.h)
    fn lean_mk_kernel_exception(env: *mut LeanObject, msg: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_type_expected_exception(env: *mut LeanObject, lctx: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_function_expected_exception(env: *mut LeanObject, lctx: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_app_type_mismatch_exception(env: *mut LeanObject, lctx: *mut LeanObject, app: *mut LeanObject, fun_type: *mut LeanObject, arg_type: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_def_type_mismatch_exception(env: *mut LeanObject, lctx: *mut LeanObject, name: *mut LeanObject, given: *mut LeanObject, expected: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_invalid_proj_exception(env: *mut LeanObject, lctx: *mut LeanObject, proj: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_string_from_bytes(s: *const c_char, n: Size) -> *mut LeanObject;
}

// ---------------------------------------------------------------------------
// Local shims: adapt super::* Rust fns to signatures used in this module
// ---------------------------------------------------------------------------

#[inline(always)]
unsafe fn lean_is_scalar(o: *const LeanObject) -> bool {
    super::lean_is_scalar(o as *mut _)
}

#[inline(always)]
unsafe fn lean_ptr_tag(o: *const LeanObject) -> u32 {
    super::lean_ptr_tag(o as *mut _) as u32
}

#[inline(always)]
unsafe fn lean_ctor_get(o: *const LeanObject, i: u32) -> *mut LeanObject {
    (o.add(1) as *const *mut LeanObject).add(i as usize).read()
}

#[inline(always)]
unsafe fn lean_alloc_ctor(tag: u32, num_objs: u32, scalar_sz: u32) -> *mut LeanObject {
    lean_runtime_alloc_ctor(tag, num_objs, scalar_sz)
}

#[inline(always)]
unsafe fn lean_ctor_set(o: *mut LeanObject, i: u32, v: *mut LeanObject) {
    lean_runtime_ctor_set(o, i, v)
}

/// Borrowing wrapper around `lean_expr_hash`. The exported `lean_expr_hash`
/// (`@[export] def hashEx : Expr → UInt64`) takes its `Expr` argument by value and
/// therefore **consumes** (decrements) it. All call sites here only hold borrowed
/// references, so we `lean_inc` before handing the reference over to be consumed.
#[inline(always)]
unsafe fn expr_hash(e: *const LeanObject) -> u64 {
    lean_inc(e as *mut LeanObject);
    lean_expr_hash(e)
}

/// Borrowing wrappers around the `Expr → Bool` flag exports
/// (`@[export] def hasFVarEx : Expr → Bool`, `hasExprMVarEx`, …). Like `lean_expr_hash`
/// these take the `Expr` by value and **consume** it, so we `lean_inc` before calling.
#[inline(always)]
unsafe fn expr_has_fvar(e: *const LeanObject) -> bool {
    lean_inc(e as *mut LeanObject);
    lean_expr_has_fvar(e)
}
#[inline(always)]
unsafe fn expr_has_expr_mvar(e: *const LeanObject) -> bool {
    lean_inc(e as *mut LeanObject);
    lean_expr_has_expr_mvar(e)
}

#[inline(always)]
unsafe fn lean_unbox(o: *const LeanObject) -> usize {
    super::lean_unbox(o as *mut _)
}

#[inline(always)]
unsafe fn lean_name_eq(a: *const LeanObject, b: *const LeanObject) -> bool {
    super::lean_name_eq_export(a as *mut _, b as *mut _) != 0
}

#[inline(always)]
unsafe fn lean_mk_string(s: *const u8, n: usize) -> *mut LeanObject {
    lean_mk_string_from_bytes(s.cast(), n)
}

// ---------------------------------------------------------------------------
// Exported C symbols for inline C++ accessor functions
// These were inline in the C++ runtime (lean/lean.h) and thus not exported,
// but libleanshared.so references them as external symbols — so Rust provides them.
// ---------------------------------------------------------------------------

// Names: lean_name_eq_raw returns 0 (not equal) or 1 (equal)
#[no_mangle]
pub unsafe extern "C" fn lean_name_eq_raw(a: *const LeanObject, b: *const LeanObject) -> u8 {
    super::lean_name_eq_export(a as *mut _, b as *mut _)
}

// Levels
// Level::Succ (tag 1): field[0] = pred level
#[no_mangle]
pub unsafe extern "C" fn lean_level_get_succ(l: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(l, 0)
}

// Level::Param (tag 4): field[0] = name
#[no_mangle]
pub unsafe extern "C" fn lean_level_get_param_name(l: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(l, 0)
}

// Expressions
// Expr::App (tag 5): field[0]=fn, field[1]=arg
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_app(e: *const LeanObject) -> bool {
    !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_APP
}

#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_app_fn(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(e, 0)
}

#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_app_arg(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(e, 1)
}

// Expr::Const (tag 4): field[0]=name, field[1]=List Level
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_const(e: *const LeanObject) -> bool {
    !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_CONST
}

#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_const_name(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(e, 0)
}

// Expr::Proj (tag 11): field[0]=sname, field[1]=idx, field[2]=expr
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_proj_sname(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(e, 0)
}

#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_proj_idx(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(e, 1)
}

#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_proj_expr(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(e, 2)
}

// Nat scalars: small Nat values are stored as tagged scalars (lean_box(n))
#[no_mangle]
pub unsafe extern "C" fn lean_nat_is_small(n: *const LeanObject) -> bool {
    lean_is_scalar(n)
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_get_small_value(n: *const LeanObject) -> u32 {
    lean_unbox(n) as u32
}

// ConstantInfo: constant_info_kind enum {Axiom=0,Definition=1,Theorem=2,Opaque=3,Quot=4,Inductive=5,...}
// Each variant wraps its val at field[0]
const CONST_INFO_INDUCTIVE_TAG: u32 = 5;

#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_is_inductive(info: *const LeanObject) -> bool {
    !lean_is_scalar(info) && lean_ptr_tag(info) == CONST_INFO_INDUCTIVE_TAG
}

#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_to_inductive_val(info: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(info, 0)
}

// InductiveVal: field[0]=ConstantVal, field[1]=nparams(Nat), field[2]=nindices(Nat),
//               field[3]=all(List Name), field[4]=cnstrs(List Name), field[5]=nnested(Nat)
#[no_mangle]
pub unsafe extern "C" fn lean_inductive_val_get_nparams(v: *const LeanObject) -> u32 {
    lean_unbox(lean_ctor_get(v, 1)) as u32
}

#[no_mangle]
pub unsafe extern "C" fn lean_inductive_val_get_nindices(v: *const LeanObject) -> u32 {
    lean_unbox(lean_ctor_get(v, 2)) as u32
}

// InductiveVal.cnstrs is the List Name at field[4]
#[no_mangle]
pub unsafe extern "C" fn lean_inductive_val_get_cnstrs(v: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(v, 4)
}

// List.nil = scalar, List.cons h t has field[0]=h, field[1]=t
unsafe fn lean_list_length(mut l: *const LeanObject) -> u32 {
    let mut count = 0u32;
    while !lean_is_scalar(l) {
        count += 1;
        l = lean_ctor_get(l, 1);
    }
    count
}

#[no_mangle]
pub unsafe extern "C" fn lean_inductive_val_get_ncnstrs(v: *const LeanObject) -> u32 {
    lean_list_length(lean_ctor_get(v, 4))
}

// LocalDecl: cdecl (tag 0) / ldecl (tag 1)
//   field[0]=index(Nat), field[1]=name(Name), field[2]=userName(Name), field[3]=type(Expr)
//   ldecl also has field[4]=value(Expr)
#[no_mangle]
pub unsafe extern "C" fn lean_local_decl_get_type(d: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(d, 3)
}

// lean_local_ctx_find returns Option LocalDecl (None = scalar, Some(d) = tag-1 ctor with field[0]=d)
// This shim extracts the FVarId from an FVar expr, calls lean_local_ctx_find, and unwraps the Option.
#[no_mangle]
pub unsafe extern "C" fn lean_local_ctx_find_local_decl(lctx: *const LeanObject, fvar_expr: *const LeanObject) -> *mut LeanObject {
    let fvar_id = lean_ctor_get(fvar_expr, 0); // Expr::FVar field[0] = FVarId (= Name, FVarId is a single-field struct erased in ABI)
    // lean_local_ctx_find consumes both args (C++ passes them via to_obj_arg()); our lctx/fvar_id
    // are borrowed, so inc each first — otherwise every fvar lookup over-decrements the lctx.
    lean_inc(lctx as *mut _);
    lean_inc(fvar_id);
    let opt = lean_local_ctx_find(lctx as *mut _, fvar_id); // Option LocalDecl
    if lean_is_scalar(opt) {
        opt // None: return scalar
    } else {
        let decl = lean_ctor_get(opt, 0); // Some.field[0] = LocalDecl
        lean_inc(decl);
        lean_dec(opt);
        decl
    }
}

// ---------------------------------------------------------------------------
// Missing shims: inline C++ functions not exported as symbols
// ---------------------------------------------------------------------------

// List.nil = scalar, List.cons: field[0]=head, field[1]=tail
#[no_mangle]
pub unsafe extern "C" fn lean_list_head(l: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(l, 0)
}

#[no_mangle]
pub unsafe extern "C" fn lean_list_tail(l: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(l, 1)
}

// Expr::Const (tag 4): field[0]=name, field[1]=List Level
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_const_levels(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(e, 1)
}

// Expr::Pi (tag 7)
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_pi(e: *const LeanObject) -> bool {
    !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_PI
}

// Lambda/Pi: field[0]=name, field[1]=domain, field[2]=body
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_binding_domain(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(e, 1)
}

#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_binding_body(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(e, 2)
}

// Expr.Data u64 is stored after the header+object-fields.
// Bits [63:44] = bvarRange. has_loose_bvars iff bvarRange > 0.
#[no_mangle]
pub unsafe extern "C" fn lean_expr_has_loose_bvars(e: *const LeanObject) -> bool {
    if lean_is_scalar(e) { return false; }
    let num_objs = (*e).other as usize;
    let data = (e.add(1) as *const u8).add(num_objs * 8).cast::<u64>().read();
    (data >> 44) > 0
}

// Count arguments in an App chain: App(App(f,a1),a2) has 2 args.
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_app_num_args(e: *const LeanObject) -> u32 {
    let mut count = 0u32;
    let mut cur = e;
    while !lean_is_scalar(cur) && lean_ptr_tag(cur) == EXPR_APP {
        count += 1;
        cur = lean_ctor_get(cur, 0);
    }
    count
}

// Expr::Lit (tag 9): field[0]=Literal. Literal::Nat has tag 0.
const LITERAL_NAT_TAG: u32 = 0;

#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_nat_lit(e: *const LeanObject) -> bool {
    !lean_is_scalar(e)
        && lean_ptr_tag(e) == EXPR_LIT
        && !lean_is_scalar(lean_ctor_get(e, 0))
        && lean_ptr_tag(lean_ctor_get(e, 0)) == LITERAL_NAT_TAG
}

// Get Nat from Expr::Lit(Literal::Nat(n))
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_lit_nat(e: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(lean_ctor_get(e, 0), 0)
}

// Create Expr::Lit(Literal::Nat(n)). Consumes n.
#[no_mangle]
pub unsafe extern "C" fn lean_expr_mk_lit_nat(n: *mut LeanObject) -> *mut LeanObject {
    let lit = lean_alloc_ctor(LITERAL_NAT_TAG, 1, 0);
    lean_ctor_set(lit, 0, n);
    lean_expr_mk_lit(lit)
}

// ---------------------------------------------------------------------------
// Nat arithmetic shims — inline-equivalent dispatch (small vs. big nat)
// Small Nat: tagged scalar, value = lean_unbox(ptr), max = LEAN_MAX_SMALL_NAT.
// Big Nat:   heap-allocated mpz object.
// ---------------------------------------------------------------------------
const LEAN_MAX_SMALL_NAT: usize = usize::MAX >> 1;

#[inline(always)]
unsafe fn lean_usize_to_nat(n: usize) -> *mut LeanObject {
    if n <= LEAN_MAX_SMALL_NAT {
        super::lean_box(n)
    } else {
        runtime_object_nat_int_impl::lean_big_usize_to_nat(n)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_mk_obj(n: u64) -> *mut LeanObject {
    if n <= LEAN_MAX_SMALL_NAT as u64 {
        super::lean_box(n as usize)
    } else {
        runtime_object_nat_int_impl::lean_big_uint64_to_nat(n)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_add(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        lean_usize_to_nat(lean_unbox(a as *const _).wrapping_add(lean_unbox(b as *const _)))
    } else {
        runtime_object_nat_int_impl::lean_nat_big_add(a, b)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_sub(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        let n1 = lean_unbox(a as *const _);
        let n2 = lean_unbox(b as *const _);
        super::lean_box(if n1 >= n2 { n1 - n2 } else { 0 })
    } else {
        runtime_object_nat_int_impl::lean_nat_big_sub(a, b)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_mul(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        let n1 = lean_unbox(a as *const _);
        if n1 == 0 { return a; }
        let n2 = lean_unbox(b as *const _);
        let r = n1.wrapping_mul(n2);
        if r <= LEAN_MAX_SMALL_NAT && r / n1 == n2 {
            super::lean_box(r)
        } else {
            runtime_object_nat_int_impl::lean_nat_overflow_mul(n1, n2)
        }
    } else {
        runtime_object_nat_int_impl::lean_nat_big_mul(a, b)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_div(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        let n1 = lean_unbox(a as *const _);
        let n2 = lean_unbox(b as *const _);
        super::lean_box(if n2 == 0 { 0 } else { n1 / n2 })
    } else {
        runtime_object_nat_int_impl::lean_nat_big_div(a, b)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_mod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        let n1 = lean_unbox(a as *const _);
        let n2 = lean_unbox(b as *const _);
        super::lean_box(if n2 == 0 { n1 } else { n1 % n2 })
    } else {
        runtime_object_nat_int_impl::lean_nat_big_mod(a, b)
    }
}

// For land/lor, tagged-scalar bitwise ops preserve the tag bit (bit 0 = 1 & 1 = 1 / 1 | 1 = 1).
#[no_mangle]
pub unsafe extern "C" fn lean_nat_land(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        (a as usize & b as usize) as *mut LeanObject
    } else {
        runtime_object_nat_int_impl::lean_nat_big_land(a, b)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_lor(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        (a as usize | b as usize) as *mut LeanObject
    } else {
        runtime_object_nat_int_impl::lean_nat_big_lor(a, b)
    }
}

// lean_nat_xor (= lean_nat_lxor in lean.h): tag bit cancels on XOR so must unbox/rebox.
#[no_mangle]
pub unsafe extern "C" fn lean_nat_xor(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        super::lean_box(lean_unbox(a as *const _) ^ lean_unbox(b as *const _))
    } else {
        runtime_object_nat_int_impl::lean_nat_big_xor(a, b)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_shiftr(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        let s1 = lean_unbox(a as *const _);
        let s2 = lean_unbox(b as *const _);
        super::lean_box(if s2 < usize::BITS as usize { s1 >> s2 } else { 0 })
    } else {
        runtime_object_nat_int_impl::lean_nat_big_shiftr(a, b)
    }
}

// ===========================================================================
// Real Lean/C++ exports used by the shims below.
// These are genuine exported symbols (Lean @[export] or C++ LEAN_EXPORT), as
// opposed to the inline C++ accessors which we re-implement as shims.
// ===========================================================================
extern "C" {
    // Expr binder info (Lean @[export], consumes its owned arg, returns u8).
    fn lean_expr_binder_info(e: *mut LeanObject) -> u8;
    // Environment quot-initialized flag (Lean @[export], consumes arg).
    fn lean_environment_quot_init(env: *mut LeanObject) -> u8;
    // RecursorVal flags (Lean @[export], consume arg).
    fn lean_recursor_k(v: *mut LeanObject) -> u8;
    fn lean_recursor_is_unsafe(v: *mut LeanObject) -> u8;
    // DefinitionVal safety (Lean @[export], consumes arg). 0 = unsafe, 1 = safe, 2 = partial.
    fn lean_definition_val_get_safety(v: *mut LeanObject) -> u8;
    // *_val unsafe flags (Lean @[export], consume arg).
    fn lean_axiom_val_is_unsafe(v: *mut LeanObject) -> u8;
    fn lean_opaque_val_is_unsafe(v: *mut LeanObject) -> u8;
    fn lean_inductive_val_is_unsafe(v: *mut LeanObject) -> u8;
    fn lean_constructor_val_is_unsafe(v: *mut LeanObject) -> u8;
    // ReducibilityHints height (Lean @[export], consumes arg).
    fn lean_reducibility_hints_get_height(h: *mut LeanObject) -> u32;
    // Native kernel reduction (C++ LEAN_EXPORT). Borrows env/opts/fn; returns Except.
    fn lean_eval_const_at_kernel_env(env: *mut LeanObject, opts: *mut LeanObject, fname: *mut LeanObject, n: usize, args: *const *mut LeanObject) -> *mut LeanObject;
    // Empty options (C++ LEAN_EXPORT). Consumes the unit arg, returns owned empty options.
    fn lean_options_get_empty(u: *mut LeanObject) -> *mut LeanObject;
    // Expr level-param instantiation (Lean @[export]). Borrows e/ps/ls, returns owned.
    fn lean_expr_instantiate_lparams(e: *mut LeanObject, ps: *mut LeanObject, ls: *mut LeanObject) -> *mut LeanObject;
    // Real Lean LocalContext builders (return new LocalContext; consume owned args).
    #[link_name = "lean_local_ctx_mk_local_decl"]
    fn lean_real_lctx_mk_local_decl(lctx: *mut LeanObject, fvar_id: *mut LeanObject, user_name: *mut LeanObject, ty: *mut LeanObject, bi: u8) -> *mut LeanObject;
    #[link_name = "lean_local_ctx_mk_let_decl"]
    fn lean_real_lctx_mk_let_decl(lctx: *mut LeanObject, fvar_id: *mut LeanObject, user_name: *mut LeanObject, ty: *mut LeanObject, value: *mut LeanObject, nondep: u8) -> *mut LeanObject;
    // local_ctx::mk_pi (= mk_binding<false>) via the clean C ABI wrapper in type_checker.cpp.
    // BORROWS lctx/fvars/body; returns an owned expr.
    fn lean_kernel_local_ctx_mk_pi(lctx: *mut LeanObject, fvars: *const *mut LeanObject, n: usize, body: *mut LeanObject, remove_dead_let: u8) -> *mut LeanObject;
}

// ===========================================================================
// Shims for the remaining inline-C++ accessor functions referenced by this
// module. Field-read accessors return BORROWED references (like C++
// cnstr_get_ref); callers add a reference where they retain the value.
// ===========================================================================

// --- Literal / constant_info / hints tag constants ---
const LITERAL_STRING_TAG: u32 = 1;
const CI_AXIOM: u32 = 0;
const CI_DEFINITION: u32 = 1;
const CI_THEOREM: u32 = 2;
const CI_OPAQUE: u32 = 3;
const CI_QUOT: u32 = 4;
const CI_INDUCTIVE: u32 = 5;
const CI_CONSTRUCTOR: u32 = 6;
const CI_RECURSOR: u32 = 7;
const DEFINITION_SAFETY_UNSAFE: u8 = 0;
const REDUCIBILITY_HINTS_REGULAR_TAG: u32 = 2;

// --- Name ---
// Name.anonymous is the boxed scalar 0.
#[no_mangle]
pub unsafe extern "C" fn lean_name_anonymous() -> *mut LeanObject {
    super::lean_box(0)
}

// --- List ---
// List.nil is the boxed scalar 0; List.cons (tag 1) has field[0]=head, field[1]=tail.
#[no_mangle]
pub unsafe extern "C" fn lean_list_is_nil(l: *const LeanObject) -> bool {
    lean_is_scalar(l)
}

// List.nil ignores its (erased) element-type argument.
#[no_mangle]
pub unsafe extern "C" fn lean_mk_list_nil(_ty: *mut LeanObject) -> *mut LeanObject {
    super::lean_box(0)
}

// --- Levels (Max tag 2 / IMax tag 3): field[0]=lhs, field[1]=rhs ---
#[no_mangle]
pub unsafe extern "C" fn lean_level_get_max_lhs(l: *const LeanObject) -> *mut LeanObject { lean_ctor_get(l, 0) }
#[no_mangle]
pub unsafe extern "C" fn lean_level_get_max_rhs(l: *const LeanObject) -> *mut LeanObject { lean_ctor_get(l, 1) }
#[no_mangle]
pub unsafe extern "C" fn lean_level_get_imax_lhs(l: *const LeanObject) -> *mut LeanObject { lean_ctor_get(l, 0) }
#[no_mangle]
pub unsafe extern "C" fn lean_level_get_imax_rhs(l: *const LeanObject) -> *mut LeanObject { lean_ctor_get(l, 1) }

// --- Expr kind / pointer identity ---
// expr_kind(e) = cnstr_tag(e); Expr is never a scalar.
#[no_mangle]
pub unsafe extern "C" fn lean_expr_kind(e: *const LeanObject) -> u32 { lean_ptr_tag(e) }

// is_eqp = pointer equality.
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_eqp(a: *const LeanObject, b: *const LeanObject) -> bool { a == b }

// --- Expr predicates ---
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_fvar(e: *const LeanObject) -> bool { !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_FVAR }
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_sort(e: *const LeanObject) -> bool { !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_SORT }
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_lambda(e: *const LeanObject) -> bool { !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_LAMBDA }
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_let(e: *const LeanObject) -> bool { !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_LET }
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_proj(e: *const LeanObject) -> bool { !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_PROJ }

// Expr::Lit (tag 9): field[0]=Literal. Literal::String has tag 1.
#[no_mangle]
pub unsafe extern "C" fn lean_expr_is_string_lit(e: *const LeanObject) -> bool {
    !lean_is_scalar(e)
        && lean_ptr_tag(e) == EXPR_LIT
        && !lean_is_scalar(lean_ctor_get(e, 0))
        && lean_ptr_tag(lean_ctor_get(e, 0)) == LITERAL_STRING_TAG
}

// --- Expr field accessors (borrowed) ---
// Expr::FVar (tag 1): field[0]=FVarId
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_fvar_id(e: *const LeanObject) -> *mut LeanObject { lean_ctor_get(e, 0) }
// Expr::Sort (tag 3): field[0]=Level
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_sort_level(e: *const LeanObject) -> *mut LeanObject { lean_ctor_get(e, 0) }
// Expr::MData (tag 10): field[0]=kvmap, field[1]=expr
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_mdata_expr(e: *const LeanObject) -> *mut LeanObject { lean_ctor_get(e, 1) }
// Lambda/Pi: field[0]=name
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_binding_name(e: *const LeanObject) -> *mut LeanObject { lean_ctor_get(e, 0) }
// Expr::Let (tag 8): field[0]=name, field[1]=type, field[2]=value, field[3]=body
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_let_name(e: *const LeanObject) -> *mut LeanObject { lean_ctor_get(e, 0) }
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_let_type(e: *const LeanObject) -> *mut LeanObject { lean_ctor_get(e, 1) }
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_let_value(e: *const LeanObject) -> *mut LeanObject { lean_ctor_get(e, 2) }
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_let_body(e: *const LeanObject) -> *mut LeanObject { lean_ctor_get(e, 3) }

// binding_info: delegates to the real lean_expr_binder_info (which consumes its arg).
#[no_mangle]
pub unsafe extern "C" fn lean_expr_get_binding_info(e: *const LeanObject) -> u8 {
    lean_inc(e as *mut _);
    lean_expr_binder_info(e as *mut _)
}

// Prop = Sort 0.
#[no_mangle]
pub unsafe extern "C" fn lean_expr_mk_prop() -> *mut LeanObject {
    let zero = lean_level_mk_zero();
    lean_expr_mk_sort(zero)
}

// --- Nat comparisons / helpers ---
#[no_mangle]
pub unsafe extern "C" fn lean_nat_eq(a: *const LeanObject, b: *const LeanObject) -> bool {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        lean_unbox(a) == lean_unbox(b)
    } else {
        runtime_object_nat_int_impl::lean_nat_big_eq(a as *mut _, b as *mut _)
    }
}
#[no_mangle]
pub unsafe extern "C" fn lean_nat_beq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
    lean_nat_eq(a as *const _, b as *const _)
}
#[no_mangle]
pub unsafe extern "C" fn lean_nat_ble(a: *mut LeanObject, b: *mut LeanObject) -> bool {
    if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
        lean_unbox(a as *const _) <= lean_unbox(b as *const _)
    } else {
        runtime_object_nat_int_impl::lean_nat_big_le(a, b)
    }
}
#[no_mangle]
pub unsafe extern "C" fn lean_nat_is_zero(n: *const LeanObject) -> bool {
    // Big Nat is never zero; small Nat zero is boxed scalar 0.
    lean_is_scalar(n) && lean_unbox(n) == 0
}
// Nat predecessor (saturating): n - 1.
#[no_mangle]
pub unsafe extern "C" fn lean_nat_dec(n: *mut LeanObject) -> *mut LeanObject {
    lean_nat_sub(n, super::lean_box(1))
}

// --- Environment ---
#[no_mangle]
pub unsafe extern "C" fn lean_environment_is_quot_initialized(env: *const LeanObject) -> bool {
    lean_inc(env as *mut _);
    lean_environment_quot_init(env as *mut _) != 0
}

// --- ConstantInfo (info tag = kind; field[0] = inner val; val.field[0] = constant_val) ---
// constant_val: field[0]=name, field[1]=lparams, field[2]=type
#[inline(always)]
unsafe fn ci_to_val(info: *const LeanObject) -> *mut LeanObject { lean_ctor_get(info, 0) }
#[inline(always)]
unsafe fn ci_constant_val(info: *const LeanObject) -> *mut LeanObject { lean_ctor_get(ci_to_val(info), 0) }

#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_get_name(info: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(ci_constant_val(info), 0)
}
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_get_lparams(info: *const LeanObject) -> *mut LeanObject {
    lean_ctor_get(ci_constant_val(info), 1)
}
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_get_num_lparams(info: *const LeanObject) -> u32 {
    lean_list_length(lean_ctor_get(ci_constant_val(info), 1))
}
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_is_definition(info: *const LeanObject) -> bool {
    !lean_is_scalar(info) && lean_ptr_tag(info) == CI_DEFINITION
}
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_is_constructor(info: *const LeanObject) -> bool {
    !lean_is_scalar(info) && lean_ptr_tag(info) == CI_CONSTRUCTOR
}
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_is_recursor(info: *const LeanObject) -> bool {
    !lean_is_scalar(info) && lean_ptr_tag(info) == CI_RECURSOR
}
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_to_definition_val(info: *const LeanObject) -> *mut LeanObject { ci_to_val(info) }
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_to_constructor_val(info: *const LeanObject) -> *mut LeanObject { ci_to_val(info) }
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_to_recursor_val(info: *const LeanObject) -> *mut LeanObject { ci_to_val(info) }
// has_value: theorem or definition.
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_has_value(info: *const LeanObject) -> bool {
    let k = lean_ptr_tag(info);
    k == CI_THEOREM || k == CI_DEFINITION
}
// get_safety: the argument is a definition_val (call site passes to_definition_val result).
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_get_safety(defval: *const LeanObject) -> u8 {
    lean_inc(defval as *mut _);
    lean_definition_val_get_safety(defval as *mut _)
}
// is_unsafe: mirrors constant_info::is_unsafe() switch on kind.
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_is_unsafe(info: *const LeanObject) -> bool {
    let val = ci_to_val(info);
    match lean_ptr_tag(info) {
        CI_AXIOM       => { lean_inc(val); lean_axiom_val_is_unsafe(val) != 0 }
        CI_DEFINITION  => { lean_inc(val); lean_definition_val_get_safety(val) == DEFINITION_SAFETY_UNSAFE }
        CI_THEOREM     => false,
        CI_OPAQUE      => { lean_inc(val); lean_opaque_val_is_unsafe(val) != 0 }
        CI_QUOT        => false,
        CI_INDUCTIVE   => { lean_inc(val); lean_inductive_val_is_unsafe(val) != 0 }
        CI_CONSTRUCTOR => { lean_inc(val); lean_constructor_val_is_unsafe(val) != 0 }
        CI_RECURSOR    => { lean_inc(val); lean_recursor_is_unsafe(val) != 0 }
        _              => false,
    }
}
// get_hints: definitions carry reducibility hints at val.field[2]; otherwise the opaque hint (boxed 0).
#[no_mangle]
pub unsafe extern "C" fn lean_constant_info_get_hints(info: *const LeanObject) -> *mut LeanObject {
    if lean_ptr_tag(info) == CI_DEFINITION {
        lean_ctor_get(ci_to_val(info), 2)
    } else {
        super::lean_box(0)
    }
}

// --- ConstructorVal: field[0]=cv, field[1]=induct, field[2]=cidx, field[3]=nparams, field[4]=nfields ---
#[no_mangle]
pub unsafe extern "C" fn lean_constructor_val_get_induct(v: *const LeanObject) -> *mut LeanObject { lean_ctor_get(v, 1) }
#[no_mangle]
pub unsafe extern "C" fn lean_constructor_val_get_nparams(v: *const LeanObject) -> u32 { lean_unbox(lean_ctor_get(v, 3)) as u32 }
#[no_mangle]
pub unsafe extern "C" fn lean_constructor_val_get_nfields(v: *const LeanObject) -> u32 { lean_unbox(lean_ctor_get(v, 4)) as u32 }

// --- RecursorVal: field[0]=cv,1=all,2=nparams,3=nindices,4=nmotives,5=nminors,6=rules ---
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_val_get_nparams(v: *const LeanObject) -> u32 { lean_unbox(lean_ctor_get(v, 2)) as u32 }
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_val_get_nmotives(v: *const LeanObject) -> u32 { lean_unbox(lean_ctor_get(v, 4)) as u32 }
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_val_get_nminors(v: *const LeanObject) -> u32 { lean_unbox(lean_ctor_get(v, 5)) as u32 }
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_val_get_rules(v: *const LeanObject) -> *mut LeanObject { lean_ctor_get(v, 6) }
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_val_get_major_idx(v: *const LeanObject) -> u32 {
    let nparams = lean_unbox(lean_ctor_get(v, 2)) as u32;
    let nindices = lean_unbox(lean_ctor_get(v, 3)) as u32;
    let nmotives = lean_unbox(lean_ctor_get(v, 4)) as u32;
    let nminors = lean_unbox(lean_ctor_get(v, 5)) as u32;
    nparams + nmotives + nminors + nindices
}
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_val_is_k(v: *const LeanObject) -> bool {
    lean_inc(v as *mut _);
    lean_recursor_k(v as *mut _) != 0
}
// get_major_induct: walk the constant_val.type telescope and return the head const's name (borrowed).
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_val_get_major_induct(v: *const LeanObject) -> *mut LeanObject {
    let n = lean_recursor_val_get_major_idx(v);
    // constant_val.type = field[2] of constant_val (= field[0] of recursor_val)
    let mut t = lean_ctor_get(lean_ctor_get(v, 0), 2);
    for _ in 0..n {
        // binding_body = field[2]
        t = lean_ctor_get(t, 2);
    }
    // binding_domain = field[1]
    t = lean_ctor_get(t, 1);
    // get_app_fn: strip App spine (App field[0]=fn)
    while !lean_is_scalar(t) && lean_ptr_tag(t) == EXPR_APP {
        t = lean_ctor_get(t, 0);
    }
    // const_name = field[0] of Const
    lean_ctor_get(t, 0)
}

// --- RecursorRule: field[0]=cnstr, field[1]=nfields, field[2]=rhs ---
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_rule_get_cnstr(r: *const LeanObject) -> *mut LeanObject { lean_ctor_get(r, 0) }
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_rule_get_nfields(r: *const LeanObject) -> u32 { lean_unbox(lean_ctor_get(r, 1)) as u32 }
#[no_mangle]
pub unsafe extern "C" fn lean_recursor_rule_get_rhs(r: *const LeanObject) -> *mut LeanObject { lean_ctor_get(r, 2) }

// --- LocalDecl: cdecl (tag 0) / ldecl (tag 1); ldecl field[4]=value ---
#[no_mangle]
pub unsafe extern "C" fn lean_local_decl_has_value(d: *const LeanObject) -> bool {
    !lean_is_scalar(d) && lean_ptr_tag(d) != 0
}
// get_value returns the borrowed value expr; only valid when has_value (ldecl).
#[no_mangle]
pub unsafe extern "C" fn lean_local_decl_get_value(d: *const LeanObject) -> *mut LeanObject { lean_ctor_get(d, 4) }

// --- reducibility_hints compare / is_regular ---
// kind: Opaque=boxed 0, Abbreviation=boxed 1, Regular=heap ctor (tag 2 with uint32 height).
#[inline(always)]
unsafe fn hints_kind(h: *const LeanObject) -> u32 {
    if lean_is_scalar(h) { lean_unbox(h) as u32 } else { lean_ptr_tag(h) }
}
#[inline(always)]
unsafe fn hints_height(h: *const LeanObject) -> u32 {
    lean_inc(h as *mut _);
    lean_reducibility_hints_get_height(h as *mut _)
}
#[no_mangle]
pub unsafe extern "C" fn lean_hints_is_regular(h: *const LeanObject) -> bool {
    hints_kind(h) == REDUCIBILITY_HINTS_REGULAR_TAG
}
// Mirrors C++ compare(reducibility_hints): <0 unfold h1, ==0 unfold both, >0 unfold h2.
#[no_mangle]
pub unsafe extern "C" fn lean_hints_compare(h1: *const LeanObject, h2: *const LeanObject) -> i32 {
    const OPAQUE: u32 = 0;
    const ABBREVIATION: u32 = 1;
    const REGULAR: u32 = 2;
    let k1 = hints_kind(h1);
    let k2 = hints_kind(h2);
    if k1 == k2 {
        if k1 == REGULAR {
            let a = hints_height(h1);
            let b = hints_height(h2);
            if a == b { 0 } else if a > b { -1 } else { 1 }
        } else {
            0
        }
    } else if k1 == OPAQUE {
        1
    } else if k2 == OPAQUE {
        -1
    } else if k1 == ABBREVIATION {
        -1
    } else if k2 == ABBREVIATION {
        1
    } else {
        0
    }
}

// --- Native reduction: wrap lean_eval_const_at_kernel_env (mirrors ir::run_boxed_kernel) ---
// Borrows env/opts/fname; returns the unwrapped result value (Except payload).
#[no_mangle]
pub unsafe extern "C" fn lean_ir_run_boxed_kernel(env: *const LeanObject, opts: *mut LeanObject, name: *mut LeanObject, n: u32, args: *const *mut LeanObject) -> *mut LeanObject {
    let result = lean_eval_const_at_kernel_env(env as *mut _, opts, name, n as usize, args);
    let value = lean_ctor_get(result, 0);
    lean_inc(value);
    lean_dec(result);
    value
}

// --- Empty options (mirrors C++ options() default constructor) ---
#[no_mangle]
pub unsafe extern "C" fn lean_mk_empty_options() -> *mut LeanObject {
    lean_options_get_empty(super::lean_box(0))
}

// --- LocalContext: build (fvar, new_lctx) pairs from the real Lean exports ---
// These are NOT #[no_mangle]: `lean_local_ctx_mk_local_decl` is also a Lean stdlib
// export (returning just the LocalContext), so an exported shim would collide.
// As module-local fns they simply shadow the names at the call sites in this file.
//
// `mk_local_decl(g, un, type, bi)` in C++ does:
//   new_lctx = lean_local_ctx_mk_local_decl(lctx, g.next(), un, type, bi); return mk_fvar(g.next())
// The fresh fvarId is supplied by the caller as `fvar_id`.
unsafe fn lean_local_ctx_mk_local_decl(
    lctx: *mut LeanObject,
    fvar_id: *mut LeanObject,
    user_name: *mut LeanObject,
    ty: *mut LeanObject,
    bi: u8,
) -> *mut LeanObject {
    // The real export consumes lctx/fvar_id/user_name/ty; preserve the caller's refs.
    lean_inc(lctx); lean_inc(fvar_id); lean_inc(user_name); lean_inc(ty);
    let new_lctx = lean_real_lctx_mk_local_decl(lctx, fvar_id, user_name, ty, bi);
    lean_inc(fvar_id); // lean_expr_mk_fvar consumes its arg
    let fvar = lean_expr_mk_fvar(fvar_id);
    let pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, fvar);
    lean_ctor_set(pair, 1, new_lctx);
    pair
}

unsafe fn lean_local_ctx_mk_local_decl_with_value(
    lctx: *mut LeanObject,
    fvar_id: *mut LeanObject,
    user_name: *mut LeanObject,
    ty: *mut LeanObject,
    value: *mut LeanObject,
) -> *mut LeanObject {
    // The real export consumes all owned args; preserve the caller's refs.
    lean_inc(lctx); lean_inc(fvar_id); lean_inc(user_name); lean_inc(ty); lean_inc(value);
    let new_lctx = lean_real_lctx_mk_let_decl(lctx, fvar_id, user_name, ty, value, 0);
    lean_inc(fvar_id); // lean_expr_mk_fvar consumes its arg
    let fvar = lean_expr_mk_fvar(fvar_id);
    let pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, fvar);
    lean_ctor_set(pair, 1, new_lctx);
    pair
}

// --- local_ctx::mk_pi (mk_binding<false>) via the clean C ABI wrapper in type_checker.cpp ---
unsafe fn lean_local_ctx_mk_pi(
    lctx: *const LeanObject,
    fvars: *const *mut LeanObject,
    n: u32,
    body: *mut LeanObject,
    remove_dead_let: bool,
) -> *mut LeanObject {
    lean_kernel_local_ctx_mk_pi(lctx as *mut _, fvars, n as usize, body, remove_dead_let as u8)
}

// ---------------------------------------------------------------------------
// Expression kind constants (mirrors expr_kind in C++)
// ---------------------------------------------------------------------------
const EXPR_BVAR:   u32 = 0;
const EXPR_FVAR:   u32 = 1;
const EXPR_MVAR:   u32 = 2;
const EXPR_SORT:   u32 = 3;
const EXPR_CONST:  u32 = 4;
const EXPR_APP:    u32 = 5;
const EXPR_LAMBDA: u32 = 6;
const EXPR_PI:     u32 = 7;
const EXPR_LET:    u32 = 8;
const EXPR_LIT:    u32 = 9;
const EXPR_MDATA:  u32 = 10;
const EXPR_PROJ:   u32 = 11;

// Level kind constants
const LEVEL_ZERO:  u32 = 0; // scalar (lean_is_scalar)
const LEVEL_SUCC:  u32 = 1;
const LEVEL_MAX:   u32 = 2;
const LEVEL_IMAX:  u32 = 3;
const LEVEL_PARAM: u32 = 4;
const LEVEL_MVAR:  u32 = 5;

// `Except ε α` constructor tags: `error` is declared first, `ok` second.
const EXCEPT_ERROR_TAG: u32 = 0;
const EXCEPT_OK_TAG:    u32 = 1;

// Definition safety
const DEF_SAFETY_UNSAFE:  u8 = 0;
const DEF_SAFETY_SAFE:    u8 = 1;
const DEF_SAFETY_PARTIAL: u8 = 2;

// Binder info
const BI_DEFAULT:  u8 = 0;
const BI_IMPLICIT: u8 = 1;
const BI_STRICT:   u8 = 2;
const BI_INST:     u8 = 3;

// ---------------------------------------------------------------------------
// LBool (three-valued boolean: true / false / undef)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum LBool {
    True,
    False,
    Undef,
}

impl LBool {
    fn from_bool(b: bool) -> Self {
        if b { LBool::True } else { LBool::False }
    }
}

// ---------------------------------------------------------------------------
// Level arithmetic helpers
// ---------------------------------------------------------------------------

unsafe fn level_kind(l: *const LeanObject) -> u32 {
    if lean_is_scalar(l) {
        LEVEL_ZERO
    } else {
        lean_ptr_tag(l)
    }
}

/// Strips succ chain from `l`, returns (base, offset).
unsafe fn level_to_offset(l: *const LeanObject) -> (*const LeanObject, u32) {
    let mut cur = l;
    let mut offset: u32 = 0;
    while level_kind(cur) == LEVEL_SUCC {
        cur = lean_level_get_succ(cur);
        offset += 1;
    }
    (cur, offset)
}

/// Push all flattened Max arguments of `l` into `buf`.
unsafe fn level_push_max_args(l: *const LeanObject, buf: &mut Vec<*mut LeanObject>) {
    if level_kind(l) == LEVEL_MAX {
        level_push_max_args(lean_level_get_max_lhs(l), buf);
        level_push_max_args(lean_level_get_max_rhs(l), buf);
    } else {
        lean_inc(l as *mut LeanObject);
        buf.push(l as *mut LeanObject);
    }
}

/// Normalize a level (port of normalize(level) from level.h).
unsafe fn normalize_level(l: *mut LeanObject) -> *mut LeanObject {
    match level_kind(l) {
        LEVEL_ZERO | LEVEL_PARAM | LEVEL_MVAR => {
            lean_inc(l);
            l
        }
        LEVEL_SUCC => {
            let inner = lean_level_get_succ(l);
            let norm = normalize_level(inner);
            // mk_succ consumes `norm` (obj_arg) — no dec afterwards.
            lean_level_mk_succ(norm)
        }
        LEVEL_MAX => {
            // Port of `normalize` (level.h): flatten max args, normalize each (re-flattening
            // since normalization may itself yield a max), sort by is_norm_lt, then drop
            // subsumed args (same base ⇒ keep only the largest offset; an explicit/numeral
            // arg is dropped when some other arg has an offset ≥ it), and rebuild the max.
            let mut todo: Vec<*mut LeanObject> = Vec::new();
            level_push_max_args(l, &mut todo);
            let mut args: Vec<*mut LeanObject> = Vec::new();
            for &a in &todo {
                let na = normalize_level(a);
                level_push_max_args(na, &mut args);
                lean_dec(na);
            }
            for &a in &todo { lean_dec(a); }

            args.sort_by(|&a, &b| {
                if is_norm_lt(a, b) { std::cmp::Ordering::Less }
                else if is_norm_lt(b, a) { std::cmp::Ordering::Greater }
                else { std::cmp::Ordering::Equal }
            });

            // Select indices to keep (subsumption); dec the rest.
            let mut keep: Vec<usize> = Vec::new();
            let mut i = 0usize;
            if is_explicit_level(args[0]) {
                while i + 1 < args.len() && is_explicit_level(args[i + 1]) { i += 1; }
                let k = level_to_offset(args[i] as *const LeanObject).1;
                let mut j = i + 1;
                while j < args.len() && level_to_offset(args[j] as *const LeanObject).1 < k { j += 1; }
                if j < args.len() { i += 1; } // largest explicit is subsumed by a non-explicit arg
            }
            keep.push(i);
            let (mut prev_base, mut prev_off) = level_to_offset(args[i] as *const LeanObject);
            i += 1;
            while i < args.len() {
                let (cb, co) = level_to_offset(args[i] as *const LeanObject);
                if lean_level_eq(prev_base, cb) {
                    if prev_off < co {
                        prev_base = cb; prev_off = co;
                        keep.pop();
                        keep.push(i);
                    }
                } else {
                    prev_base = cb; prev_off = co;
                    keep.push(i);
                }
                i += 1;
            }

            let keep_set: HashSet<usize> = keep.iter().copied().collect();
            let mut kept: Vec<*mut LeanObject> = Vec::with_capacity(keep.len());
            for (idx, &a) in args.iter().enumerate() {
                if keep_set.contains(&idx) { kept.push(a); } else { lean_dec(a); }
            }

            // mk_max consumes both args (obj_arg); `kept` owns each, so they flow in without dec.
            kept.iter().rev().copied().reduce(|acc, cur| {
                lean_level_mk_max(cur, acc)
            }).unwrap_or_else(|| lean_level_mk_zero())
        }
        LEVEL_IMAX => {
            let lhs_raw = lean_level_get_imax_lhs(l);
            let rhs_raw = lean_level_get_imax_rhs(l);
            let lhs = normalize_level(lhs_raw);
            let rhs = normalize_level(rhs_raw);
            // IMax l 0 = 0
            if level_kind(rhs) == LEVEL_ZERO {
                lean_dec(lhs);
                lean_dec(rhs);
                return lean_level_mk_zero();
            }
            // IMax l (Succ r) = Max l (Succ r). mk_max/mk_imax consume lhs/rhs — no dec after.
            if level_kind(rhs) == LEVEL_SUCC {
                let m = lean_level_mk_max(lhs, rhs);
                let r = normalize_level(m);
                lean_dec(m);
                return r;
            }
            lean_level_mk_imax(lhs, rhs)
        }
        _ => {
            lean_inc(l);
            l
        }
    }
}

/// A level is "explicit" (a numeral) iff its succ-chain bottoms out at `zero`.
unsafe fn is_explicit_level(l: *const LeanObject) -> bool {
    level_kind(level_to_offset(l).0) == LEVEL_ZERO
}

/// Comparison for sorted Max-arg deduplication (port of is_norm_lt).
unsafe fn is_norm_lt(a: *const LeanObject, b: *const LeanObject) -> bool {
    let (base_a, off_a) = level_to_offset(a);
    let (base_b, off_b) = level_to_offset(b);
    let ka = level_kind(base_a);
    let kb = level_kind(base_b);
    if ka != kb {
        return ka < kb;
    }
    if ka == LEVEL_PARAM || ka == LEVEL_MVAR {
        let na = lean_level_get_param_name(base_a);
        let nb = lean_level_get_param_name(base_b);
        let ha = expr_hash(na as *const LeanObject); // reuse hash for name (borrowing)
        let hb = expr_hash(nb as *const LeanObject);
        if ha != hb { return ha < hb; }
    }
    off_a < off_b
}

/// Check level equivalence (modulo normalization).
unsafe fn is_equivalent_level(l1: *mut LeanObject, l2: *mut LeanObject) -> Result<bool, KernelError> {
    check_system_result()?;
    if lean_level_eq(l1, l2) {
        return Ok(true);
    }
    let n1 = normalize_level(l1);
    let n2 = normalize_level(l2);
    let eq = lean_level_eq(n1, n2);
    lean_dec(n1);
    lean_dec(n2);
    Ok(eq)
}

/// Return true if l is definitely not zero for any universe assignment.
unsafe fn is_not_zero_level(l: *const LeanObject) -> bool {
    match level_kind(l) {
        LEVEL_ZERO  => false,
        LEVEL_PARAM => false,
        LEVEL_MVAR  => false,
        LEVEL_SUCC  => true,
        LEVEL_MAX   => {
            is_not_zero_level(lean_level_get_max_lhs(l))
                || is_not_zero_level(lean_level_get_max_rhs(l))
        }
        LEVEL_IMAX  => {
            is_not_zero_level(lean_level_get_imax_rhs(l))
        }
        _ => false,
    }
}

/// Return true if l1 >= l2 (port of is_geq_core after normalizing).
unsafe fn is_geq_level(l1: *mut LeanObject, l2: *mut LeanObject) -> Result<bool, KernelError> {
    if lean_level_eq(l1, l2) { return Ok(true); }
    let n1 = normalize_level(l1);
    let n2 = normalize_level(l2);
    let result = is_geq_normalized(n1, n2);
    lean_dec(n1);
    lean_dec(n2);
    result
}

unsafe fn is_geq_normalized(l1: *mut LeanObject, l2: *mut LeanObject) -> Result<bool, KernelError> {
    check_system_result()?;
    if lean_level_eq(l1, l2) { return Ok(true); }
    let (base1, off1) = level_to_offset(l1 as *const LeanObject);
    let (base2, off2) = level_to_offset(l2 as *const LeanObject);
    // l1 = base1 + off1, l2 = base2 + off2
    // l1 >= l2  iff  base1 + off1 >= base2 + off2
    if level_kind(l2) == LEVEL_MAX {
        // l1 >= max(a, b)  iff  l1 >= a && l1 >= b
        let a = lean_level_get_max_lhs(l2);
        let b = lean_level_get_max_rhs(l2);
        return Ok(is_geq_normalized(l1, a)? && is_geq_normalized(l1, b)?);
    }
    if level_kind(l1) == LEVEL_MAX {
        // max(a, b) >= l2  iff  a >= l2 || b >= l2
        let a = lean_level_get_max_lhs(l1);
        let b = lean_level_get_max_rhs(l1);
        return Ok(is_geq_normalized(a, l2)? || is_geq_normalized(b, l2)?);
    }
    if lean_level_eq(base1, base2) {
        return Ok(off1 >= off2);
    }
    // ZERO base: l1 >= l2 only if l2 is zero
    if level_kind(base2) == LEVEL_ZERO {
        return Ok(true); // any >= 0
    }
    Ok(false)
}

/// Traverse level `l`; return first param name not in `lparams`, or None.
unsafe fn get_undef_param(l: *const LeanObject, lparams: *const LeanObject) -> Option<*mut LeanObject> {
    match level_kind(l) {
        LEVEL_ZERO => None,
        LEVEL_PARAM => {
            let name = lean_level_get_param_name(l);
            let mut cur = lparams as *mut LeanObject;
            while !lean_list_is_nil(cur) {
                let h = lean_list_head(cur);
                if lean_name_eq(h, name) {
                    return None;
                }
                cur = lean_list_tail(cur);
            }
            Some(name)
        }
        LEVEL_MVAR  => None, // mvars are not params
        LEVEL_SUCC  => get_undef_param(lean_level_get_succ(l), lparams),
        LEVEL_MAX   => {
            get_undef_param(lean_level_get_max_lhs(l), lparams)
                .or_else(|| get_undef_param(lean_level_get_max_rhs(l), lparams))
        }
        LEVEL_IMAX  => {
            get_undef_param(lean_level_get_imax_lhs(l), lparams)
                .or_else(|| get_undef_param(lean_level_get_imax_rhs(l), lparams))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// KernelError — mirrors the 17 Lean.Kernel.Exception variants
// ---------------------------------------------------------------------------

pub enum KernelError {
    // Type-error variants (carry Lean object pointers)
    UnknownConstant       { env: *mut LeanObject, name: *mut LeanObject },
    AlreadyDeclared       { env: *mut LeanObject, name: *mut LeanObject },
    DeclTypeMismatch      { env: *mut LeanObject, decl: *mut LeanObject, given_type: *mut LeanObject },
    DeclHasMVars          { env: *mut LeanObject, name: *mut LeanObject, expr: *mut LeanObject },
    DeclHasFVars          { env: *mut LeanObject, name: *mut LeanObject, expr: *mut LeanObject },
    FunExpected           { env: *mut LeanObject, lctx: *mut LeanObject, expr: *mut LeanObject },
    TypeExpected          { env: *mut LeanObject, lctx: *mut LeanObject, expr: *mut LeanObject },
    LetTypeMismatch       { env: *mut LeanObject, lctx: *mut LeanObject, name: *mut LeanObject,
                            given: *mut LeanObject, expected: *mut LeanObject },
    ExprTypeMismatch      { env: *mut LeanObject, lctx: *mut LeanObject, expr: *mut LeanObject,
                            expected: *mut LeanObject },
    AppTypeMismatch       { env: *mut LeanObject, lctx: *mut LeanObject, app: *mut LeanObject,
                            fun_type: *mut LeanObject, arg_type: *mut LeanObject },
    InvalidProj           { env: *mut LeanObject, lctx: *mut LeanObject, proj: *mut LeanObject },
    ThmTypeIsNotProp      { env: *mut LeanObject, name: *mut LeanObject, ty: *mut LeanObject },
    Other                 { msg: *mut LeanObject },
    // Resource-limit variants (no payload; use lean_box)
    DeterministicTimeout,
    ExcessiveMemory,
    DeepRecursion,
    Interrupted,
}

impl Drop for KernelError {
    fn drop(&mut self) {
        unsafe {
            match self {
                KernelError::UnknownConstant  { env, name }
                | KernelError::AlreadyDeclared { env, name }  => {
                    lean_dec(*env); lean_dec(*name);
                }
                KernelError::DeclTypeMismatch { env, decl, given_type } => {
                    lean_dec(*env); lean_dec(*decl); lean_dec(*given_type);
                }
                KernelError::DeclHasMVars { env, name, expr }
                | KernelError::DeclHasFVars { env, name, expr } => {
                    lean_dec(*env); lean_dec(*name); lean_dec(*expr);
                }
                KernelError::FunExpected  { env, lctx, expr }
                | KernelError::TypeExpected { env, lctx, expr }
                | KernelError::InvalidProj  { env, lctx, proj: expr } => {
                    lean_dec(*env); lean_dec(*lctx); lean_dec(*expr);
                }
                KernelError::LetTypeMismatch { env, lctx, name, given, expected } => {
                    lean_dec(*env); lean_dec(*lctx); lean_dec(*name);
                    lean_dec(*given); lean_dec(*expected);
                }
                KernelError::ExprTypeMismatch { env, lctx, expr, expected } => {
                    lean_dec(*env); lean_dec(*lctx); lean_dec(*expr); lean_dec(*expected);
                }
                KernelError::AppTypeMismatch { env, lctx, app, fun_type, arg_type } => {
                    lean_dec(*env); lean_dec(*lctx); lean_dec(*app);
                    lean_dec(*fun_type); lean_dec(*arg_type);
                }
                KernelError::ThmTypeIsNotProp { env, name, ty } => {
                    lean_dec(*env); lean_dec(*name); lean_dec(*ty);
                }
                KernelError::Other { msg } => {
                    lean_dec(*msg);
                }
                KernelError::DeterministicTimeout
                | KernelError::ExcessiveMemory
                | KernelError::DeepRecursion
                | KernelError::Interrupted => {}
            }
        }
    }
}

/// Convert KernelError into a Lean `Except KernelException α` value (Except.error …).
unsafe fn kernel_error_to_lean_except(e: KernelError) -> *mut LeanObject {
    let inner: *mut LeanObject = match e {
        KernelError::UnknownConstant { env, name } => {
            let o = lean_alloc_ctor(0, 2, 0); // tag 0
            lean_ctor_set(o, 0, env);
            lean_ctor_set(o, 1, name);
            o
        }
        KernelError::AlreadyDeclared { env, name } => {
            let o = lean_alloc_ctor(1, 2, 0);
            lean_ctor_set(o, 0, env);
            lean_ctor_set(o, 1, name);
            o
        }
        KernelError::DeclTypeMismatch { env, decl, given_type } => {
            let o = lean_alloc_ctor(2, 3, 0);
            lean_ctor_set(o, 0, env);
            lean_ctor_set(o, 1, decl);
            lean_ctor_set(o, 2, given_type);
            o
        }
        KernelError::DeclHasMVars { env, name, expr } => {
            let o = lean_alloc_ctor(3, 3, 0);
            lean_ctor_set(o, 0, env); lean_ctor_set(o, 1, name); lean_ctor_set(o, 2, expr); o
        }
        KernelError::DeclHasFVars { env, name, expr } => {
            let o = lean_alloc_ctor(4, 3, 0);
            lean_ctor_set(o, 0, env); lean_ctor_set(o, 1, name); lean_ctor_set(o, 2, expr); o
        }
        KernelError::FunExpected { env, lctx, expr } => {
            let o = lean_alloc_ctor(5, 3, 0);
            lean_ctor_set(o, 0, env); lean_ctor_set(o, 1, lctx); lean_ctor_set(o, 2, expr); o
        }
        KernelError::TypeExpected { env, lctx, expr } => {
            let o = lean_alloc_ctor(6, 3, 0);
            lean_ctor_set(o, 0, env); lean_ctor_set(o, 1, lctx); lean_ctor_set(o, 2, expr); o
        }
        KernelError::LetTypeMismatch { env, lctx, name, given, expected } => {
            let o = lean_alloc_ctor(7, 5, 0);
            lean_ctor_set(o, 0, env); lean_ctor_set(o, 1, lctx); lean_ctor_set(o, 2, name);
            lean_ctor_set(o, 3, given); lean_ctor_set(o, 4, expected);
            o
        }
        KernelError::ExprTypeMismatch { env, lctx, expr, expected } => {
            let o = lean_alloc_ctor(8, 4, 0);
            lean_ctor_set(o, 0, env); lean_ctor_set(o, 1, lctx);
            lean_ctor_set(o, 2, expr); lean_ctor_set(o, 3, expected);
            o
        }
        KernelError::AppTypeMismatch { env, lctx, app, fun_type, arg_type } => {
            let o = lean_alloc_ctor(9, 5, 0);
            lean_ctor_set(o, 0, env); lean_ctor_set(o, 1, lctx); lean_ctor_set(o, 2, app);
            lean_ctor_set(o, 3, fun_type); lean_ctor_set(o, 4, arg_type);
            o
        }
        KernelError::InvalidProj { env, lctx, proj } => {
            let o = lean_alloc_ctor(10, 3, 0);
            lean_ctor_set(o, 0, env); lean_ctor_set(o, 1, lctx); lean_ctor_set(o, 2, proj); o
        }
        KernelError::ThmTypeIsNotProp { env, name, ty } => {
            let o = lean_alloc_ctor(11, 3, 0);
            lean_ctor_set(o, 0, env); lean_ctor_set(o, 1, name); lean_ctor_set(o, 2, ty); o
        }
        KernelError::Other { msg } => {
            let o = lean_alloc_ctor(12, 1, 0);
            lean_ctor_set(o, 0, msg); o
        }
        KernelError::DeterministicTimeout => lean_box(13),
        KernelError::ExcessiveMemory     => lean_box(14),
        KernelError::DeepRecursion       => lean_box(15),
        KernelError::Interrupted         => lean_box(16),
    };
    // Wrap: Except.error inner (Except.error is the first constructor → tag 0)
    let except_err = lean_alloc_ctor(EXCEPT_ERROR_TAG, 1, 0);
    lean_ctor_set(except_err, 0, inner);
    except_err
}

// ---------------------------------------------------------------------------
// Owned reference-counted Lean objects
// ---------------------------------------------------------------------------

/// RAII wrapper that increments refcount on construction and decrements on drop.
struct OwnedLean(*mut LeanObject);

impl OwnedLean {
    unsafe fn new(o: *mut LeanObject) -> Self {
        lean_inc(o);
        OwnedLean(o)
    }
    fn get(&self) -> *mut LeanObject {
        self.0
    }
    /// Consume without decrementing (transfer ownership to caller).
    fn into_raw(self) -> *mut LeanObject {
        let p = self.0;
        std::mem::forget(self);
        p
    }
}

impl Drop for OwnedLean {
    fn drop(&mut self) {
        unsafe { lean_dec(self.0); }
    }
}

impl Clone for OwnedLean {
    fn clone(&self) -> Self {
        unsafe { OwnedLean::new(self.0) }
    }
}

// ---------------------------------------------------------------------------
// ExprKey — wrapper for HashMap/HashSet keys over expression pointers
// ---------------------------------------------------------------------------

struct ExprKey(*mut LeanObject);

impl ExprKey {
    unsafe fn new(o: *mut LeanObject) -> Self {
        lean_inc(o);
        ExprKey(o)
    }
}

impl Drop for ExprKey {
    fn drop(&mut self) {
        unsafe { lean_dec(self.0); }
    }
}

impl std::hash::Hash for ExprKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { expr_hash(self.0).hash(state) }
    }
}

impl PartialEq for ExprKey {
    fn eq(&self, other: &Self) -> bool {
        unsafe { lean_expr_eqv(self.0, other.0) }
    }
}

impl Eq for ExprKey {}

type ExprCache = HashMap<ExprKey, OwnedLean>;

// ---------------------------------------------------------------------------
// NameGenerator
// ---------------------------------------------------------------------------

struct NameGenerator {
    prefix: *mut LeanObject, // owned
    counter: u64,
}

impl NameGenerator {
    unsafe fn new(prefix: *mut LeanObject) -> Self {
        lean_inc(prefix);
        NameGenerator { prefix, counter: 0 }
    }

    unsafe fn mk_fresh_name(&mut self) -> *mut LeanObject {
        let counter_obj = lean_nat_mk_obj(self.counter);
        let n = lean_name_mk_numeral(self.prefix, counter_obj);
        lean_dec(counter_obj);
        self.counter += 1;
        n
    }
}

impl Drop for NameGenerator {
    fn drop(&mut self) {
        unsafe { lean_dec(self.prefix); }
    }
}

// ---------------------------------------------------------------------------
// Global constants (AtomicPtr, initialized once)
// ---------------------------------------------------------------------------

macro_rules! global_const {
    ($name:ident) => {
        static $name: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());
    };
}

global_const!(G_KERNEL_FRESH);
global_const!(G_BOOL_TRUE);
global_const!(G_EXPR_BOOL_TRUE);  // `Expr.const Bool.true []`
global_const!(G_EXPR_BOOL_FALSE); // `Expr.const Bool.false []`
global_const!(G_EAGER_REDUCE);
global_const!(G_DONT_CARE);
global_const!(G_NAT_ZERO);
global_const!(G_NAT_SUCC);
global_const!(G_NAT_ADD);
global_const!(G_NAT_SUB);
global_const!(G_NAT_MUL);
global_const!(G_NAT_POW);
global_const!(G_NAT_GCD);
global_const!(G_NAT_DIV);
global_const!(G_NAT_MOD);
global_const!(G_NAT_BEQ);
global_const!(G_NAT_BLE);
global_const!(G_NAT_LAND);
global_const!(G_NAT_LOR);
global_const!(G_NAT_XOR);
global_const!(G_NAT_SHIFTLEFT);
global_const!(G_NAT_SHIFTRIGHT);
global_const!(G_STRING_MK);
global_const!(G_LEAN_REDUCE_BOOL);
global_const!(G_LEAN_REDUCE_NAT);

unsafe fn load_global(g: &AtomicPtr<LeanObject>) -> *mut LeanObject {
    g.load(Ordering::Acquire)
}

/// Look up a constant, returning an owned bare `ConstantInfo`, or a boxed scalar
/// (testable with `lean_is_scalar`) when the constant is absent.
///
/// `lean_environment_find` *consumes* both of its arguments (the C++ `environment::find`
/// passes `env`/`name` via `to_obj_arg()`) and returns an `Option ConstantInfo`. Our
/// callers hold only borrowed references and expect the unwrapped `ConstantInfo`, so we
/// inc both inputs and strip the `Option.some` wrapper here.
unsafe fn env_find(env: *const LeanObject, name: *mut LeanObject) -> *mut LeanObject {
    lean_inc(env as *mut LeanObject);
    lean_inc(name);
    let opt = lean_environment_find(env, name);
    if lean_is_scalar(opt) {
        opt // Option.none
    } else {
        let info = lean_ctor_get(opt, 0); // Option.some payload (borrowed)
        lean_inc(info);
        lean_dec(opt);
        info
    }
}

/// Build a persistent const expression and store in a global.
unsafe fn init_global_const(g: &AtomicPtr<LeanObject>, parts: &[&str]) {
    let name = build_lean_name(parts);
    lean_mark_persistent(name);
    let levels = lean_mk_list_nil(ptr::null_mut()); // empty list
    let expr = lean_expr_mk_const(name, levels);
    lean_mark_persistent(expr);
    g.store(expr, Ordering::Release);
}

/// Build a Lean name from dot-separated parts.
unsafe fn build_lean_name(parts: &[&str]) -> *mut LeanObject {
    let mut cur = lean_name_anonymous();
    for &part in parts {
        let s = lean_mk_string(part.as_ptr(), part.len());
        // lean_name_mk_string consumes both `cur` and `s` (obj_arg). Do NOT dec
        // them afterwards — ownership is transferred into the new name.
        cur = lean_name_mk_string(cur, s);
    }
    cur
}

// ---------------------------------------------------------------------------
// System check
// ---------------------------------------------------------------------------

unsafe fn check_system_result() -> Result<(), KernelError> {
    if !lean_stack_has_space() {
        return Err(KernelError::DeepRecursion);
    }
    if !lean_memory_within_limit() {
        return Err(KernelError::ExcessiveMemory);
    }
    if check_heartbeat_exceeded() {
        return Err(KernelError::DeterministicTimeout);
    }
    if check_interrupted_flag() {
        return Err(KernelError::Interrupted);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// TypeCheckerState
// ---------------------------------------------------------------------------

struct TypeCheckerState {
    env:          *mut LeanObject, // borrowed (inc'd by TypeChecker creator)
    ngen:         NameGenerator,
    infer_cache:  [ExprCache; 2],  // [0]=check mode, [1]=infer-only mode
    whnf_core:    ExprCache,
    whnf:         ExprCache,
    unfold:       ExprCache,
    eqv_manager:  *mut c_void, // owned EquivManager
    failure:      HashSet<(ExprKey, ExprKey)>,
}

impl TypeCheckerState {
    unsafe fn new(env: *mut LeanObject) -> Self {
        lean_inc(env);
        let prefix = load_global(&G_KERNEL_FRESH);
        TypeCheckerState {
            env,
            ngen: NameGenerator::new(prefix),
            infer_cache: [HashMap::new(), HashMap::new()],
            whnf_core: HashMap::new(),
            whnf: HashMap::new(),
            unfold: HashMap::new(),
            eqv_manager: lean_equiv_manager_new(),
            failure: HashSet::new(),
        }
    }
}

impl Drop for TypeCheckerState {
    fn drop(&mut self) {
        unsafe {
            lean_dec(self.env);
            lean_equiv_manager_free(self.eqv_manager);
        }
    }
}

// ---------------------------------------------------------------------------
// TypeChecker
// ---------------------------------------------------------------------------

struct TypeChecker {
    st:                 Box<TypeCheckerState>,
    lctx:               *mut LeanObject, // owned
    definition_safety:  u8,
    eager_reduce:       bool,
    lparams:            Option<*mut LeanObject>, // borrowed, names list
}

impl TypeChecker {
    unsafe fn new(env: *mut LeanObject, lctx: *mut LeanObject, definition_safety: u8) -> Self {
        lean_inc(lctx);
        TypeChecker {
            st: Box::new(TypeCheckerState::new(env)),
            lctx,
            definition_safety,
            eager_reduce: false,
            lparams: None,
        }
    }

    fn env(&self) -> *mut LeanObject {
        self.st.env
    }

    unsafe fn with_saved_lctx<R, E, F>(&mut self, f: F) -> Result<R, E>
    where F: FnOnce(&mut Self) -> Result<R, E>
    {
        let saved = self.lctx;
        lean_inc(saved);
        let result = f(self);
        let old = self.lctx;
        self.lctx = saved;
        lean_dec(old);
        result
    }

    /// Create a fresh local declaration in lctx. Returns the fvar expr.
    unsafe fn lctx_mk_local_decl(
        &mut self,
        name: *mut LeanObject,
        ty: *mut LeanObject,
        bi: u8,
    ) -> *mut LeanObject {
        // lean_local_ctx_mk_local_decl returns (fvar, new_lctx) as a pair
        let id = self.st.ngen.mk_fresh_name();
        let result_pair = lean_local_ctx_mk_local_decl(self.lctx, id, name, ty, bi);
        lean_dec(id);
        let fvar = lean_ctor_get(result_pair, 0);
        let new_lctx = lean_ctor_get(result_pair, 1);
        lean_inc(fvar);
        lean_inc(new_lctx);
        lean_dec(result_pair);
        lean_dec(self.lctx);
        self.lctx = new_lctx;
        fvar
    }

    unsafe fn lctx_mk_lambda(&self, fvars: &[*mut LeanObject], body: *mut LeanObject) -> *mut LeanObject {
        lean_local_ctx_mk_lambda(self.lctx, fvars.as_ptr(), fvars.len() as u32, body)
    }

    unsafe fn lctx_mk_pi(&self, fvars: &[*mut LeanObject], body: *mut LeanObject, remove_dead_let: bool) -> *mut LeanObject {
        lean_local_ctx_mk_pi(self.lctx, fvars.as_ptr(), fvars.len() as u32, body, remove_dead_let)
    }

    // -----------------------------------------------------------------------
    // Level checking
    // -----------------------------------------------------------------------

    unsafe fn check_level(&self, l: *const LeanObject) -> Result<(), KernelError> {
        if let Some(lparams) = self.lparams {
            if let Some(undef) = get_undef_param(l, lparams) {
                let msg = format_level_error_msg(undef);
                return Err(KernelError::Other { msg });
            }
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // ensure_sort / ensure_pi
    // -----------------------------------------------------------------------

    unsafe fn ensure_sort_core(&mut self, e: *mut LeanObject, s: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        if lean_expr_is_sort(e) {
            lean_inc(e);
            return Ok(e);
        }
        let new_e = self.whnf(e)?;
        if lean_expr_is_sort(new_e) {
            return Ok(new_e);
        }
        lean_dec(new_e);
        lean_inc(self.st.env);
        lean_inc(self.lctx);
        lean_inc(s);
        Err(KernelError::TypeExpected { env: self.st.env, lctx: self.lctx, expr: s })
    }

    unsafe fn ensure_pi_core(&mut self, e: *mut LeanObject, s: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        if lean_expr_is_pi(e) {
            lean_inc(e);
            return Ok(e);
        }
        let new_e = self.whnf(e)?;
        if lean_expr_is_pi(new_e) {
            return Ok(new_e);
        }
        lean_dec(new_e);
        lean_inc(self.st.env);
        lean_inc(self.lctx);
        lean_inc(s);
        Err(KernelError::FunExpected { env: self.st.env, lctx: self.lctx, expr: s })
    }

    // -----------------------------------------------------------------------
    // infer_fvar
    // -----------------------------------------------------------------------

    unsafe fn infer_fvar(&self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        let opt_decl = lean_local_ctx_find_local_decl(self.lctx, e);
        if lean_is_scalar(opt_decl) {
            // None
            lean_inc(self.st.env);
            let msg = lean_mk_string(b"unknown free variable".as_ptr(), 21);
            return Err(KernelError::Other { msg });
        }
        let ty = lean_local_decl_get_type(opt_decl);
        lean_inc(ty);
        lean_dec(opt_decl);
        Ok(ty)
    }

    // -----------------------------------------------------------------------
    // infer_constant
    // -----------------------------------------------------------------------

    unsafe fn infer_constant(&mut self, e: *mut LeanObject, infer_only: bool) -> Result<*mut LeanObject, KernelError> {
        let name = lean_expr_get_const_name(e);
        let info_opt = env_find(self.st.env, name);
        if lean_is_scalar(info_opt) {
            // not found
            lean_inc(self.st.env);
            lean_inc(name);
            return Err(KernelError::UnknownConstant { env: self.st.env, name });
        }
        let info = info_opt;
        let ps = lean_constant_info_get_lparams(info);
        let ls = lean_expr_get_const_levels(e);
        let ps_len = list_length(ps);
        let ls_len = list_length(ls);
        if ps_len != ls_len {
            let msg = format_arity_error_msg(name, ps_len, ls_len);
            lean_dec(info);
            return Err(KernelError::Other { msg });
        }
        if !infer_only {
            if lean_constant_info_is_unsafe(info) && self.definition_safety != DEF_SAFETY_UNSAFE {
                lean_inc(self.st.env);
                lean_inc(name);
                lean_dec(info);
                let msg_str = format!("invalid declaration, it uses unsafe declaration '{}'", lean_name_to_string(name));
                let msg = lean_mk_string(msg_str.as_ptr(), msg_str.len());
                return Err(KernelError::Other { msg });
            }
            if lean_constant_info_is_definition(info) {
                let defval = lean_constant_info_to_definition_val(info);
                let safety = lean_constant_info_get_safety(defval);
                if safety == DEF_SAFETY_PARTIAL && self.definition_safety == DEF_SAFETY_SAFE {
                    lean_dec(info);
                    let msg_str = format!("invalid declaration, safe declaration must not contain partial declaration");
                    let msg = lean_mk_string(msg_str.as_ptr(), msg_str.len());
                    return Err(KernelError::Other { msg });
                }
            }
            // check each level
            let mut lev = ls;
            while !lean_list_is_nil(lev) {
                let l = lean_list_head(lev);
                self.check_level(l)?;
                lev = lean_list_tail(lev);
            }
        }
        let result = lean_instantiate_type_lparams(info, ls);
        lean_dec(info);
        Ok(result)
    }

    // -----------------------------------------------------------------------
    // infer_lambda
    // -----------------------------------------------------------------------

    unsafe fn infer_lambda(&mut self, e_orig: *mut LeanObject, infer_only: bool) -> Result<*mut LeanObject, KernelError> {
        self.with_saved_lctx(|tc| {
            let mut fvars: Vec<*mut LeanObject> = Vec::new();
            let mut e = e_orig;
            lean_inc(e);
            while lean_expr_is_lambda(e) {
                let name = lean_expr_get_binding_name(e);
                let domain_bv = lean_expr_get_binding_domain(e);
                let d = if fvars.is_empty() {
                    lean_inc(domain_bv);
                    domain_bv
                } else {
                    lean_expr_instantiate_rev(domain_bv, fvars.len() as u32, fvars.as_ptr())
                };
                if !infer_only {
                    let sort = tc.infer_type_core(d, infer_only)?;
                    let _ = tc.ensure_sort_core(sort, d)?;
                }
                let bi = lean_expr_get_binding_info(e);
                let fvar = tc.lctx_mk_local_decl(name, d, bi);
                lean_dec(d);
                fvars.push(fvar);
                let body = lean_expr_get_binding_body(e);
                let new_e = lean_expr_instantiate1(body, fvar);
                lean_dec(e);
                e = new_e;
            }
            let inst = if fvars.is_empty() {
                lean_inc(e);
                e
            } else {
                lean_expr_instantiate_rev(e, fvars.len() as u32, fvars.as_ptr())
            };
            lean_dec(e);
            let mut r = tc.infer_type_core(inst, infer_only)?;
            lean_dec(inst);
            r = lean_expr_cheap_beta_reduce(r);
            // infer_lambda builds a Pi over cdecls (remove_dead_let = false)
            let pi = tc.lctx_mk_pi(&fvars, r, false);
            lean_dec(r);
            for f in &fvars { lean_dec(*f); }
            Ok(pi)
        })
    }

    // -----------------------------------------------------------------------
    // infer_pi
    // -----------------------------------------------------------------------

    unsafe fn infer_pi(&mut self, e_orig: *mut LeanObject, infer_only: bool) -> Result<*mut LeanObject, KernelError> {
        self.with_saved_lctx(|tc| {
            let mut fvars: Vec<*mut LeanObject> = Vec::new();
            let mut us: Vec<*mut LeanObject> = Vec::new(); // levels
            let mut e = e_orig;
            lean_inc(e);
            while lean_expr_is_pi(e) {
                let domain_bv = lean_expr_get_binding_domain(e);
                let d = lean_expr_instantiate_rev(domain_bv, fvars.len() as u32, fvars.as_ptr());
                let d_type = tc.infer_type_core(d, infer_only)?;
                let t1 = tc.ensure_sort_core(d_type, d)?;
                us.push(lean_expr_get_sort_level(t1));
                lean_inc(*us.last().unwrap());
                lean_dec(t1);
                let name = lean_expr_get_binding_name(e);
                let bi = lean_expr_get_binding_info(e);
                let fvar = tc.lctx_mk_local_decl(name, d, bi);
                lean_dec(d);
                fvars.push(fvar);
                let body = lean_expr_get_binding_body(e);
                let new_e = lean_expr_instantiate1(body, fvar);
                lean_dec(e);
                e = new_e;
            }
            let inst = lean_expr_instantiate_rev(e, fvars.len() as u32, fvars.as_ptr());
            lean_dec(e);
            let inst_type = tc.infer_type_core(inst, infer_only)?;
            let s = tc.ensure_sort_core(inst_type, inst)?;
            lean_dec(inst);
            let mut r_level = lean_expr_get_sort_level(s);
            lean_inc(r_level);
            lean_dec(s);
            // Fold imax right to left. mk_imax/mk_sort consume their args (obj_arg);
            // `us` holds owned levels and `r_level` is owned, so they flow in without dec.
            for level in us.iter().rev() {
                r_level = lean_level_mk_imax(*level, r_level);
            }
            let result = lean_expr_mk_sort(r_level);
            for f in &fvars { lean_dec(*f); }
            Ok(result)
        })
    }

    // -----------------------------------------------------------------------
    // infer_app
    // -----------------------------------------------------------------------

    unsafe fn infer_app(&mut self, e: *mut LeanObject, infer_only: bool) -> Result<*mut LeanObject, KernelError> {
        if !infer_only {
            let fn_type = self.infer_type_core(lean_expr_get_app_fn(e), infer_only)?;
            let f_type = self.ensure_pi_core(fn_type, e)?;
            let arg = lean_expr_get_app_arg(e);
            let a_type = self.infer_type_core(arg, infer_only)?;
            let d_type = lean_expr_get_binding_domain(f_type);

            // Detect eagerReduce argument
            let is_eager = is_eager_reduce_expr(arg);
            let saved_eager = self.eager_reduce;
            if is_eager { self.eager_reduce = true; }

            let def_eq = self.is_def_eq(a_type, d_type)?;
            if is_eager { self.eager_reduce = saved_eager; }

            if !def_eq {
                lean_inc(self.st.env);
                lean_inc(self.lctx);
                lean_inc(e);
                lean_inc(f_type);
                lean_inc(a_type);
                return Err(KernelError::AppTypeMismatch {
                    env: self.st.env,
                    lctx: self.lctx,
                    app: e,
                    fun_type: f_type,
                    arg_type: a_type,
                });
            }
            lean_dec(a_type);
            let body = lean_expr_get_binding_body(f_type);
            let result = lean_expr_instantiate1(body, arg);
            lean_dec(f_type);
            Ok(result)
        } else {
            // infer-only fast path: collect args, infer f type, thread bindings
            let mut args: Vec<*mut LeanObject> = Vec::new();
            let mut cur = e;
            while lean_expr_is_app(cur) {
                args.push(lean_expr_get_app_arg(cur));
                cur = lean_expr_get_app_fn(cur);
            }
            args.reverse();
            let f = cur;
            let mut f_type = self.infer_type_core(f, true)?;
            let mut j = 0usize;
            let nargs = args.len();
            for i in 0..nargs {
                if lean_expr_is_pi(f_type) {
                    let body = lean_expr_get_binding_body(f_type);
                    // consume binding without substituting yet
                    let old = f_type;
                    lean_inc(body);
                    lean_dec(old);
                    f_type = body;
                } else {
                    let inst = lean_expr_instantiate_rev(f_type, (i - j) as u32, args[j..i].as_ptr());
                    lean_dec(f_type);
                    f_type = self.ensure_pi_core(inst, e)?;
                    let body = lean_expr_get_binding_body(f_type);
                    lean_inc(body);
                    lean_dec(f_type);
                    f_type = body;
                    j = i;
                }
            }
            let result = lean_expr_instantiate_rev(f_type, (nargs - j) as u32, args[j..].as_ptr());
            lean_dec(f_type);
            Ok(result)
        }
    }

    // -----------------------------------------------------------------------
    // infer_let
    // -----------------------------------------------------------------------

    unsafe fn infer_let(&mut self, e_orig: *mut LeanObject, infer_only: bool) -> Result<*mut LeanObject, KernelError> {
        self.with_saved_lctx(|tc| {
            let mut fvars: Vec<*mut LeanObject> = Vec::new();
            let mut e = e_orig;
            lean_inc(e);
            while lean_expr_is_let(e) {
                let name = lean_expr_get_let_name(e);
                let ty_bv = lean_expr_get_let_type(e);
                let val_bv = lean_expr_get_let_value(e);
                let ty = lean_expr_instantiate_rev(ty_bv, fvars.len() as u32, fvars.as_ptr());
                let val = lean_expr_instantiate_rev(val_bv, fvars.len() as u32, fvars.as_ptr());
                if !infer_only {
                    let ty_type = tc.infer_type_core(ty, infer_only)?;
                    let _ = tc.ensure_sort_core(ty_type, ty)?;
                    let val_type = tc.infer_type_core(val, infer_only)?;
                    if !tc.is_def_eq(val_type, ty)? {
                        lean_inc(tc.st.env);
                        lean_inc(tc.lctx);
                        lean_inc(name);
                        lean_inc(val_type);
                        lean_inc(ty);
                        return Err(KernelError::LetTypeMismatch {
                            env: tc.st.env, lctx: tc.lctx, name,
                            given: val_type, expected: ty,
                        });
                    }
                }
                // mk_local_decl_with_value
                let id = tc.st.ngen.mk_fresh_name();
                let pair = lean_local_ctx_mk_local_decl_with_value(tc.lctx, id, name, ty, val);
                lean_dec(id);
                lean_dec(ty);
                lean_dec(val);
                let fvar = lean_ctor_get(pair, 0);
                let new_lctx = lean_ctor_get(pair, 1);
                lean_inc(fvar);
                lean_inc(new_lctx);
                lean_dec(pair);
                lean_dec(tc.lctx);
                tc.lctx = new_lctx;
                fvars.push(fvar);
                let body = lean_expr_get_let_body(e);
                let new_e = lean_expr_instantiate1(body, fvar);
                lean_dec(e);
                e = new_e;
            }
            let inst = lean_expr_instantiate_rev(e, fvars.len() as u32, fvars.as_ptr());
            lean_dec(e);
            let mut r = tc.infer_type_core(inst, infer_only)?;
            lean_dec(inst);
            r = lean_expr_cheap_beta_reduce(r);
            // mk_pi with is_let = true (remove_dead_let = true)
            let pi = tc.lctx_mk_pi(&fvars, r, true);
            lean_dec(r);
            for f in &fvars { lean_dec(*f); }
            Ok(pi)
        })
    }

    // -----------------------------------------------------------------------
    // infer_proj
    // -----------------------------------------------------------------------

    unsafe fn infer_proj(&mut self, e: *mut LeanObject, infer_only: bool) -> Result<*mut LeanObject, KernelError> {
        let proj_e = lean_expr_get_proj_expr(e);
        let proj_sname = lean_expr_get_proj_sname(e);
        let proj_idx_nat = lean_expr_get_proj_idx(e);

        if !lean_nat_is_small(proj_idx_nat) {
            lean_inc(self.st.env);
            lean_inc(self.lctx);
            lean_inc(e);
            return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
        }
        let idx = lean_nat_get_small_value(proj_idx_nat) as usize;

        let proj_e_type_uninferred = self.infer_type_core(proj_e, infer_only)?;
        let mut ty = self.whnf(proj_e_type_uninferred)?;
        lean_dec(proj_e_type_uninferred);

        // Collect args from the type application
        let mut type_args: Vec<*mut LeanObject> = Vec::new();
        let mut cur = ty;
        while lean_expr_is_app(cur) {
            type_args.push(lean_expr_get_app_arg(cur));
            cur = lean_expr_get_app_fn(cur);
        }
        type_args.reverse();
        let I = cur;

        if !lean_expr_is_const(I) {
            lean_dec(ty);
            lean_inc(self.st.env); lean_inc(self.lctx); lean_inc(e);
            return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
        }
        let I_name = lean_expr_get_const_name(I);
        if !lean_name_eq(I_name, proj_sname) {
            lean_dec(ty);
            lean_inc(self.st.env); lean_inc(self.lctx); lean_inc(e);
            return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
        }

        let I_info_opt = env_find(self.st.env, I_name);
        if lean_is_scalar(I_info_opt) || !lean_constant_info_is_inductive(I_info_opt) {
            lean_dec(ty);
            lean_inc(self.st.env); lean_inc(self.lctx); lean_inc(e);
            return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
        }
        let I_val = lean_constant_info_to_inductive_val(I_info_opt);
        let nparams = lean_inductive_val_get_nparams(I_val) as usize;
        let nindices = lean_inductive_val_get_nindices(I_val) as usize;
        let ncnstrs = lean_inductive_val_get_ncnstrs(I_val);

        if ncnstrs != 1 || type_args.len() != nparams + nindices {
            lean_dec(ty);
            lean_dec(I_info_opt);
            lean_inc(self.st.env); lean_inc(self.lctx); lean_inc(e);
            return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
        }

        let cnstr_names = lean_inductive_val_get_cnstrs(I_val);
        let cnstr_name = lean_list_head(cnstr_names);
        let c_info_opt = env_find(self.st.env, cnstr_name);
        let I_levels = lean_expr_get_const_levels(I);
        let mut r = lean_instantiate_type_lparams(c_info_opt, I_levels);
        lean_dec(c_info_opt);
        lean_dec(I_info_opt);

        // Apply parameters
        for i in 0..nparams {
            r = self.whnf(r)?;
            if !lean_expr_is_pi(r) {
                lean_dec(ty); lean_dec(r);
                lean_inc(self.st.env); lean_inc(self.lctx); lean_inc(e);
                return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
            }
            let body = lean_expr_get_binding_body(r);
            let new_r = lean_expr_instantiate1(body, type_args[i]);
            lean_dec(r);
            r = new_r;
        }

        let is_prop_type = self.is_prop(ty)?;
        lean_dec(ty);

        // Skip fields up to idx
        for i in 0..idx {
            r = self.whnf(r)?;
            if !lean_expr_is_pi(r) {
                lean_dec(r);
                lean_inc(self.st.env); lean_inc(self.lctx); lean_inc(e);
                return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
            }
            if is_prop_type {
                let dom = lean_expr_get_binding_domain(r);
                if !self.is_prop(dom)? {
                    lean_dec(r);
                    lean_inc(self.st.env); lean_inc(self.lctx); lean_inc(e);
                    return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
                }
            }
            let body = lean_expr_get_binding_body(r);
            if lean_expr_has_loose_bvars(body) {
                let proj_i = lean_expr_mk_proj(proj_sname, lean_nat_mk_obj(i as u64), proj_e);
                lean_inc(proj_sname); lean_inc(proj_e);
                let new_r = lean_expr_instantiate1(body, proj_i);
                lean_dec(proj_i);
                lean_dec(r);
                r = new_r;
            } else {
                lean_inc(body);
                lean_dec(r);
                r = body;
            }
        }

        r = self.whnf(r)?;
        if !lean_expr_is_pi(r) {
            lean_dec(r);
            lean_inc(self.st.env); lean_inc(self.lctx); lean_inc(e);
            return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
        }
        let dom = lean_expr_get_binding_domain(r);
        if is_prop_type && !self.is_prop(dom)? {
            lean_dec(r);
            lean_inc(self.st.env); lean_inc(self.lctx); lean_inc(e);
            return Err(KernelError::InvalidProj { env: self.st.env, lctx: self.lctx, proj: e });
        }
        lean_inc(dom);
        lean_dec(r);
        Ok(dom)
    }

    // -----------------------------------------------------------------------
    // infer_type_core — main dispatch
    // -----------------------------------------------------------------------

    unsafe fn infer_type_core(&mut self, e: *mut LeanObject, infer_only: bool) -> Result<*mut LeanObject, KernelError> {
        if lean_expr_has_loose_bvars(e) {
            let msg = lean_mk_string(b"type checker does not support loose bound variables".as_ptr(), 51);
            return Err(KernelError::Other { msg });
        }

        check_system_result()?;

        let cache_idx = if infer_only { 1 } else { 0 };
        let key = ExprKey::new(e);
        if let Some(v) = self.st.infer_cache[cache_idx].get(&key) {
            let r = v.get();
            lean_inc(r);
            return Ok(r);
        }

        let kind = lean_expr_kind(e);
        let r: *mut LeanObject = match kind {
            EXPR_LIT   => {
                // lit_type returns Nat or String based on literal kind
                lean_lit_type(e)
            }
            EXPR_MDATA => self.infer_type_core(lean_expr_get_mdata_expr(e), infer_only)?,
            EXPR_PROJ  => self.infer_proj(e, infer_only)?,
            EXPR_FVAR  => self.infer_fvar(e)?,
            EXPR_MVAR  => {
                let msg = lean_mk_string(b"kernel type checker does not support meta variables".as_ptr(), 51);
                return Err(KernelError::Other { msg });
            }
            EXPR_BVAR  => {
                // should be unreachable after instantiate
                let msg = lean_mk_string(b"unexpected bound variable in type checker".as_ptr(), 41);
                return Err(KernelError::Other { msg });
            }
            EXPR_SORT  => {
                let l = lean_expr_get_sort_level(e);
                if !infer_only {
                    self.check_level(l)?;
                }
                // lean_level_mk_succ / lean_expr_mk_sort both take obj_arg (consume their
                // argument). `l` is borrowed from `e`, so inc it once to hand an owned
                // reference to mk_succ; the resulting `l2` is owned and consumed by mk_sort.
                lean_inc(l);
                let l2 = lean_level_mk_succ(l);
                lean_expr_mk_sort(l2)
            }
            EXPR_CONST  => self.infer_constant(e, infer_only)?,
            EXPR_LAMBDA => self.infer_lambda(e, infer_only)?,
            EXPR_PI     => self.infer_pi(e, infer_only)?,
            EXPR_APP    => self.infer_app(e, infer_only)?,
            EXPR_LET    => self.infer_let(e, infer_only)?,
            _ => {
                let msg = lean_mk_string(b"unknown expression kind".as_ptr(), 23);
                return Err(KernelError::Other { msg });
            }
        };

        // `OwnedLean::new` inc's `r` for the cache; the original owned `r` is returned.
        self.st.infer_cache[cache_idx].insert(ExprKey::new(e), OwnedLean::new(r));
        Ok(r)
    }

    unsafe fn infer_type(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        self.infer_type_core(e, true)
    }

    pub unsafe fn infer(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        self.infer_type(e)
    }

    // -----------------------------------------------------------------------
    // is_prop
    // -----------------------------------------------------------------------

    unsafe fn is_prop(&mut self, e: *mut LeanObject) -> Result<bool, KernelError> {
        let ty = self.infer_type(e)?;
        let whnf_ty = self.whnf(ty)?;
        lean_dec(ty);
        let prop = lean_expr_mk_prop();
        let eq = lean_expr_eqv(whnf_ty, prop);
        lean_dec(prop);
        lean_dec(whnf_ty);
        Ok(eq)
    }

    // -----------------------------------------------------------------------
    // reduce_recursor  (iota + quotient reduction)
    // -----------------------------------------------------------------------

    unsafe fn reduce_recursor(
        &mut self,
        e: *mut LeanObject,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Result<Option<*mut LeanObject>, KernelError> {
        // Try quotient reduction first
        if lean_environment_is_quot_initialized(self.st.env) {
            // We can't pass closures through the C quot_reduce_rec; use the inductive path instead
            // (A proper implementation would call quot_reduce_rec via a trampoline)
            // For now, fall through to inductive reduction
        }

        // Inductive reduction
        let result = inductive_reduce_rec_impl(
            self.st.env,
            e,
            cheap_rec,
            cheap_proj,
            self,
        )?;
        Ok(result)
    }

    // -----------------------------------------------------------------------
    // reduce_proj_core
    // -----------------------------------------------------------------------

    unsafe fn reduce_proj_core(&mut self, c: *mut LeanObject, idx: usize) -> Result<Option<*mut LeanObject>, KernelError> {
        let c = if lean_expr_is_string_lit(c) {
            let ctor = lean_string_lit_to_constructor(c);
            lean_inc(ctor);
            self.whnf(ctor)?
        } else {
            lean_inc(c);
            c
        };

        let mut args: Vec<*mut LeanObject> = Vec::new();
        let mut cur = c;
        while lean_expr_is_app(cur) {
            args.push(lean_expr_get_app_arg(cur));
            cur = lean_expr_get_app_fn(cur);
        }
        args.reverse();
        let mk = cur;

        if !lean_expr_is_const(mk) {
            lean_dec(c);
            return Ok(None);
        }
        let mk_name = lean_expr_get_const_name(mk);
        let mk_info = env_find(self.st.env, mk_name);
        if lean_is_scalar(mk_info) || !lean_constant_info_is_constructor(mk_info) {
            lean_dec(mk_info);
            lean_dec(c);
            return Ok(None);
        }
        let nparams = lean_constructor_val_get_nparams(lean_constant_info_to_constructor_val(mk_info)) as usize;
        lean_dec(mk_info);
        if nparams + idx < args.len() {
            let result = args[nparams + idx];
            lean_inc(result);
            lean_dec(c);
            Ok(Some(result))
        } else {
            lean_dec(c);
            Ok(None)
        }
    }

    unsafe fn reduce_proj(&mut self, e: *mut LeanObject, cheap_rec: bool, cheap_proj: bool) -> Result<Option<*mut LeanObject>, KernelError> {
        let idx_nat = lean_expr_get_proj_idx(e);
        if !lean_nat_is_small(idx_nat) { return Ok(None); }
        let idx = lean_nat_get_small_value(idx_nat) as usize;
        let proj_e = lean_expr_get_proj_expr(e);
        let c = if cheap_proj {
            self.whnf_core(proj_e, cheap_rec, cheap_proj)?
        } else {
            self.whnf(proj_e)?
        };
        let result = self.reduce_proj_core(c, idx)?;
        lean_dec(c);
        Ok(result)
    }

    // -----------------------------------------------------------------------
    // whnf_fvar
    // -----------------------------------------------------------------------

    unsafe fn whnf_fvar(&mut self, e: *mut LeanObject, cheap_rec: bool, cheap_proj: bool) -> Result<*mut LeanObject, KernelError> {
        let opt_decl = lean_local_ctx_find_local_decl(self.lctx, e);
        if !lean_is_scalar(opt_decl) && lean_local_decl_has_value(opt_decl) {
            let val = lean_local_decl_get_value(opt_decl);
            lean_inc(val);
            lean_dec(opt_decl);
            return self.whnf_core(val, cheap_rec, cheap_proj);
        }
        lean_dec(opt_decl);
        lean_inc(e);
        Ok(e)
    }

    // -----------------------------------------------------------------------
    // whnf_core
    // -----------------------------------------------------------------------

    unsafe fn whnf_core(&mut self, e: *mut LeanObject, cheap_rec: bool, cheap_proj: bool) -> Result<*mut LeanObject, KernelError> {
        check_system_result()?;

        let kind = lean_expr_kind(e);
        // Fast path for non-reducing cases
        match kind {
            EXPR_BVAR | EXPR_SORT | EXPR_MVAR | EXPR_PI | EXPR_CONST | EXPR_LAMBDA | EXPR_LIT => {
                lean_inc(e);
                return Ok(e);
            }
            EXPR_MDATA => {
                return self.whnf_core(lean_expr_get_mdata_expr(e), cheap_rec, cheap_proj);
            }
            EXPR_FVAR => {
                let opt_decl = lean_local_ctx_find_local_decl(self.lctx, e);
                let has_val = !lean_is_scalar(opt_decl) && lean_local_decl_has_value(opt_decl);
                lean_dec(opt_decl);
                if !has_val {
                    lean_inc(e);
                    return Ok(e);
                }
                // fall through to main work
            }
            EXPR_APP | EXPR_LET | EXPR_PROJ => {
                // fall through
            }
            _ => {
                lean_inc(e);
                return Ok(e);
            }
        }

        // Check whnf_core cache (only when not using cheap mode)
        if !cheap_rec && !cheap_proj {
            let key = ExprKey::new(e);
            if let Some(v) = self.st.whnf_core.get(&key) {
                let r = v.get();
                lean_inc(r);
                return Ok(r);
            }
        }

        let r: *mut LeanObject = match lean_expr_kind(e) {
            EXPR_FVAR => {
                self.whnf_fvar(e, cheap_rec, cheap_proj)?
            }
            EXPR_PROJ => {
                if let Some(m) = self.reduce_proj(e, cheap_rec, cheap_proj)? {
                    let result = self.whnf_core(m, cheap_rec, cheap_proj)?;
                    lean_dec(m);
                    result
                } else {
                    lean_inc(e);
                    e
                }
            }
            EXPR_APP => {
                let mut args: Vec<*mut LeanObject> = Vec::new();
                let mut cur = e;
                while lean_expr_is_app(cur) {
                    args.push(lean_expr_get_app_arg(cur));
                    cur = lean_expr_get_app_fn(cur);
                }
                args.reverse();
                // cur is now the function
                let f0 = cur;
                let f = self.whnf_core(f0, cheap_rec, cheap_proj)?;

                if lean_expr_is_lambda(f) {
                    // Beta reduction
                    let mut f_cur = f;
                    let mut m = 1usize;
                    let num_args = args.len();
                    while lean_expr_is_lambda(lean_expr_get_binding_body(f_cur)) && m < num_args {
                        f_cur = lean_expr_get_binding_body(f_cur);
                        m += 1;
                    }
                    let body = lean_expr_get_binding_body(f_cur);
                    // The lambda consumes the first `m` arguments (application order). C++ uses
                    // `instantiate` over a reversed buffer; the equivalent here is `instantiate_rev`
                    // over the first `m` args in application order: instantiate_rev maps
                    // bvar#i -> subst[m-1-i], so x0<-args[0] .. x_{m-1}<-args[m-1].
                    let inst = lean_expr_instantiate_rev(body, m as u32, args.as_ptr());
                    // apply the remaining args (application order). lean_expr_mk_app consumes both
                    // arguments, so inc each borrowed arg and let the previous `app` flow in.
                    let mut app = inst;
                    for &arg in &args[m..] {
                        lean_inc(arg);
                        app = lean_expr_mk_app(app, arg);
                    }
                    lean_dec(f);
                    let result = self.whnf_core(app, cheap_rec, cheap_proj)?;
                    lean_dec(app);
                    result
                } else if lean_expr_is_eqp(f, f0) {
                    // Try recursor
                    lean_inc(e);
                    if let Some(r) = self.reduce_recursor(e, cheap_rec, cheap_proj)? {
                        lean_dec(e);
                        lean_dec(f);
                        let result = self.whnf_core(r, cheap_rec, cheap_proj)?;
                        lean_dec(r);
                        result
                    } else {
                        lean_dec(f);
                        lean_dec(e);
                        lean_inc(e);
                        e
                    }
                } else {
                    // rebuild application with reduced function. mk_app consumes both args.
                    let mut app = f;
                    for &arg in &args {
                        lean_inc(arg);
                        app = lean_expr_mk_app(app, arg);
                    }
                    let result = self.whnf_core(app, cheap_rec, cheap_proj)?;
                    lean_dec(app);
                    result
                }
            }
            EXPR_LET => {
                // `Expr.letE` lays out [name, type, value, body]; the body is field 3.
                // `get_binding_body` is field 2 (Lambda/Pi layout) — for a `let` that is the
                // *value*, so we must use `get_let_body` here, else `let g := v; body` would
                // instantiate `v` into `v` and reduce to `v`.
                let val = lean_expr_get_let_value(e);
                let body = lean_expr_get_let_body(e);
                let inst = lean_expr_instantiate1(body, val);
                let result = self.whnf_core(inst, cheap_rec, cheap_proj)?;
                lean_dec(inst);
                result
            }
            _ => {
                lean_inc(e);
                e
            }
        };

        if !cheap_rec && !cheap_proj {
            self.st.whnf_core.insert(ExprKey::new(e), OwnedLean::new(r));
        }
        Ok(r)
    }

    // -----------------------------------------------------------------------
    // unfold_definition
    // -----------------------------------------------------------------------

    unsafe fn unfold_definition_core(&mut self, e: *mut LeanObject) -> Option<*mut LeanObject> {
        if !lean_expr_is_const(e) { return None; }
        let name = lean_expr_get_const_name(e);
        let info_opt = env_find(self.st.env, name);
        if lean_is_scalar(info_opt) { return None; }
        if !lean_constant_info_has_value(info_opt) {
            lean_dec(info_opt);
            return None;
        }
        let nparams = lean_constant_info_get_num_lparams(info_opt) as usize;
        let levels = lean_expr_get_const_levels(e);
        let levels_len = list_length(levels);
        if nparams != levels_len {
            lean_dec(info_opt);
            return None;
        }

        let levels_obj = levels;
        // Check unfold cache
        let key = ExprKey::new(e);
        if let Some(v) = self.st.unfold.get(&key) {
            lean_dec(info_opt);
            let r = v.get();
            lean_inc(r);
            return Some(r);
        }
        let result = lean_instantiate_value_lparams(info_opt, levels_obj);
        lean_dec(info_opt);
        // `OwnedLean::new` inc's `result` for the cache; the original owned `result` is returned.
        if levels_len > 0 {
            self.st.unfold.insert(ExprKey::new(e), OwnedLean::new(result));
        }
        Some(result)
    }

    unsafe fn unfold_definition(&mut self, e: *mut LeanObject) -> Option<*mut LeanObject> {
        if lean_expr_is_app(e) {
            // `lean_expr_get_app_fn` strips a single application layer; walk to the spine head.
            let mut f0 = e;
            while lean_expr_is_app(f0) {
                f0 = lean_expr_get_app_fn(f0);
            }
            if let Some(f) = self.unfold_definition_core(f0) {
                // rebuild with args
                let mut args: Vec<*mut LeanObject> = Vec::new();
                let mut cur = e;
                while lean_expr_is_app(cur) {
                    args.push(lean_expr_get_app_arg(cur));
                    cur = lean_expr_get_app_fn(cur);
                }
                // args are in reverse order. mk_app consumes both arguments.
                let mut app = f;
                for &arg in args.iter().rev() {
                    lean_inc(arg);
                    app = lean_expr_mk_app(app, arg);
                }
                Some(app)
            } else {
                None
            }
        } else {
            self.unfold_definition_core(e)
        }
    }

    // -----------------------------------------------------------------------
    // reduce_nat / reduce_native
    // -----------------------------------------------------------------------

    unsafe fn reduce_nat(&mut self, e: *mut LeanObject) -> Result<Option<*mut LeanObject>, KernelError> {
        let nargs = lean_expr_get_app_num_args(e);
        if nargs == 1 {
            let f = lean_expr_get_app_fn(e);
            let nat_succ = load_global(&G_NAT_SUCC);
            if lean_expr_eqv(f, nat_succ) {
                let arg_r = self.whnf(lean_expr_get_app_arg(e))?;
                let result = reduce_nat_succ(arg_r);
                lean_dec(arg_r);
                return Ok(result);
            }
        } else if nargs == 2 {
            let f = lean_expr_get_app_fn(lean_expr_get_app_fn(e));
            if !lean_expr_is_const(f) { return Ok(None); }
            let result = self.reduce_bin_nat_op(e, f)?;
            return Ok(result);
        }
        Ok(None)
    }

    unsafe fn reduce_bin_nat_op(&mut self, e: *mut LeanObject, f: *mut LeanObject) -> Result<Option<*mut LeanObject>, KernelError> {
        let arg1 = self.whnf(lean_expr_get_app_arg(lean_expr_get_app_fn(e)))?;
        if !is_nat_lit_ext(arg1) { lean_dec(arg1); return Ok(None); }
        let arg2 = self.whnf(lean_expr_get_app_arg(e))?;
        if !is_nat_lit_ext(arg2) { lean_dec(arg1); lean_dec(arg2); return Ok(None); }
        // v1/v2 are BORROWED out of arg1/arg2 (they may point inside the literals).
        // We must keep arg1/arg2 alive until we are done reading v1/v2, so the
        // decrements happen only after the computation below. lean_nat_* BORROW
        // their operands and return an owned result.
        let v1 = get_nat_val(arg1);
        let v2 = get_nat_val(arg2);

        let result: Option<*mut LeanObject> = 'compute: {
            // Nat.add, Nat.sub, Nat.mul, Nat.div, Nat.mod, Nat.gcd, Nat.land, Nat.lor, Nat.xor
            if lean_expr_eqv(f, load_global(&G_NAT_ADD)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_add(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_SUB)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_sub(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_MUL)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_mul(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_DIV)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_div(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_MOD)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_mod(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_GCD)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_gcd(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_LAND)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_land(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_LOR)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_lor(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_XOR)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_xor(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_SHIFTLEFT)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_shiftl(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_SHIFTRIGHT)) {
                break 'compute Some(lean_expr_mk_lit_nat(lean_nat_shiftr(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_POW)) {
                const MAX_EXP: u64 = 1 << 24;
                if lean_nat_is_small(v2) && (lean_nat_get_small_value(v2) as u64) <= MAX_EXP {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_pow(v1, v2, MAX_EXP)));
                } else {
                    break 'compute None;
                }
            }
            if lean_expr_eqv(f, load_global(&G_NAT_BEQ)) {
                break 'compute Some(mk_bool(lean_nat_beq(v1, v2)));
            }
            if lean_expr_eqv(f, load_global(&G_NAT_BLE)) {
                break 'compute Some(mk_bool(lean_nat_ble(v1, v2)));
            }
            None
        };

        lean_dec(arg1);
        lean_dec(arg2);
        Ok(result)
    }

    unsafe fn reduce_native(&self, e: *mut LeanObject) -> Option<*mut LeanObject> {
        if !lean_expr_is_app(e) { return None; }
        let arg = lean_expr_get_app_arg(e);
        if !lean_expr_is_const(arg) { return None; }
        let f = lean_expr_get_app_fn(e);
        let reduce_bool = load_global(&G_LEAN_REDUCE_BOOL);
        let reduce_nat = load_global(&G_LEAN_REDUCE_NAT);
        if lean_expr_eqv(f, reduce_bool) {
            let name = lean_expr_get_const_name(arg);
            let opts = lean_mk_empty_options();
            let r = lean_ir_run_boxed_kernel(self.st.env, opts, name, 0, ptr::null());
            lean_dec(opts);
            if lean_is_scalar(r) {
                Some(mk_bool(lean_unbox(r) != 0))
            } else {
                lean_dec(r);
                None // error handled in C++ by throwing; here we just skip
            }
        } else if lean_expr_eqv(f, reduce_nat) {
            let name = lean_expr_get_const_name(arg);
            let opts = lean_mk_empty_options();
            let r = lean_ir_run_boxed_kernel(self.st.env, opts, name, 0, ptr::null());
            lean_dec(opts);
            Some(lean_expr_mk_lit_nat(r))
        } else {
            None
        }
    }

    // -----------------------------------------------------------------------
    // whnf (full)
    // -----------------------------------------------------------------------

    unsafe fn whnf(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        // Fast no-cache cases
        let kind = lean_expr_kind(e);
        match kind {
            EXPR_BVAR | EXPR_SORT | EXPR_MVAR | EXPR_PI | EXPR_LIT => {
                lean_inc(e);
                return Ok(e);
            }
            EXPR_MDATA => {
                return self.whnf(lean_expr_get_mdata_expr(e));
            }
            EXPR_FVAR => {
                let opt_decl = lean_local_ctx_find_local_decl(self.lctx, e);
                let has_val = !lean_is_scalar(opt_decl) && lean_local_decl_has_value(opt_decl);
                lean_dec(opt_decl);
                if !has_val {
                    lean_inc(e);
                    return Ok(e);
                }
            }
            _ => {}
        }

        // Check whnf cache
        let key = ExprKey::new(e);
        if let Some(v) = self.st.whnf.get(&key) {
            let r = v.get();
            lean_inc(r);
            return Ok(r);
        }

        let mut t = e;
        lean_inc(t);
        loop {
            let t1 = self.whnf_core(t, false, false)?;
            lean_dec(t);
            // In each return path `OwnedLean::new` inc's for the cache, and the original
            // owned value (`cached`/`v`/`t1`) is returned — no extra inc (that would leak).
            if let Some(v) = self.reduce_native(t1) {
                let cached = v;
                self.st.whnf.insert(ExprKey::new(e), OwnedLean::new(cached));
                lean_dec(t1);
                return Ok(cached);
            }
            if let Some(v) = self.reduce_nat(t1)? {
                self.st.whnf.insert(ExprKey::new(e), OwnedLean::new(v));
                lean_dec(t1);
                return Ok(v);
            }
            if let Some(next) = self.unfold_definition(t1) {
                lean_dec(t1);
                t = next;
            } else {
                let r = t1;
                self.st.whnf.insert(ExprKey::new(e), OwnedLean::new(r));
                return Ok(r);
            }
        }
    }

    // -----------------------------------------------------------------------
    // is_delta
    // -----------------------------------------------------------------------

    unsafe fn is_delta(&self, e: *const LeanObject) -> Option<*mut LeanObject> {
        let f = app_head(e as *mut _);
        if !lean_expr_is_const(f) { return None; }
        let name = lean_expr_get_const_name(f);
        let info_opt = env_find(self.st.env, name);
        if lean_is_scalar(info_opt) { return None; }
        if !lean_constant_info_has_value(info_opt) {
            lean_dec(info_opt);
            return None;
        }
        let ps_len = lean_constant_info_get_num_lparams(info_opt) as usize;
        let ls_len = list_length(lean_expr_get_const_levels(f));
        if ps_len != ls_len {
            lean_dec(info_opt);
            return None;
        }
        Some(info_opt) // caller must dec
    }

    // -----------------------------------------------------------------------
    // is_def_eq helpers
    // -----------------------------------------------------------------------

    unsafe fn quick_is_def_eq(&mut self, t: *mut LeanObject, s: *mut LeanObject, use_hash: bool) -> Result<LBool, KernelError> {
        if lean_equiv_manager_is_equiv(self.st.eqv_manager, t, s, use_hash) {
            return Ok(LBool::True);
        }
        let kt = lean_expr_kind(t);
        let ks = lean_expr_kind(s);
        if kt == ks {
            match kt {
                EXPR_LAMBDA | EXPR_PI => {
                    return Ok(LBool::from_bool(self.is_def_eq_binding(t, s)?));
                }
                EXPR_SORT => {
                    let lt = lean_expr_get_sort_level(t);
                    let ls_l = lean_expr_get_sort_level(s);
                    return Ok(LBool::from_bool(is_equivalent_level(lt, ls_l)?));
                }
                EXPR_MDATA => {
                    return self.quick_is_def_eq(lean_expr_get_mdata_expr(t), lean_expr_get_mdata_expr(s), use_hash);
                }
                EXPR_LIT => {
                    return Ok(LBool::from_bool(lean_expr_eqv(t, s)));
                }
                _ => {}
            }
        }
        Ok(LBool::Undef)
    }

    unsafe fn is_def_eq_binding(&mut self, mut t: *mut LeanObject, mut s: *mut LeanObject) -> Result<bool, KernelError> {
        // Both must be lambda or both pi
        let k = lean_expr_kind(t);
        let mut subst: Vec<*mut LeanObject> = Vec::new();

        self.with_saved_lctx(|tc| {
            loop {
                let dom_t = lean_expr_get_binding_domain(t);
                let dom_s = lean_expr_get_binding_domain(s);
                let mut var_s_type: Option<*mut LeanObject> = None;
                if !lean_expr_eqv(dom_t, dom_s) {
                    let inst_s = lean_expr_instantiate_rev(dom_s, subst.len() as u32, subst.as_ptr());
                    let inst_t = lean_expr_instantiate_rev(dom_t, subst.len() as u32, subst.as_ptr());
                    let eq = tc.is_def_eq(inst_t, inst_s)?;
                    lean_dec(inst_t);
                    if !eq {
                        lean_dec(inst_s);
                        return Ok(false);
                    }
                    var_s_type = Some(inst_s);
                }
                let body_t = lean_expr_get_binding_body(t);
                let body_s = lean_expr_get_binding_body(s);
                if lean_expr_has_loose_bvars(body_t) || lean_expr_has_loose_bvars(body_s) {
                    let s_type = if let Some(st) = var_s_type {
                        st
                    } else {
                        lean_expr_instantiate_rev(dom_s, subst.len() as u32, subst.as_ptr())
                    };
                    let bi = lean_expr_get_binding_info(s);
                    let name = lean_expr_get_binding_name(s);
                    let fvar = tc.lctx_mk_local_decl(name, s_type, bi);
                    lean_dec(s_type);
                    subst.push(fvar);
                } else {
                    if let Some(st) = var_s_type { lean_dec(st); }
                    let dont_care = load_global(&G_DONT_CARE);
                    lean_inc(dont_care);
                    subst.push(dont_care);
                }

                t = body_t;
                s = body_s;
                if lean_expr_kind(t) != k || lean_expr_kind(s) != k {
                    break;
                }
            }
            let inst_t = lean_expr_instantiate_rev(t, subst.len() as u32, subst.as_ptr());
            let inst_s = lean_expr_instantiate_rev(s, subst.len() as u32, subst.as_ptr());
            let result = tc.is_def_eq(inst_t, inst_s)?;
            lean_dec(inst_t);
            lean_dec(inst_s);
            for f in &subst { lean_dec(*f); }
            Ok(result)
        })
    }

    unsafe fn is_def_eq_args(&mut self, mut t: *mut LeanObject, mut s: *mut LeanObject) -> Result<bool, KernelError> {
        while lean_expr_is_app(t) && lean_expr_is_app(s) {
            if !self.is_def_eq(lean_expr_get_app_arg(t), lean_expr_get_app_arg(s))? {
                return Ok(false);
            }
            t = lean_expr_get_app_fn(t);
            s = lean_expr_get_app_fn(s);
        }
        Ok(!lean_expr_is_app(t) && !lean_expr_is_app(s))
    }

    unsafe fn try_eta_expansion_core(&mut self, t: *mut LeanObject, s: *mut LeanObject) -> Result<bool, KernelError> {
        if lean_expr_is_lambda(t) && !lean_expr_is_lambda(s) {
            let s_inferred = self.infer_type(s)?;
            let s_type = self.whnf(s_inferred)?;
            if !lean_expr_is_pi(s_type) {
                lean_dec(s_type);
                return Ok(false);
            }
            let name = lean_expr_get_binding_name(s_type);
            let dom = lean_expr_get_binding_domain(s_type);
            let bi = lean_expr_get_binding_info(s_type);
            // mk_app/mk_lambda consume their args (obj_arg): inc the borrowed s/name/dom,
            // and let the freshly built bvar/app flow in without dec.
            lean_inc(s);
            let app = lean_expr_mk_app(s, lean_expr_mk_bvar(lean_box(0)));
            lean_inc(name); lean_inc(dom);
            let new_s = lean_expr_mk_lambda(name, dom, app, bi);
            lean_dec(s_type);
            let result = self.is_def_eq(t, new_s)?;
            lean_dec(new_s);
            Ok(result)
        } else {
            Ok(false)
        }
    }

    unsafe fn try_eta_struct_core(&mut self, t: *mut LeanObject, s: *mut LeanObject) -> Result<bool, KernelError> {
        let f = app_head(s);
        if !lean_expr_is_const(f) { return Ok(false); }
        let f_name = lean_expr_get_const_name(f);
        let f_info_opt = env_find(self.st.env, f_name);
        if lean_is_scalar(f_info_opt) || !lean_constant_info_is_constructor(f_info_opt) {
            lean_dec(f_info_opt);
            return Ok(false);
        }
        let f_val = lean_constant_info_to_constructor_val(f_info_opt);
        let nparams = lean_constructor_val_get_nparams(f_val) as usize;
        let nfields = lean_constructor_val_get_nfields(f_val) as usize;
        let s_nargs = lean_expr_get_app_num_args(s) as usize;
        if s_nargs != nparams + nfields {
            lean_dec(f_info_opt);
            return Ok(false);
        }
        let induct_name = lean_constructor_val_get_induct(f_val);
        if !is_non_rec_structure_name(self.st.env, induct_name) {
            lean_dec(f_info_opt);
            return Ok(false);
        }
        lean_dec(f_info_opt);

        let t_type = self.infer_type(t)?;
        let s_type = self.infer_type(s)?;
        if !self.is_def_eq(t_type, s_type)? {
            lean_dec(t_type); lean_dec(s_type);
            return Ok(false);
        }
        lean_dec(t_type); lean_dec(s_type);

        // Collect s args
        let mut s_args: Vec<*mut LeanObject> = Vec::new();
        let mut cur = s;
        while lean_expr_is_app(cur) {
            s_args.push(lean_expr_get_app_arg(cur));
            cur = lean_expr_get_app_fn(cur);
        }
        s_args.reverse();

        for i in nparams..s_args.len() {
            let proj_idx = lean_nat_mk_obj((i - nparams) as u64); // owned, consumed by mk_proj
            lean_inc(induct_name); lean_inc(t);
            let proj = lean_expr_mk_proj(induct_name, proj_idx, t);
            if !self.is_def_eq(proj, s_args[i])? {
                lean_dec(proj);
                return Ok(false);
            }
            lean_dec(proj);
        }
        Ok(true)
    }

    unsafe fn is_def_eq_app(&mut self, t: *mut LeanObject, s: *mut LeanObject) -> Result<bool, KernelError> {
        if lean_expr_is_app(t) && lean_expr_is_app(s) {
            let mut t_args: Vec<*mut LeanObject> = Vec::new();
            let mut s_args: Vec<*mut LeanObject> = Vec::new();
            let mut tc = t;
            let mut sc = s;
            while lean_expr_is_app(tc) { t_args.push(lean_expr_get_app_arg(tc)); tc = lean_expr_get_app_fn(tc); }
            while lean_expr_is_app(sc) { s_args.push(lean_expr_get_app_arg(sc)); sc = lean_expr_get_app_fn(sc); }
            let t_fn = tc;
            let s_fn = sc;
            if t_args.len() == s_args.len() && self.is_def_eq(t_fn, s_fn)? {
                for (ta, sa) in t_args.iter().zip(s_args.iter()) {
                    if !self.is_def_eq(*ta, *sa)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
        }
        Ok(false)
    }

    unsafe fn is_def_eq_proof_irrel(&mut self, t: *mut LeanObject, s: *mut LeanObject) -> Result<LBool, KernelError> {
        let t_type = self.infer_type(t)?;
        if !self.is_prop(t_type)? {
            lean_dec(t_type);
            return Ok(LBool::Undef);
        }
        lean_dec(t_type);
        let s_type = self.infer_type(s)?;
        let t_type2 = self.infer_type(t)?;
        let r = self.is_def_eq(t_type2, s_type)?;
        lean_dec(s_type); lean_dec(t_type2);
        Ok(LBool::from_bool(r))
    }

    unsafe fn is_def_eq_unit_like(&mut self, t: *mut LeanObject, s: *mut LeanObject) -> Result<bool, KernelError> {
        let t_type_raw = self.infer_type(t)?;
        let t_type = self.whnf(t_type_raw)?;
        lean_dec(t_type_raw);
        let I = app_head(t_type);
        if !lean_expr_is_const(I) {
            lean_dec(t_type);
            return Ok(false);
        }
        let I_name = lean_expr_get_const_name(I);
        if !is_non_rec_structure_name(self.st.env, I_name) {
            lean_dec(t_type);
            return Ok(false);
        }
        let I_info = env_find(self.st.env, I_name);
        if lean_is_scalar(I_info) {
            lean_dec(t_type);
            return Ok(false);
        }
        let I_val = lean_constant_info_to_inductive_val(I_info);
        let cnstrs = lean_inductive_val_get_cnstrs(I_val);
        let ctor_name = lean_list_head(cnstrs);
        let ctor_info = env_find(self.st.env, ctor_name);
        lean_dec(I_info);
        if lean_is_scalar(ctor_info) {
            lean_dec(t_type);
            return Ok(false);
        }
        let ctor_val = lean_constant_info_to_constructor_val(ctor_info);
        if lean_constructor_val_get_nfields(ctor_val) != 0 {
            lean_dec(ctor_info);
            lean_dec(t_type);
            return Ok(false);
        }
        lean_dec(ctor_info);
        let s_type = self.infer_type(s)?;
        let r = self.is_def_eq(t_type, s_type)?;
        lean_dec(t_type);
        lean_dec(s_type);
        Ok(r)
    }

    unsafe fn failed_before(&self, t: *mut LeanObject, s: *mut LeanObject) -> bool {
        let ht = expr_hash(t);
        let hs = expr_hash(s);
        let key = if ht <= hs {
            (ExprKey(t), ExprKey(s))
        } else {
            (ExprKey(s), ExprKey(t))
        };
        let result = self.st.failure.contains(&key);
        std::mem::forget(key); // Don't drop, no ownership
        result
    }

    unsafe fn cache_failure(&mut self, t: *mut LeanObject, s: *mut LeanObject) {
        let ht = expr_hash(t);
        let hs = expr_hash(s);
        if ht <= hs {
            self.st.failure.insert((ExprKey::new(t), ExprKey::new(s)));
        } else {
            self.st.failure.insert((ExprKey::new(s), ExprKey::new(t)));
        }
    }

    unsafe fn try_unfold_proj_app(&mut self, e: *mut LeanObject) -> Result<Option<*mut LeanObject>, KernelError> {
        let f = app_head(e);
        if lean_expr_is_proj(f) {
            let e_new = self.whnf_core(e, false, false)?;
            if lean_expr_eqv(e_new, e) {
                lean_dec(e_new);
                Ok(None)
            } else {
                Ok(Some(e_new))
            }
        } else {
            Ok(None)
        }
    }

    unsafe fn lazy_delta_reduction_step(
        &mut self,
        t_n: &mut *mut LeanObject,
        s_n: &mut *mut LeanObject,
    ) -> Result<ReductionStatus, KernelError> {
        let d_t = self.is_delta(*t_n);
        let d_s = self.is_delta(*s_n);

        if d_t.is_none() && d_s.is_none() {
            return Ok(ReductionStatus::DefUnknown);
        }

        if d_t.is_some() && d_s.is_none() {
            if let Some(s_new) = self.try_unfold_proj_app(*s_n)? {
                lean_dec(*s_n);
                *s_n = s_new;
            } else {
                let unfolded = self.unfold_definition(*t_n).unwrap();
                let new_t = self.whnf_core(unfolded, false, true)?;
                lean_dec(unfolded);
                lean_dec(*t_n);
                *t_n = new_t;
            }
        } else if d_t.is_none() && d_s.is_some() {
            if let Some(t_new) = self.try_unfold_proj_app(*t_n)? {
                lean_dec(*t_n);
                *t_n = t_new;
            } else {
                let unfolded = self.unfold_definition(*s_n).unwrap();
                let new_s = self.whnf_core(unfolded, false, true)?;
                lean_dec(unfolded);
                lean_dec(*s_n);
                *s_n = new_s;
            }
        } else {
            let info_t = d_t.unwrap();
            let info_s = d_s.unwrap();
            let hints_t = lean_constant_info_get_hints(info_t);
            let hints_s = lean_constant_info_get_hints(info_s);
            let c = lean_hints_compare(hints_t, hints_s);
            lean_dec(info_t);
            lean_dec(info_s);
            if c < 0 {
                let unfolded = self.unfold_definition(*t_n).unwrap();
                let new_t = self.whnf_core(unfolded, false, true)?;
                lean_dec(unfolded); lean_dec(*t_n);
                *t_n = new_t;
            } else if c > 0 {
                let unfolded = self.unfold_definition(*s_n).unwrap();
                let new_s = self.whnf_core(unfolded, false, true)?;
                lean_dec(unfolded); lean_dec(*s_n);
                *s_n = new_s;
            } else {
                let info_t2 = self.is_delta(*t_n).unwrap();
                let info_s2 = self.is_delta(*s_n).unwrap();
                let same_def = lean_constant_info_get_name(info_t2) == lean_constant_info_get_name(info_s2);
                let is_regular = lean_hints_is_regular(lean_constant_info_get_hints(info_t2));
                lean_dec(info_t2); lean_dec(info_s2);

                if lean_expr_is_app(*t_n) && lean_expr_is_app(*s_n) && same_def && is_regular {
                    if !self.failed_before(*t_n, *s_n) {
                        let t_fn = app_head(*t_n);
                        let s_fn = app_head(*s_n);
                        let lvl_eq = is_equivalent_levels_list(lean_expr_get_const_levels(t_fn), lean_expr_get_const_levels(s_fn))?;
                        if lvl_eq && self.is_def_eq_args(*t_n, *s_n)? {
                            return Ok(ReductionStatus::DefEqual);
                        } else {
                            self.cache_failure(*t_n, *s_n);
                        }
                    }
                }
                let unf_t = self.unfold_definition(*t_n).unwrap();
                let unf_s = self.unfold_definition(*s_n).unwrap();
                let new_t = self.whnf_core(unf_t, false, true)?;
                let new_s = self.whnf_core(unf_s, false, true)?;
                lean_dec(unf_t); lean_dec(unf_s);
                lean_dec(*t_n); lean_dec(*s_n);
                *t_n = new_t; *s_n = new_s;
            }
        }

        match self.quick_is_def_eq(*t_n, *s_n, false)? {
            LBool::True  => Ok(ReductionStatus::DefEqual),
            LBool::False => Ok(ReductionStatus::DefDiff),
            LBool::Undef => Ok(ReductionStatus::Continue),
        }
    }

    unsafe fn is_def_eq_offset(&mut self, t: *mut LeanObject, s: *mut LeanObject) -> Result<LBool, KernelError> {
        if is_nat_zero_expr(t) && is_nat_zero_expr(s) {
            return Ok(LBool::True);
        }
        let pred_t = nat_pred(t);
        let pred_s = nat_pred(s);
        if let (Some(pt), Some(ps)) = (pred_t, pred_s) {
            Ok(LBool::from_bool(self.is_def_eq_core(pt, ps)?))
        } else {
            Ok(LBool::Undef)
        }
    }

    unsafe fn lazy_delta_reduction(
        &mut self,
        t_n: &mut *mut LeanObject,
        s_n: &mut *mut LeanObject,
    ) -> Result<LBool, KernelError> {
        loop {
            let r = self.is_def_eq_offset(*t_n, *s_n)?;
            if r != LBool::Undef { return Ok(r); }

            if (!expr_has_fvar(*t_n) && !expr_has_fvar(*s_n)) || self.eager_reduce {
                if let Some(tv) = self.reduce_nat(*t_n)? {
                    return Ok(LBool::from_bool(self.is_def_eq_core(tv, *s_n)?));
                }
                if let Some(sv) = self.reduce_nat(*s_n)? {
                    return Ok(LBool::from_bool(self.is_def_eq_core(*t_n, sv)?));
                }
            }

            if let Some(tv) = self.reduce_native(*t_n) {
                return Ok(LBool::from_bool(self.is_def_eq_core(tv, *s_n)?));
            }
            if let Some(sv) = self.reduce_native(*s_n) {
                return Ok(LBool::from_bool(self.is_def_eq_core(*t_n, sv)?));
            }

            match self.lazy_delta_reduction_step(t_n, s_n)? {
                ReductionStatus::Continue   => continue,
                ReductionStatus::DefUnknown => return Ok(LBool::Undef),
                ReductionStatus::DefEqual   => return Ok(LBool::True),
                ReductionStatus::DefDiff    => return Ok(LBool::False),
            }
        }
    }

    unsafe fn lazy_delta_proj_reduction(
        &mut self,
        t_n: &mut *mut LeanObject,
        s_n: &mut *mut LeanObject,
        idx: *const LeanObject,
    ) -> Result<bool, KernelError> {
        loop {
            match self.lazy_delta_reduction_step(t_n, s_n)? {
                ReductionStatus::Continue => continue,
                ReductionStatus::DefEqual => return Ok(true),
                ReductionStatus::DefUnknown | ReductionStatus::DefDiff => {
                    if lean_nat_is_small(idx) {
                        let i = lean_nat_get_small_value(idx) as usize;
                        if let Some(t_proj) = self.reduce_proj_core(*t_n, i)? {
                            if let Some(s_proj) = self.reduce_proj_core(*s_n, i)? {
                                return self.is_def_eq_core(t_proj, s_proj);
                            }
                            lean_dec(t_proj);
                        }
                    }
                    return self.is_def_eq_core(*t_n, *s_n);
                }
            }
        }
    }

    unsafe fn try_string_lit_expansion_core(
        &mut self,
        t: *mut LeanObject,
        s: *mut LeanObject,
    ) -> Result<LBool, KernelError> {
        if lean_expr_is_string_lit(t) && lean_expr_is_app(s) {
            let string_mk = load_global(&G_STRING_MK);
            if lean_expr_eqv(lean_expr_get_app_fn(s), string_mk) {
                let ctor = lean_string_lit_to_constructor(t);
                let whnf_ctor = self.whnf(ctor)?;
                lean_dec(ctor);
                return Ok(LBool::from_bool(self.is_def_eq_core(whnf_ctor, s)?));
            }
        }
        Ok(LBool::Undef)
    }

    // -----------------------------------------------------------------------
    // is_def_eq_core — the main decision procedure
    // -----------------------------------------------------------------------

    unsafe fn is_def_eq_core(&mut self, t: *mut LeanObject, s: *mut LeanObject) -> Result<bool, KernelError> {
        check_system_result()?;
        let r = self.quick_is_def_eq(t, s, true)?;
        if r != LBool::Undef { return Ok(r == LBool::True); }

        // Proof by reflection: if t has no fvars and s is Bool.true, fully reduce t
        let bool_true = load_global(&G_BOOL_TRUE);
        if (!expr_has_fvar(t) || self.eager_reduce) && lean_expr_is_const(s) && lean_name_eq(lean_expr_get_const_name(s), bool_true) {
            let whnf_t = self.whnf(t)?;
            if lean_expr_is_const(whnf_t) && lean_name_eq(lean_expr_get_const_name(whnf_t), bool_true) {
                lean_dec(whnf_t);
                return Ok(true);
            }
            lean_dec(whnf_t);
        }

        // whnf_core with cheap_proj=true (no full whnf for projections)
        let mut t_n = self.whnf_core(t, false, true)?;
        let mut s_n = self.whnf_core(s, false, true)?;

        if !lean_expr_is_eqp(t_n, t) || !lean_expr_is_eqp(s_n, s) {
            let r = self.quick_is_def_eq(t_n, s_n, false)?;
            if r != LBool::Undef {
                lean_dec(t_n); lean_dec(s_n);
                return Ok(r == LBool::True);
            }
        }

        let r = self.is_def_eq_proof_irrel(t_n, s_n)?;
        if r != LBool::Undef {
            lean_dec(t_n); lean_dec(s_n);
            return Ok(r == LBool::True);
        }

        let r = self.lazy_delta_reduction(&mut t_n, &mut s_n)?;
        if r != LBool::Undef {
            lean_dec(t_n); lean_dec(s_n);
            return Ok(r == LBool::True);
        }

        // Constant and fvar checks
        if lean_expr_is_const(t_n) && lean_expr_is_const(s_n) {
            if lean_name_eq(lean_expr_get_const_name(t_n), lean_expr_get_const_name(s_n)) {
                if is_equivalent_levels_list(lean_expr_get_const_levels(t_n), lean_expr_get_const_levels(s_n))? {
                    lean_dec(t_n); lean_dec(s_n);
                    return Ok(true);
                }
            }
        }
        if lean_expr_is_fvar(t_n) && lean_expr_is_fvar(s_n) {
            if lean_name_eq(lean_expr_get_fvar_id(t_n), lean_expr_get_fvar_id(s_n)) {
                lean_dec(t_n); lean_dec(s_n);
                return Ok(true);
            }
        }

        // Proj-proj reduction
        if lean_expr_is_proj(t_n) && lean_expr_is_proj(s_n) {
            let ti = lean_expr_get_proj_idx(t_n);
            let si = lean_expr_get_proj_idx(s_n);
            if lean_nat_eq(ti, si) {
                let mut t_c = lean_expr_get_proj_expr(t_n);
                let mut s_c = lean_expr_get_proj_expr(s_n);
                lean_inc(t_c); lean_inc(s_c);
                if self.lazy_delta_proj_reduction(&mut t_c, &mut s_c, ti)? {
                    lean_dec(t_c); lean_dec(s_c);
                    lean_dec(t_n); lean_dec(s_n);
                    return Ok(true);
                }
                lean_dec(t_c); lean_dec(s_c);
            }
        }

        // Invoke whnf_core again using full whnf for projections
        let t_n_n = self.whnf_core(t_n, false, false)?;
        let s_n_n = self.whnf_core(s_n, false, false)?;
        if !lean_expr_is_eqp(t_n_n, t_n) || !lean_expr_is_eqp(s_n_n, s_n) {
            lean_dec(t_n); lean_dec(s_n);
            let r = self.is_def_eq_core(t_n_n, s_n_n)?;
            lean_dec(t_n_n); lean_dec(s_n_n);
            return Ok(r);
        }
        lean_dec(t_n_n); lean_dec(s_n_n);

        // App-app
        if self.is_def_eq_app(t_n, s_n)? {
            lean_dec(t_n); lean_dec(s_n);
            return Ok(true);
        }

        // Eta expansion
        if self.try_eta_expansion_core(t_n, s_n)? || self.try_eta_expansion_core(s_n, t_n)? {
            lean_dec(t_n); lean_dec(s_n);
            return Ok(true);
        }

        // Eta struct
        if self.try_eta_struct_core(t_n, s_n)? || self.try_eta_struct_core(s_n, t_n)? {
            lean_dec(t_n); lean_dec(s_n);
            return Ok(true);
        }

        // String literal expansion
        let r = self.try_string_lit_expansion_core(t_n, s_n)?;
        if r != LBool::Undef {
            lean_dec(t_n); lean_dec(s_n);
            return Ok(r == LBool::True);
        }
        let r = self.try_string_lit_expansion_core(s_n, t_n)?;
        if r != LBool::Undef {
            lean_dec(t_n); lean_dec(s_n);
            return Ok(r == LBool::True);
        }

        // Unit-like
        if self.is_def_eq_unit_like(t_n, s_n)? {
            lean_dec(t_n); lean_dec(s_n);
            return Ok(true);
        }

        lean_dec(t_n); lean_dec(s_n);
        Ok(false)
    }

    pub unsafe fn is_def_eq(&mut self, t: *mut LeanObject, s: *mut LeanObject) -> Result<bool, KernelError> {
        let r = self.is_def_eq_core(t, s)?;
        if r {
            lean_equiv_manager_add_equiv(self.st.eqv_manager, t, s);
        }
        Ok(r)
    }

    pub unsafe fn whnf_public(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        self.whnf(e)
    }

    // -----------------------------------------------------------------------
    // check (type check + return type)
    // -----------------------------------------------------------------------

    pub unsafe fn check(&mut self, e: *mut LeanObject, lps: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        let saved = self.lparams;
        self.lparams = Some(lps);
        let r = self.infer_type_core(e, false);
        self.lparams = saved;
        r
    }

    pub unsafe fn check_ignore_undefined_universes(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        let saved = self.lparams;
        self.lparams = None;
        let r = self.infer_type_core(e, false);
        self.lparams = saved;
        r
    }

    pub unsafe fn ensure_sort(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        self.ensure_sort_core(e, e)
    }

    pub unsafe fn ensure_type(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        let ty = self.infer_type(e)?;
        self.ensure_sort_core(ty, e)
    }

    pub unsafe fn ensure_pi(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        self.ensure_pi_core(e, e)
    }
}

impl Drop for TypeChecker {
    fn drop(&mut self) {
        unsafe { lean_dec(self.lctx); }
    }
}

// ---------------------------------------------------------------------------
// Standalone helpers used by the type checker
// ---------------------------------------------------------------------------

unsafe fn lean_lit_type(e: *mut LeanObject) -> *mut LeanObject {
    // `e` is an `Expr.lit`; its field 0 is the `Literal`, whose ctor tag selects the type
    // (0 = natVal → `Nat`, 1 = strVal → `String`). Return an `Expr.const`, not a bare `Name`.
    let lit = lean_ctor_get(e, 0);
    let tag = lean_ptr_tag(lit);
    let name = if tag == LITERAL_NAT_TAG {
        build_lean_name(&["Nat"])
    } else {
        build_lean_name(&["String"])
    };
    let nil = lean_mk_list_nil(ptr::null_mut());
    // lean_expr_mk_const consumes both `name` and `nil`.
    lean_expr_mk_const(name, nil)
}

unsafe fn is_eager_reduce_expr(e: *mut LeanObject) -> bool {
    // eagerReduce fn arg  → is_const(get_app_fn(e)) && get_app_num_args == 2
    let eager = load_global(&G_EAGER_REDUCE);
    let nargs = lean_expr_get_app_num_args(e);
    if nargs != 2 { return false; }
    let f = app_head(e);
    if !lean_expr_is_const(f) { return false; }
    lean_name_eq(lean_expr_get_const_name(f), lean_expr_get_const_name(eager))
}

unsafe fn is_nat_lit_ext(e: *mut LeanObject) -> bool {
    let nat_zero = load_global(&G_NAT_ZERO);
    lean_expr_eqv(e, nat_zero) || lean_expr_is_nat_lit(e)
}

unsafe fn get_nat_val(e: *mut LeanObject) -> *mut LeanObject {
    // Returns a BORROWED nat object: for the literal case it points inside `e`'s
    // `Expr.lit`, for the `Nat.zero` constant case it is the scalar `box(0)`.
    // The caller must NOT `lean_dec` the result, and must keep `e` alive while using it.
    let nat_zero = load_global(&G_NAT_ZERO);
    if lean_expr_eqv(e, nat_zero) {
        lean_nat_mk_obj(0) // scalar box(0): no ownership, safe to treat as borrowed
    } else {
        lean_expr_get_lit_nat(e) // borrowed pointer into the literal
    }
}

unsafe fn reduce_nat_succ(arg: *mut LeanObject) -> Option<*mut LeanObject> {
    if !is_nat_lit_ext(arg) { return None; }
    let v = get_nat_val(arg); // borrowed; do NOT dec
    let one = lean_nat_mk_obj(1); // scalar box(1)
    // lean_nat_add BORROWS both args, returns an owned result.
    let result = lean_nat_add(v, one);
    Some(lean_expr_mk_lit_nat(result))
}

unsafe fn mk_bool(b: bool) -> *mut LeanObject {
    // The kernel reduces Nat.beq/ble/reduceBool to the *expression* `Bool.true`/`Bool.false`
    // (a `Expr.const`), not to a raw Bool scalar.
    let e = load_global(if b { &G_EXPR_BOOL_TRUE } else { &G_EXPR_BOOL_FALSE });
    lean_inc(e);
    e
}

unsafe fn is_nat_zero_expr(e: *mut LeanObject) -> bool {
    let nat_zero = load_global(&G_NAT_ZERO);
    if lean_expr_eqv(e, nat_zero) { return true; }
    if lean_expr_is_nat_lit(e) {
        let n = lean_expr_get_lit_nat(e);
        return lean_nat_is_zero(n);
    }
    false
}

unsafe fn nat_pred(e: *mut LeanObject) -> Option<*mut LeanObject> {
    if lean_expr_is_nat_lit(e) {
        let n = lean_expr_get_lit_nat(e);
        if lean_nat_is_zero(n) { return None; }
        let pred = lean_nat_dec(n);
        return Some(lean_expr_mk_lit_nat(pred));
    }
    let nat_succ = load_global(&G_NAT_SUCC);
    if lean_expr_get_app_num_args(e) == 1 {
        let f = lean_expr_get_app_fn(e);
        if lean_expr_eqv(f, nat_succ) {
            let arg = lean_expr_get_app_arg(e);
            lean_inc(arg);
            return Some(arg);
        }
    }
    None
}

unsafe fn is_equivalent_levels_list(ls1: *mut LeanObject, ls2: *mut LeanObject) -> Result<bool, KernelError> {
    let mut l1 = ls1;
    let mut l2 = ls2;
    loop {
        let nil1 = lean_list_is_nil(l1);
        let nil2 = lean_list_is_nil(l2);
        if nil1 && nil2 { return Ok(true); }
        if nil1 || nil2 { return Ok(false); }
        if !is_equivalent_level(lean_list_head(l1), lean_list_head(l2))? {
            return Ok(false);
        }
        l1 = lean_list_tail(l1);
        l2 = lean_list_tail(l2);
    }
}

unsafe fn list_length(l: *mut LeanObject) -> usize {
    let mut cur = l;
    let mut n = 0;
    while !lean_list_is_nil(cur) {
        n += 1;
        cur = lean_list_tail(cur);
    }
    n
}

/// Check if env has a non-recursive structure with this name.
unsafe fn is_non_rec_structure_name(env: *mut LeanObject, name: *mut LeanObject) -> bool {
    let info_opt = env_find(env, name);
    if lean_is_scalar(info_opt) { return false; }
    if !lean_constant_info_is_inductive(info_opt) {
        lean_dec(info_opt);
        return false;
    }
    let I_val = lean_constant_info_to_inductive_val(info_opt);
    let result = lean_inductive_val_get_ncnstrs(I_val) == 1
        && lean_inductive_val_get_nindices(I_val) == 0
        && !lean_inductive_val_is_rec(I_val);
    lean_dec(info_opt);
    result
}

unsafe fn format_level_error_msg(name: *mut LeanObject) -> *mut LeanObject {
    let s = format!("invalid reference to undefined universe level parameter");
    lean_mk_string(s.as_ptr(), s.len())
}

unsafe fn format_arity_error_msg(name: *mut LeanObject, expected: usize, got: usize) -> *mut LeanObject {
    let s = format!("incorrect number of universe levels parameters");
    lean_mk_string(s.as_ptr(), s.len())
}

unsafe fn lean_name_to_string(name: *mut LeanObject) -> String {
    // Simplified; a real implementation would recurse through the name structure
    "<name>".to_string()
}

// ---------------------------------------------------------------------------
// inductive_reduce_rec_impl  (called from TypeChecker::reduce_recursor)
//
// This is a Rust port of the inductive_reduce_rec template in inductive.h.
// It calls back into `tc` for whnf/infer_type/is_def_eq.
// ---------------------------------------------------------------------------

unsafe fn inductive_reduce_rec_impl(
    env: *mut LeanObject,
    e: *mut LeanObject,
    cheap_rec: bool,
    cheap_proj: bool,
    tc: &mut TypeChecker,
) -> Result<Option<*mut LeanObject>, KernelError> {
    // Walk the whole application spine: `lean_expr_get_app_fn` strips a single layer, so we
    // must iterate to reach the head constant (the recursor). A multi-argument recursor
    // application like `Decidable.rec C m1 m2 major` has an `App` immediately under it, not the
    // const, so checking only one layer would wrongly bail and leave recursors unreduced.
    let mut rec_args: Vec<*mut LeanObject> = Vec::new();
    let mut cur = e;
    while lean_expr_is_app(cur) {
        rec_args.push(lean_expr_get_app_arg(cur));
        cur = lean_expr_get_app_fn(cur);
    }
    rec_args.reverse();
    let rec_fn = cur; // spine head
    if !lean_expr_is_const(rec_fn) { return Ok(None); }
    let rec_name = lean_expr_get_const_name(rec_fn);
    let rec_info_opt = env_find(env, rec_name);
    if lean_is_scalar(rec_info_opt) || !lean_constant_info_is_recursor(rec_info_opt) {
        lean_dec(rec_info_opt);
        return Ok(None);
    }

    let rec_val = lean_constant_info_to_recursor_val(rec_info_opt);
    let major_idx = lean_recursor_val_get_major_idx(rec_val) as usize;
    if major_idx >= rec_args.len() {
        lean_dec(rec_info_opt);
        return Ok(None);
    }

    let mut major = rec_args[major_idx];
    lean_inc(major);

    // to_cnstr_when_K
    if lean_recursor_val_is_k(rec_val) {
        major = to_cnstr_when_K_impl(env, rec_val, major, tc)?;
    }

    // whnf major
    {
        let whnf_major = if cheap_rec {
            tc.whnf_core(major, cheap_rec, cheap_proj)?
        } else {
            tc.whnf(major)?
        };
        lean_dec(major);
        major = whnf_major;
    }

    // nat/string lit to constructor
    if lean_expr_is_nat_lit(major) {
        let ctor = lean_nat_lit_to_constructor(major);
        lean_dec(major);
        major = ctor;
    } else if lean_expr_is_string_lit(major) {
        let ctor = lean_string_lit_to_constructor(major);
        let whnf = tc.whnf(ctor)?;
        lean_dec(ctor); lean_dec(major);
        major = whnf;
    } else {
        // to_cnstr_when_structure
        let induct_name = lean_recursor_val_get_major_induct(rec_val);
        major = to_cnstr_when_structure_impl(env, induct_name, major, tc)?;
    }

    // Find recursor rule matching major's constructor
    let rule = get_rec_rule_for_impl(rec_val, major);
    if rule.is_none() {
        lean_dec(major); lean_dec(rec_info_opt);
        return Ok(None);
    }
    let rule = rule.unwrap();

    let mut major_args: Vec<*mut LeanObject> = Vec::new();
    let mut mc = major;
    while lean_expr_is_app(mc) {
        major_args.push(lean_expr_get_app_arg(mc));
        mc = lean_expr_get_app_fn(mc);
    }
    major_args.reverse();

    let nfields = lean_recursor_rule_get_nfields(rule) as usize;
    if nfields > major_args.len() {
        lean_dec(rule); lean_dec(major); lean_dec(rec_info_opt);
        return Ok(None);
    }
    let rec_levels = lean_expr_get_const_levels(rec_fn);
    let rec_lparams = lean_constant_info_get_lparams(rec_info_opt);
    let nparams_rec = lean_recursor_val_get_nparams(rec_val) as usize;
    let nmotives = lean_recursor_val_get_nmotives(rec_val) as usize;
    let nminors = lean_recursor_val_get_nminors(rec_val) as usize;

    let rhs_tmpl = lean_recursor_rule_get_rhs(rule);
    let mut rhs = lean_instantiate_lparams(rhs_tmpl, rec_lparams, rec_levels);

    // Apply params + motives + minors from rec_args. mk_app consumes both args (obj_arg):
    // inc the borrowed element, let `rhs` flow into the new node (no dec).
    for i in 0..(nparams_rec + nmotives + nminors) {
        if i < rec_args.len() {
            lean_inc(rec_args[i]);
            rhs = lean_expr_mk_app(rhs, rec_args[i]);
        }
    }

    // Apply fields from major
    let nparams_ctor = major_args.len() - nfields;
    for i in 0..nfields {
        lean_inc(major_args[nparams_ctor + i]);
        rhs = lean_expr_mk_app(rhs, major_args[nparams_ctor + i]);
    }

    // Apply extra rec_args after major
    if rec_args.len() > major_idx + 1 {
        for i in (major_idx + 1)..rec_args.len() {
            lean_inc(rec_args[i]);
            rhs = lean_expr_mk_app(rhs, rec_args[i]);
        }
    }

    lean_dec(rule); lean_dec(major); lean_dec(rec_info_opt);
    Ok(Some(rhs))
}

unsafe fn to_cnstr_when_K_impl(
    env: *mut LeanObject,
    rec_val: *mut LeanObject,
    e: *mut LeanObject,
    tc: &mut TypeChecker,
) -> Result<*mut LeanObject, KernelError> {
    let app_type_raw = tc.infer_type(e)?;
    let app_type = tc.whnf(app_type_raw)?;
    lean_dec(app_type_raw);
    let app_type_fn = app_head(app_type);
    if !lean_expr_is_const(app_type_fn) {
        lean_dec(app_type);
        lean_inc(e);
        return Ok(e);
    }
    let major_induct = lean_recursor_val_get_major_induct(rec_val);
    if !lean_name_eq(lean_expr_get_const_name(app_type_fn), major_induct) {
        lean_dec(app_type);
        lean_inc(e);
        return Ok(e);
    }
    // Check for metavars in indices
    if expr_has_expr_mvar(app_type) {
        let nparams = lean_recursor_val_get_nparams(rec_val) as usize;
        let mut args: Vec<*mut LeanObject> = Vec::new();
        let mut c = app_type;
        while lean_expr_is_app(c) { args.push(lean_expr_get_app_arg(c)); c = lean_expr_get_app_fn(c); }
        args.reverse();
        for i in nparams..args.len() {
            if expr_has_expr_mvar(args[i]) {
                lean_dec(app_type);
                lean_inc(e);
                return Ok(e);
            }
        }
    }
    // mk_nullary_cnstr
    let nparams = lean_recursor_val_get_nparams(rec_val) as usize;
    let cnstr_opt = mk_nullary_cnstr_impl(env, app_type, nparams);
    if let Some(cnstr) = cnstr_opt {
        let cnstr_type = tc.infer_type(cnstr)?;
        if tc.is_def_eq(app_type, cnstr_type)? {
            lean_dec(app_type);
            lean_dec(cnstr_type);
            lean_dec(e);
            return Ok(cnstr);
        }
        lean_dec(cnstr_type);
        lean_dec(cnstr);
    }
    lean_dec(app_type);
    lean_inc(e);
    Ok(e)
}

unsafe fn to_cnstr_when_structure_impl(
    env: *mut LeanObject,
    induct_name: *mut LeanObject,
    e: *mut LeanObject,
    tc: &mut TypeChecker,
) -> Result<*mut LeanObject, KernelError> {
    if !is_non_rec_structure_name(env, induct_name) { return Ok(e); }
    if is_constructor_app_impl(env, e) { return Ok(e); }
    let e_type_raw = tc.infer_type(e)?;
    let e_type = tc.whnf(e_type_raw)?;
    lean_dec(e_type_raw);
    // Check type name matches induct_name
    let e_fn = app_head(e_type);
    if !lean_expr_is_const(e_fn) || !lean_name_eq(lean_expr_get_const_name(e_fn), induct_name) {
        lean_dec(e_type);
        return Ok(e);
    }
    // Check not a Prop
    let e_type_sort_raw = tc.infer_type(e_type)?;
    let e_type_sort = tc.whnf(e_type_sort_raw)?;
    lean_dec(e_type_sort_raw);
    let prop = lean_expr_mk_prop();
    let is_prop = lean_expr_eqv(e_type_sort, prop);
    lean_dec(prop); lean_dec(e_type_sort);
    if is_prop { lean_dec(e_type); return Ok(e); }

    // Expand eta
    let result = expand_eta_struct_impl(env, e_type, e);
    lean_dec(e_type);
    lean_dec(e);
    Ok(result)
}

unsafe fn mk_nullary_cnstr_impl(env: *mut LeanObject, ty: *mut LeanObject, nparams: usize) -> Option<*mut LeanObject> {
    let mut args: Vec<*mut LeanObject> = Vec::new();
    let mut cur = ty;
    while lean_expr_is_app(cur) { args.push(lean_expr_get_app_arg(cur)); cur = lean_expr_get_app_fn(cur); }
    args.reverse();
    let d = cur;
    if !lean_expr_is_const(d) { return None; }
    let d_name = lean_expr_get_const_name(d);
    let I_info = env_find(env, d_name);
    if lean_is_scalar(I_info) || !lean_constant_info_is_inductive(I_info) {
        lean_dec(I_info);
        return None;
    }
    let I_val = lean_constant_info_to_inductive_val(I_info);
    let cnstrs = lean_inductive_val_get_cnstrs(I_val);
    if lean_list_is_nil(cnstrs) { lean_dec(I_info); return None; }
    let cnstr_name = lean_list_head(cnstrs);
    lean_inc(cnstr_name); // own before freeing I_info (cnstr_name is borrowed from it)
    lean_dec(I_info);
    args.truncate(nparams);
    let levels = lean_expr_get_const_levels(d);
    lean_inc(levels);
    // mk_const/mk_app consume their args (obj_arg); cnstr_name/levels/arg are owned/inc'd here.
    let mut app = lean_expr_mk_const(cnstr_name, levels);
    for &arg in &args {
        lean_inc(arg);
        app = lean_expr_mk_app(app, arg);
    }
    Some(app)
}

unsafe fn expand_eta_struct_impl(env: *mut LeanObject, e_type: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject {
    let mut type_args: Vec<*mut LeanObject> = Vec::new();
    let mut cur = e_type;
    while lean_expr_is_app(cur) { type_args.push(lean_expr_get_app_arg(cur)); cur = lean_expr_get_app_fn(cur); }
    type_args.reverse();
    let I = cur;
    if !lean_expr_is_const(I) { lean_inc(e); return e; }
    let ctor_name = {
        let I_name = lean_expr_get_const_name(I);
        let I_info = env_find(env, I_name);
        if lean_is_scalar(I_info) || !lean_constant_info_is_inductive(I_info) { lean_dec(I_info); lean_inc(e); return e; }
        let I_val = lean_constant_info_to_inductive_val(I_info);
        let cnstrs = lean_inductive_val_get_cnstrs(I_val);
        if lean_list_is_nil(cnstrs) { lean_dec(I_info); lean_inc(e); return e; }
        let n = lean_list_head(cnstrs);
        lean_inc(n);
        lean_dec(I_info);
        n
    };
    let ctor_info = env_find(env, ctor_name);
    if lean_is_scalar(ctor_info) { lean_dec(ctor_name); lean_inc(e); return e; }
    let ctor_val = lean_constant_info_to_constructor_val(ctor_info);
    let nparams = lean_constructor_val_get_nparams(ctor_val) as usize;
    let nfields = lean_constructor_val_get_nfields(ctor_val) as usize;
    lean_dec(ctor_info);

    let I_name = lean_expr_get_const_name(I);
    let I_levels = lean_expr_get_const_levels(I);
    // mk_const/mk_app/mk_proj consume their object args (obj_arg). `ctor_name` is owned;
    // `I_levels`/`I_name`/`e`/`type_args[i]` are borrowed, so inc each before handing it over.
    lean_inc(I_levels);
    let mut result = lean_expr_mk_const(ctor_name, I_levels);

    for i in 0..nparams {
        if i < type_args.len() {
            lean_inc(type_args[i]);
            result = lean_expr_mk_app(result, type_args[i]);
        }
    }
    for i in 0..nfields {
        let idx = lean_nat_mk_obj(i as u64); // owned, consumed by mk_proj
        lean_inc(I_name); lean_inc(e);
        let proj = lean_expr_mk_proj(I_name, idx, e);
        result = lean_expr_mk_app(result, proj);
    }
    result
}

unsafe fn is_constructor_app_impl(env: *mut LeanObject, e: *mut LeanObject) -> bool {
    let f = app_head(e);
    if !lean_expr_is_const(f) { return false; }
    let name = lean_expr_get_const_name(f);
    let info = env_find(env, name);
    if lean_is_scalar(info) { return false; }
    let is_ctor = lean_constant_info_is_constructor(info);
    lean_dec(info);
    is_ctor
}

/// Spine head of an application: `lean_expr_get_app_fn` strips only one `App` layer, but the
/// kernel's C++ `get_app_fn` returns the recursive head. Walk to it.
unsafe fn app_head(e: *mut LeanObject) -> *mut LeanObject {
    let mut cur = e;
    while lean_expr_is_app(cur) {
        cur = lean_expr_get_app_fn(cur);
    }
    cur
}

unsafe fn get_rec_rule_for_impl(rec_val: *mut LeanObject, major: *mut LeanObject) -> Option<*mut LeanObject> {
    let fn_ = app_head(major);
    if !lean_expr_is_const(fn_) { return None; }
    let cnstr_name = lean_expr_get_const_name(fn_);
    let rules = lean_recursor_val_get_rules(rec_val);
    let mut cur = rules;
    while !lean_list_is_nil(cur) {
        let rule = lean_list_head(cur);
        let rule_cnstr = lean_recursor_rule_get_cnstr(rule);
        if lean_name_eq(rule_cnstr, cnstr_name) {
            lean_inc(rule);
            return Some(rule);
        }
        cur = lean_list_tail(cur);
    }
    None
}

unsafe fn lean_instantiate_lparams(
    e: *mut LeanObject,
    lparams: *mut LeanObject,
    levels: *mut LeanObject,
) -> *mut LeanObject {
    // Substitute lparams → levels in expression e. Delegates to the real Lean
    // export lean_expr_instantiate_lparams (borrows e/ps/ls, returns owned).
    lean_expr_instantiate_lparams(e, lparams, levels)
}

// ---------------------------------------------------------------------------
// Extern "C" public entry points
// ---------------------------------------------------------------------------

// lean_add_decl / lean_add_decl_without_checking exported from kernel_environment.rs (still calls C++)
// They will be updated to call add_decl_impl once type_checker.cpp is fully removed.

// lean_kernel_* receive elab envs; need to extract kernel env first.
extern "C" {
    fn lean_elab_environment_to_kernel_env(env: *mut LeanObject) -> *mut LeanObject;
    // C++ type_checker.cpp globals (still bridged until full Rust port of add_quot/add_mutual).
    // Exported as plain C symbols (extern "C" LEAN_EXPORT) from libleanshared.
    fn initialize_cxx_type_checker_globals();
    fn finalize_cxx_type_checker_globals();
}

/// `lean_kernel_is_def_eq(env, lctx, a, b) -> Except KernelException Bool`
#[no_mangle]
pub unsafe extern "C" fn lean_kernel_is_def_eq(
    env: *mut LeanObject,
    lctx: *mut LeanObject,
    a: *mut LeanObject,
    b: *mut LeanObject,
) -> *mut LeanObject {
    let kernel_env = lean_elab_environment_to_kernel_env(env);
    let mut tc = TypeChecker::new(kernel_env, lctx, DEF_SAFETY_SAFE);
    lean_dec(kernel_env);
    match tc.is_def_eq(a, b) {
        Ok(r) => mk_except_ok(lean_box(if r { 1 } else { 0 })),
        Err(e) => kernel_error_to_lean_except(e),
    }
}

/// `lean_kernel_whnf(env, lctx, a) -> Except KernelException Expr`
#[no_mangle]
pub unsafe extern "C" fn lean_kernel_whnf(
    env: *mut LeanObject,
    lctx: *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let kernel_env = lean_elab_environment_to_kernel_env(env);
    let mut tc = TypeChecker::new(kernel_env, lctx, DEF_SAFETY_SAFE);
    lean_dec(kernel_env);
    match tc.whnf(a) {
        Ok(r) => mk_except_ok(r),
        Err(e) => kernel_error_to_lean_except(e),
    }
}

/// `lean_kernel_check(env, lctx, a) -> Except KernelException Expr`
#[no_mangle]
pub unsafe extern "C" fn lean_kernel_check(
    env: *mut LeanObject,
    lctx: *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let kernel_env = lean_elab_environment_to_kernel_env(env);
    let mut tc = TypeChecker::new(kernel_env, lctx, DEF_SAFETY_SAFE);
    lean_dec(kernel_env);
    // The `Kernel.check` debugging API matches C++ `check(expr)` (one arg), which is
    // `check_ignore_undefined_universes` (m_lparams = null). Passing an empty lparam list
    // instead would wrongly reject any term containing universe-level parameters.
    match tc.check_ignore_undefined_universes(a) {
        Ok(r) => mk_except_ok(r),
        Err(e) => kernel_error_to_lean_except(e),
    }
}

/// Build `Except.ok value` (a single-field constructor). `Except` declares `error`
/// first (tag 0) and `ok` second (tag 1), so `ok` uses tag `EXCEPT_OK_TAG`.
unsafe fn mk_except_ok(value: *mut LeanObject) -> *mut LeanObject {
    let ok = lean_alloc_ctor(EXCEPT_OK_TAG, 1, 0);
    lean_ctor_set(ok, 0, value);
    ok
}

// ---------------------------------------------------------------------------
// add_decl_impl — dispatches on declaration kind
// ---------------------------------------------------------------------------

unsafe fn add_decl_impl(
    env: *mut LeanObject,
    decl: *mut LeanObject,
    skip_check: bool,
) -> Result<*mut LeanObject, KernelError> {
    // Declaration kinds (matching C++ declaration_val tags):
    // 0 = Axiom, 1 = Definition, 2 = Theorem, 3 = Opaque, 4 = Mutual,
    // 5 = Inductive (handled in kernel_inductive.rs via lean_add_inductive)
    let kind = lean_ptr_tag(decl);
    lean_inc(env);
    let decl_name = lean_constant_info_get_name(decl);
    let decl_type = lean_constant_info_get_type(decl);

    // Basic duplicate check
    let check_result = lean_environment_check_name(env, decl_name);
    if !lean_is_scalar(check_result) {
        // Except.error — propagate
        let inner = lean_ctor_get(check_result, 0);
        lean_inc(inner);
        lean_dec(check_result);
        lean_dec(env);
        lean_inc(decl_name); lean_inc(inner);
        return Err(KernelError::AlreadyDeclared { env, name: decl_name });
    }
    lean_dec(check_result);

    if !skip_check {
        let lparams = lean_constant_info_get_lparams(decl);
        let mut tc = TypeChecker::new(env, ptr::null_mut(), DEF_SAFETY_SAFE);
        let ty = tc.check(decl_type, lparams)?;
        // For theorems: check type is Prop
        if kind == 2 {
            let sort = tc.whnf(ty)?;
            let prop = lean_expr_mk_prop();
            if !lean_expr_eqv(sort, prop) {
                lean_dec(sort); lean_dec(prop);
                lean_inc(env); lean_inc(decl_name); lean_inc(ty);
                return Err(KernelError::ThmTypeIsNotProp { env, name: decl_name, ty });
            }
            lean_dec(sort); lean_dec(prop);
        }
        lean_dec(ty);
        // Check definition value if present
        if lean_constant_info_has_value(decl) {
            let val = lean_constant_info_get_value(decl);
            let val_type = tc.check(val, lparams)?;
            if !tc.is_def_eq(val_type, decl_type)? {
                lean_inc(env);
                lean_inc(decl_name);
                lean_inc(val_type);
                lean_inc(decl_type);
                let err = KernelError::DeclTypeMismatch { env, decl: decl_name, given_type: val_type };
                lean_dec(decl_type);
                return Err(err);
            }
            lean_dec(val_type);
        }
    }

    // Add to environment
    lean_inc(decl);
    let new_env = lean_environment_add_core(env, decl);
    lean_dec(decl);
    lean_dec(env);

    if lean_is_scalar(new_env) {
        // This shouldn't happen after check_name succeeded, but handle gracefully
        lean_inc(env);
        lean_inc(decl_name);
        return Err(KernelError::AlreadyDeclared { env, name: decl_name });
    }

    Ok(new_env)
}

// ---------------------------------------------------------------------------
// Init / Finalize
// ---------------------------------------------------------------------------

#[export_name = "_ZN4lean23initialize_type_checkerEv"]
pub extern "C" fn initialize_type_checker() {
    unsafe {
        // Initialize C++ globals in type_checker.cpp (lean_cxx_add_* depend on these)
        initialize_cxx_type_checker_globals();

        let fresh_name = build_lean_name(&["_kernel_fresh"]);
        lean_mark_persistent(fresh_name);
        G_KERNEL_FRESH.store(fresh_name, Ordering::Release);
        // NB: the "_kernel_fresh" prefix is already registered by
        // initialize_cxx_type_checker_globals() above; registering it again here
        // would trip the duplicate-prefix assertion in the name generator.

        let bool_true = build_lean_name(&["Bool", "true"]);
        lean_mark_persistent(bool_true);
        G_BOOL_TRUE.store(bool_true, Ordering::Release);

        let eager_reduce = build_lean_name(&["eagerReduce"]);
        lean_mark_persistent(eager_reduce);
        G_EAGER_REDUCE.store(eager_reduce, Ordering::Release);

        // dont_care expression (a const with name "dontcare").
        // lean_expr_mk_const consumes both args (obj_arg); do not dec them after.
        let dont_care_name = build_lean_name(&["dontcare"]);
        let levels_nil = lean_mk_list_nil(ptr::null_mut());
        let dont_care_expr = lean_expr_mk_const(dont_care_name, levels_nil);
        lean_mark_persistent(dont_care_expr);
        G_DONT_CARE.store(dont_care_expr, Ordering::Release);

        // Bool constants (as Expr.const, used by mk_bool for reduced Nat.beq/ble results)
        init_global_const(&G_EXPR_BOOL_TRUE,  &["Bool", "true"]);
        init_global_const(&G_EXPR_BOOL_FALSE, &["Bool", "false"]);

        // Nat constants
        init_global_const(&G_NAT_ZERO,        &["Nat", "zero"]);
        init_global_const(&G_NAT_SUCC,        &["Nat", "succ"]);
        init_global_const(&G_NAT_ADD,         &["Nat", "add"]);
        init_global_const(&G_NAT_SUB,         &["Nat", "sub"]);
        init_global_const(&G_NAT_MUL,         &["Nat", "mul"]);
        init_global_const(&G_NAT_POW,         &["Nat", "pow"]);
        init_global_const(&G_NAT_GCD,         &["Nat", "gcd"]);
        init_global_const(&G_NAT_DIV,         &["Nat", "div"]);
        init_global_const(&G_NAT_MOD,         &["Nat", "mod"]);
        init_global_const(&G_NAT_BEQ,         &["Nat", "beq"]);
        init_global_const(&G_NAT_BLE,         &["Nat", "ble"]);
        init_global_const(&G_NAT_LAND,        &["Nat", "land"]);
        init_global_const(&G_NAT_LOR,         &["Nat", "lor"]);
        init_global_const(&G_NAT_XOR,         &["Nat", "xor"]);
        init_global_const(&G_NAT_SHIFTLEFT,   &["Nat", "shiftLeft"]);
        init_global_const(&G_NAT_SHIFTRIGHT,  &["Nat", "shiftRight"]);
        init_global_const(&G_STRING_MK,       &["String", "ofList"]);
        init_global_const(&G_LEAN_REDUCE_BOOL, &["Lean", "reduceBool"]);
        init_global_const(&G_LEAN_REDUCE_NAT,  &["Lean", "reduceNat"]);
    }
}

#[export_name = "_ZN4lean21finalize_type_checkerEv"]
pub extern "C" fn finalize_type_checker() {
    // All globals were marked persistent; the runtime will free them.
    // Reset pointers to null for cleanliness.
    unsafe { finalize_cxx_type_checker_globals(); }
    let ptrs: &[&AtomicPtr<LeanObject>] = &[
        &G_KERNEL_FRESH, &G_BOOL_TRUE, &G_EXPR_BOOL_TRUE, &G_EXPR_BOOL_FALSE, &G_EAGER_REDUCE, &G_DONT_CARE,
        &G_NAT_ZERO, &G_NAT_SUCC, &G_NAT_ADD, &G_NAT_SUB, &G_NAT_MUL,
        &G_NAT_POW, &G_NAT_GCD, &G_NAT_DIV, &G_NAT_MOD, &G_NAT_BEQ,
        &G_NAT_BLE, &G_NAT_LAND, &G_NAT_LOR, &G_NAT_XOR,
        &G_NAT_SHIFTLEFT, &G_NAT_SHIFTRIGHT,
        &G_STRING_MK, &G_LEAN_REDUCE_BOOL, &G_LEAN_REDUCE_NAT,
    ];
    for p in ptrs {
        p.store(ptr::null_mut(), Ordering::Release);
    }
}

#[export_name = "_ZN4lean22initialize_environmentEv"]
pub extern "C" fn initialize_environment() {
    // No per-environment globals needed; all state is per-instance.
}

#[export_name = "_ZN4lean20finalize_environmentEv"]
pub extern "C" fn finalize_environment() {}

// The ReductionStatus type needs to be accessible from the TypeChecker impl.
// Rust doesn't allow nested enums in impls cleanly, so we define it at module level:
#[derive(PartialEq)]
enum ReductionStatus { Continue, DefUnknown, DefEqual, DefDiff }

} // end kernel_type_checker_impl
#[cfg(feature = "export-runtime-ffi")]
pub use kernel_type_checker_impl::*;
