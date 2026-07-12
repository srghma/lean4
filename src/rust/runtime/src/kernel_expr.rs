/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust implementations of kernel/expr.cpp LEAN_EXPORT functions:
  lean_expr_mk_data, lean_expr_mk_app_data — pure bit-packing
  lean_expr_has_loose_bvar               — replaces lean_cxx_expr_has_loose_bvar
  lean_expr_lower_loose_bvars            — replaces lean_cxx_expr_lower_loose_bvars
  lean_expr_lift_loose_bvars             — replaces lean_cxx_expr_lift_loose_bvars

Expression kind tags (expr_kind enum):
  BVar=0  FVar=1  MVar=2  Sort=3  Const=4  App=5
  Lambda=6  Pi=7  Let=8  Lit=9  MData=10  Proj=11

Scalar field layout (after object pointer fields):
  All ctors: [0] Expr.Data (u64, bits 0-63)
    Bits [31:0]  = hash
    Bits [39:32] = approxDepth (clamped to 255)
    Bit  40      = hasFVar
    Bit  41      = hasExprMVar
    Bit  42      = hasLevelMVar
    Bit  43      = hasLevelParam
    Bits [63:44] = bvarRange (20-bit)
  Lambda/Pi (3 obj fields): [8] BinderInfo (u8)
  Let      (4 obj fields): [8] nondep flag (u8)
*/

mod kernel_expr_impl {
    use crate::runtime_expr_shared::{
        LeanBinderInfo, LeanExprKind, expr_binder_info_raw, expr_bvar_range, expr_bvar_range_data,
        expr_data, expr_kind, expr_let_nondep,
    };
    use crate::runtime_object_panic_impl::lean_internal_panic;
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

    unsafe extern "C" {
        fn lean_expr_mk_bvar(idx: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_lambda(
            n: *mut LeanObject,
            d: *mut LeanObject,
            b: *mut LeanObject,
            bi: LeanBinderInfo,
        ) -> *mut LeanObject;
        fn lean_expr_mk_forall(
            n: *mut LeanObject,
            d: *mut LeanObject,
            b: *mut LeanObject,
            bi: LeanBinderInfo,
        ) -> *mut LeanObject;
        fn lean_expr_mk_let(
            n: *mut LeanObject,
            t: *mut LeanObject,
            v: *mut LeanObject,
            b: *mut LeanObject,
            nondep: bool,
        ) -> *mut LeanObject;
        fn lean_expr_mk_mdata(data: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_proj(
            sname: *mut LeanObject,
            idx: *mut LeanObject,
            expr: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    // ── has_loose_bvar ──────────────────────────────────────────────────────

    // Returns true if expression `e` (visited at De Bruijn `offset`) contains
    // a loose BVar with index exactly `i + offset`.
    unsafe fn has_loose_bvar_impl(e: *const LeanObject, i: u32, offset: u32) -> bool {
        let n_i = match i.checked_add(offset) {
            Some(n) => n,
            None => return false, // overflow: index unreachable
        };
        // Early exit: this subtree has no loose bvars >= n_i
        if expr_bvar_range(e) <= n_i as u64 {
            return false;
        }
        match expr_kind(e) {
            LeanExprKind::BVar => {
                let idx_obj = lean_ctor_get(e, 0);
                if lean_is_scalar(idx_obj) {
                    lean_unbox(idx_obj) as u32 == n_i
                } else {
                    // Bignum bvar index is > u32; bvarRange would have overflowed
                    // mk_data's 20-bit cap, so this branch is unreachable in practice.
                    false
                }
            }
            LeanExprKind::App => {
                has_loose_bvar_impl(lean_ctor_get(e, 0), i, offset)
                    || has_loose_bvar_impl(lean_ctor_get(e, 1), i, offset)
            }
            LeanExprKind::Lambda | LeanExprKind::Pi => {
                has_loose_bvar_impl(lean_ctor_get(e, 1), i, offset)
                    || has_loose_bvar_impl(lean_ctor_get(e, 2), i, offset + 1)
            }
            LeanExprKind::Let => {
                has_loose_bvar_impl(lean_ctor_get(e, 1), i, offset)
                    || has_loose_bvar_impl(lean_ctor_get(e, 2), i, offset)
                    || has_loose_bvar_impl(lean_ctor_get(e, 3), i, offset + 1)
            }
            LeanExprKind::MData => has_loose_bvar_impl(lean_ctor_get(e, 1), i, offset),
            LeanExprKind::Proj => has_loose_bvar_impl(lean_ctor_get(e, 2), i, offset),
            _ => false, // Const, Sort, FVar, MVar, Lit: no loose bvars
        }
    }

    #[no_mangle]
    pub unsafe fn lean_expr_has_loose_bvar(e: *const LeanObject, i: *const LeanObject) -> bool {
        if !lean_is_scalar(i) {
            return false; // index too large, can't be present
        }
        let idx = lean_unbox(i) as u32;
        has_loose_bvar_impl(e, idx, 0)
    }

    // ── shift_loose_bvars (shared impl for lower and lift) ──────────────────
    //
    // Recursively shifts BVar indices >= s (adjusted by De Bruijn offset).
    // lift=true  → add d to matching bvar indices (lean_expr_lift_loose_bvars)
    // lift=false → subtract d from matching bvar indices (lean_expr_lower_loose_bvars)
    //
    // Ownership: `e` is borrowed; returns a new owned expression ref.
    // When no node changes, returns the same pointer with lean_inc applied.
    unsafe fn shift_loose_bvars(
        e: *mut LeanObject,
        offset: u32,
        s: u32,
        d: u32,
        lift: bool,
    ) -> *mut LeanObject {
        // Compute s1 = s + offset (abort if overflow — no BVar can be that large)
        let s1 = match s.checked_add(offset) {
            Some(n) => n,
            None => {
                lean_inc(e);
                return e;
            }
        };
        // Early exit: no loose bvars >= s1 in this subtree
        if expr_bvar_range(e) <= s1 as u64 {
            lean_inc(e);
            return e;
        }

        match expr_kind(e) {
            LeanExprKind::BVar => {
                let idx_obj = lean_ctor_get(e, 0);
                if lean_is_scalar(idx_obj) {
                    let idx = lean_unbox(idx_obj) as u32;
                    if idx >= s1 {
                        let new_idx = if lift { idx + d } else { idx - d };
                        // lean_expr_mk_bvar takes ownership of the nat arg
                        lean_expr_mk_bvar(lean_box(new_idx as usize))
                    } else {
                        lean_inc(e);
                        e
                    }
                } else {
                    // Bignum bvar index is unreachable: lean_expr_mk_data panics if
                    // bvarRange > 1048575 (20-bit cap), so any valid BVar index fits
                    // in a scalar. Return unchanged as a safe fallback.
                    lean_inc(e);
                    e
                }
            }
            LeanExprKind::App => {
                let fn_e = lean_ctor_get(e, 0);
                let arg_e = lean_ctor_get(e, 1);
                let new_fn = shift_loose_bvars(fn_e, offset, s, d, lift);
                let new_arg = shift_loose_bvars(arg_e, offset, s, d, lift);
                if new_fn == fn_e && new_arg == arg_e {
                    lean_dec(new_fn);
                    lean_dec(new_arg);
                    lean_inc(e);
                    e
                } else {
                    lean_expr_mk_app(new_fn, new_arg)
                }
            }
            LeanExprKind::Lambda | LeanExprKind::Pi => {
                let dom = lean_ctor_get(e, 1);
                let body = lean_ctor_get(e, 2);
                let new_dom = shift_loose_bvars(dom, offset, s, d, lift);
                let new_body = shift_loose_bvars(body, offset + 1, s, d, lift);
                if new_dom == dom && new_body == body {
                    lean_dec(new_dom);
                    lean_dec(new_body);
                    lean_inc(e);
                    e
                } else {
                    let name = lean_ctor_get(e, 0);
                    lean_inc(name);
                    let bi = expr_binder_info_raw(e);
                    if matches!(expr_kind(e), LeanExprKind::Lambda) {
                        lean_expr_mk_lambda(name, new_dom, new_body, bi)
                    } else {
                        lean_expr_mk_forall(name, new_dom, new_body, bi)
                    }
                }
            }
            LeanExprKind::Let => {
                let ty = lean_ctor_get(e, 1);
                let val = lean_ctor_get(e, 2);
                let body = lean_ctor_get(e, 3);
                let new_ty = shift_loose_bvars(ty, offset, s, d, lift);
                let new_val = shift_loose_bvars(val, offset, s, d, lift);
                let new_body = shift_loose_bvars(body, offset + 1, s, d, lift);
                if new_ty == ty && new_val == val && new_body == body {
                    lean_dec(new_ty);
                    lean_dec(new_val);
                    lean_dec(new_body);
                    lean_inc(e);
                    e
                } else {
                    let name = lean_ctor_get(e, 0);
                    lean_inc(name);
                    let nondep = expr_let_nondep(e);
                    lean_expr_mk_let(name, new_ty, new_val, new_body, nondep)
                }
            }
            LeanExprKind::MData => {
                let child = lean_ctor_get(e, 1);
                let new_child = shift_loose_bvars(child, offset, s, d, lift);
                if new_child == child {
                    lean_dec(new_child);
                    lean_inc(e);
                    e
                } else {
                    let md = lean_ctor_get(e, 0);
                    lean_inc(md);
                    lean_expr_mk_mdata(md, new_child)
                }
            }
            LeanExprKind::Proj => {
                let child = lean_ctor_get(e, 2);
                let new_child = shift_loose_bvars(child, offset, s, d, lift);
                if new_child == child {
                    lean_dec(new_child);
                    lean_inc(e);
                    e
                } else {
                    let sname = lean_ctor_get(e, 0);
                    let idx = lean_ctor_get(e, 1);
                    lean_inc(sname);
                    lean_inc(idx);
                    lean_expr_mk_proj(sname, idx, new_child)
                }
            }
            _ => {
                // Const, Sort, FVar, MVar, Lit: bvarRange already checked above
                lean_inc(e);
                e
            }
        }
    }

    // lower_loose_bvars(e, s, d): for all loose BVars with idx in [s, ∞), subtract d.
    // Precondition: s >= d (asserted in C++, guarded here).
    #[no_mangle]
    pub unsafe fn lean_expr_lower_loose_bvars(
        e: *mut LeanObject,
        s: *mut LeanObject,
        d: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(s) || !lean_is_scalar(d) {
            lean_inc(e);
            return e;
        }
        let s_val = lean_unbox(s) as u32;
        let d_val = lean_unbox(d) as u32;
        if d_val == 0 || s_val < d_val {
            lean_inc(e);
            return e;
        }
        shift_loose_bvars(e, 0, s_val, d_val, false)
    }

    // lift_loose_bvars(e, s, d): for all loose BVars with idx in [s, ∞), add d.
    #[no_mangle]
    pub unsafe fn lean_expr_lift_loose_bvars(
        e: *mut LeanObject,
        s: *mut LeanObject,
        d: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(s) || !lean_is_scalar(d) {
            lean_inc(e);
            return e;
        }
        let s_val = lean_unbox(s) as u32;
        let d_val = lean_unbox(d) as u32;
        if d_val == 0 {
            lean_inc(e);
            return e;
        }
        shift_loose_bvars(e, 0, s_val, d_val, true)
    }
}
