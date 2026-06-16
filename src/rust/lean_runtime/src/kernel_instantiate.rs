/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust implementations of kernel/instantiate.cpp LEAN_EXPORT functions:
  lean_expr_instantiate1      — replaces lean_cxx_expr_instantiate1
  lean_expr_instantiate       — replaces lean_cxx_expr_instantiate
  lean_expr_instantiate_range — replaces lean_cxx_expr_instantiate_range
  lean_expr_instantiate_rev   — replaces lean_cxx_expr_instantiate_rev
  lean_expr_instantiate_rev_range — replaces lean_cxx_expr_instantiate_rev_range

Algorithm: recursive expression traversal (mirrors replace_rec_fn) with an
(expr*, offset) cache for shared sub-expressions.

Expression kind tags:
  BVar=0  FVar=1  MVar=2  Sort=3  Const=4  App=5
  Lambda=6  Pi=7  Let=8  Lit=9  MData=10  Proj=11

Scalar field layout:
  All ctors: [0] Expr.Data (u64, bits 0-63)
    Bits [63:44] = bvarRange (20-bit, loose BVar count)
  Lambda/Pi (3 obj fields): uint8 BinderInfo after data u64
  Let      (4 obj fields): uint8 nondep after data u64
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_instantiate_impl {
    use super::*;
    use super::runtime_object_panic_impl::lean_internal_panic;
    use std::collections::HashMap;

    extern "C" {
        fn lean_expr_lift_loose_bvars(e: *mut LeanObject, s: *mut LeanObject, d: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_bvar(idx: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_app(f: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_lambda(n: *mut LeanObject, d: *mut LeanObject, b: *mut LeanObject, bi: u8) -> *mut LeanObject;
        fn lean_expr_mk_forall(n: *mut LeanObject, d: *mut LeanObject, b: *mut LeanObject, bi: u8) -> *mut LeanObject;
        fn lean_expr_mk_let(n: *mut LeanObject, t: *mut LeanObject, v: *mut LeanObject, b: *mut LeanObject, nondep: u8) -> *mut LeanObject;
        fn lean_expr_mk_mdata(data: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_proj(sname: *mut LeanObject, idx: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject;
    }

    const EXPR_BVAR:   u8 = 0;
    const EXPR_APP:    u8 = 5;
    const EXPR_LAMBDA: u8 = 6;
    const EXPR_PI:     u8 = 7;
    const EXPR_LET:    u8 = 8;
    const EXPR_MDATA:  u8 = 10;
    const EXPR_PROJ:   u8 = 11;

    // bvarRange = bits [63:44] of the Expr.Data u64.
    #[inline(always)]
    unsafe fn expr_bvar_range(e: *mut LeanObject) -> u64 {
        let num_objs = (*e).other as usize;
        let data = lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>());
        data >> 44
    }

    // BinderInfo byte for Lambda/Pi (stored after data u64, num_objs=3).
    #[inline(always)]
    unsafe fn expr_binder_info_raw(e: *mut LeanObject) -> u8 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint8(e, num_objs * 8 + 8)
    }

    // nondep byte for Let (4 obj fields, stored after data u64).
    #[inline(always)]
    unsafe fn expr_let_nondep(e: *mut LeanObject) -> u8 {
        lean_ctor_get_uint8(e, 4 * 8 + 8)
    }

    // (expr*, offset) → owned result cache — mirrors replace_rec_fn's cache.
    struct InstFn {
        n: usize,                           // number of substitution expressions
        base: *const *mut LeanObject,       // pointer to first subst element (borrowed)
        rev: bool,                          // if true, index as subst[n-1-rel_idx] (instantiateRev)
        cache: HashMap<(usize, u32), *mut LeanObject>,
    }

    impl Drop for InstFn {
        fn drop(&mut self) {
            unsafe {
                for (_, v) in &self.cache {
                    lean_dec(*v);
                }
            }
        }
    }

    impl InstFn {
        // Returns an owned reference to the instantiation of `e` at De Bruijn `offset`.
        // `e` is borrowed.
        unsafe fn apply(&mut self, e: *mut LeanObject, offset: u32) -> *mut LeanObject {
            // Early exit: no loose bvars at or above offset in this subtree.
            if expr_bvar_range(e) <= offset as u64 {
                lean_inc(e);
                return e;
            }

            // Cache check for shared nodes.
            let shared = (*e).rc != 1;
            if shared {
                if let Some(&cached) = self.cache.get(&(e as usize, offset)) {
                    lean_inc(cached);
                    return cached;
                }
            }

            let tag = lean_obj_tag(e);
            let result: *mut LeanObject = match tag {
                EXPR_BVAR => {
                    let idx_obj = lean_ctor_get(e, 0);
                    if lean_is_scalar(idx_obj) {
                        let idx = lean_unbox(idx_obj) as u32;
                        if idx >= offset {
                            let rel_idx = (idx - offset) as usize;
                            let (_, ovf) = (offset as usize).overflowing_add(self.n);
                            if ovf || rel_idx < self.n {
                                // In substitution range: look up substitution and lift.
                                let subst_idx = if self.rev { self.n - rel_idx - 1 } else { rel_idx };
                                let v = *self.base.add(subst_idx);
                                // lift_loose_bvars(v, 0, offset): lift all loose bvars by offset.
                                lean_expr_lift_loose_bvars(v, lean_box(0), lean_box(offset as usize))
                            } else {
                                // Beyond substitution range: lower BVar index by n.
                                let new_idx = idx as usize - self.n;
                                lean_expr_mk_bvar(lean_box(new_idx))
                            }
                        } else {
                            lean_inc(e);
                            e
                        }
                    } else {
                        // Bignum BVar: bvarRange is ≤ 20-bit; bignum indices can't appear.
                        lean_inc(e);
                        e
                    }
                }
                EXPR_APP => {
                    let fn_e  = lean_ctor_get(e, 0);
                    let arg_e = lean_ctor_get(e, 1);
                    let new_fn  = self.apply(fn_e,  offset);
                    let new_arg = self.apply(arg_e, offset);
                    if new_fn == fn_e && new_arg == arg_e {
                        lean_dec(new_fn);
                        lean_dec(new_arg);
                        lean_inc(e);
                        e
                    } else {
                        lean_expr_mk_app(new_fn, new_arg)
                    }
                }
                EXPR_LAMBDA | EXPR_PI => {
                    let dom  = lean_ctor_get(e, 1);
                    let body = lean_ctor_get(e, 2);
                    let new_dom  = self.apply(dom,  offset);
                    let new_body = self.apply(body, offset + 1);
                    if new_dom == dom && new_body == body {
                        lean_dec(new_dom);
                        lean_dec(new_body);
                        lean_inc(e);
                        e
                    } else {
                        let name = lean_ctor_get(e, 0);
                        lean_inc(name);
                        let bi = expr_binder_info_raw(e);
                        if tag == EXPR_LAMBDA {
                            lean_expr_mk_lambda(name, new_dom, new_body, bi)
                        } else {
                            lean_expr_mk_forall(name, new_dom, new_body, bi)
                        }
                    }
                }
                EXPR_LET => {
                    let ty   = lean_ctor_get(e, 1);
                    let val  = lean_ctor_get(e, 2);
                    let body = lean_ctor_get(e, 3);
                    let new_ty   = self.apply(ty,   offset);
                    let new_val  = self.apply(val,  offset);
                    let new_body = self.apply(body, offset + 1);
                    if new_ty == ty && new_val == val && new_body == body {
                        lean_dec(new_ty);
                        lean_dec(new_val);
                        lean_dec(new_body);
                        lean_inc(e);
                        e
                    } else {
                        let name   = lean_ctor_get(e, 0);
                        lean_inc(name);
                        let nondep = expr_let_nondep(e);
                        lean_expr_mk_let(name, new_ty, new_val, new_body, nondep)
                    }
                }
                EXPR_MDATA => {
                    let child = lean_ctor_get(e, 1);
                    let new_child = self.apply(child, offset);
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
                EXPR_PROJ => {
                    let child = lean_ctor_get(e, 2);
                    let new_child = self.apply(child, offset);
                    if new_child == child {
                        lean_dec(new_child);
                        lean_inc(e);
                        e
                    } else {
                        let sname = lean_ctor_get(e, 0);
                        let idx   = lean_ctor_get(e, 1);
                        lean_inc(sname);
                        lean_inc(idx);
                        lean_expr_mk_proj(sname, idx, new_child)
                    }
                }
                _ => {
                    // FVar, MVar, Sort, Const, Lit: leaves without loose bvars.
                    lean_inc(e);
                    e
                }
            };

            if shared {
                lean_inc(result);
                self.cache.insert((e as usize, offset), result);
            }
            result
        }
    }

    // Shared entry point for instantiate variants.
    // `a` is borrowed; returns owned.
    unsafe fn instantiate_core(
        a: *mut LeanObject,
        n: usize,
        base: *const *mut LeanObject,
        rev: bool,
    ) -> *mut LeanObject {
        if n == 0 || expr_bvar_range(a) == 0 {
            lean_inc(a);
            return a;
        }
        let mut inst = InstFn { n, base, rev, cache: HashMap::new() };
        inst.apply(a, 0)
    }

    // lean_expr_instantiate1 (a e : @& Expr) : Expr
    // Instantiates BVar(0) with e and lowers all remaining loose BVars by 1.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate1(
        a: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        let subst = [e as *mut LeanObject];
        instantiate_core(a, 1, subst.as_ptr(), false)
    }

    // Compute pointer to start of Lean array data (byte offset 24 from object header).
    // Does NOT dereference; safe to call on empty arrays.
    #[inline(always)]
    unsafe fn lean_array_data_ptr(obj: *mut LeanObject) -> *const *mut LeanObject {
        (obj as *const u8).add(24) as *const *mut LeanObject
    }

    // lean_expr_instantiate (a : @& Expr) (subst : @& Array Expr) : Expr
    // Instantiates BVar(i) with subst[i] for all i < subst.size.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        let n    = lean_array_size(subst);
        let base = lean_array_data_ptr(subst);
        instantiate_core(a, n, base, false)
    }

    // lean_expr_instantiate_range (a : @& Expr) (begin end : @& Nat) (subst : @& Array Expr) : Expr
    // Instantiates using subst[begin..end].
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(begin) || !lean_is_scalar(end) {
            lean_internal_panic(b"invalid range for Expr.instantiateRange\0".as_ptr() as *const i8);
        }
        let sz = lean_array_size(subst);
        let b  = lean_unbox(begin);
        let e  = lean_unbox(end);
        if b > e || e > sz {
            lean_internal_panic(b"invalid range for Expr.instantiateRange\0".as_ptr() as *const i8);
        }
        let n    = e - b;
        let base = lean_array_data_ptr(subst).add(b);
        instantiate_core(a, n, base, false)
    }

    // lean_expr_instantiate_rev (a : @& Expr) (subst : @& Array Expr) : Expr
    // Like instantiate but uses reversed indexing: BVar(i) → subst[n-1-i].
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        let n    = lean_array_size(subst);
        let base = lean_array_data_ptr(subst);
        instantiate_core(a, n, base, true)
    }

    // lean_expr_instantiate_rev_range (a : @& Expr) (begin end : @& Nat) (subst : @& Array Expr) : Expr
    // Like instantiate_rev but uses subst[begin..end].
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(begin) || !lean_is_scalar(end) {
            lean_internal_panic(b"invalid range for Expr.instantiateRevRange\0".as_ptr() as *const i8);
        }
        let sz = lean_array_size(subst);
        let b  = lean_unbox(begin);
        let e  = lean_unbox(end);
        if b > e || e > sz {
            lean_internal_panic(b"invalid range for Expr.instantiateRevRange\0".as_ptr() as *const i8);
        }
        let n    = e - b;
        let base = lean_array_data_ptr(subst).add(b);
        instantiate_core(a, n, base, true)
    }
}
