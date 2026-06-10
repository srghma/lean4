// Port of kernel/instantiate.cpp
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// Rust owns the exported instantiation entry points.  These are expression
// traversals over the runtime representation and must not delegate through the
// old C++ compatibility symbols, which are aliases back to these exports in the
// Rust runtime.

mod kernel_instantiate_impl {
    use super::*;
    use std::collections::HashMap;

    extern "C" {
        fn lean_expr_mk_bvar(idx: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_app(f: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_lambda(
            n: *mut LeanObject,
            d: *mut LeanObject,
            b: *mut LeanObject,
            bi: u8,
        ) -> *mut LeanObject;
        fn lean_expr_mk_forall(
            n: *mut LeanObject,
            d: *mut LeanObject,
            b: *mut LeanObject,
            bi: u8,
        ) -> *mut LeanObject;
        fn lean_expr_mk_let(
            n: *mut LeanObject,
            t: *mut LeanObject,
            v: *mut LeanObject,
            b: *mut LeanObject,
            nondep: u8,
        ) -> *mut LeanObject;
        fn lean_expr_mk_mdata(m: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_proj(
            struct_name: *mut LeanObject,
            idx: *mut LeanObject,
            structure: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    unsafe fn expr_loose_bvar_range(e: *mut LeanObject) -> usize {
        if lean_is_scalar(e) {
            0
        } else {
            let num_objs = (*e).m_other as usize;
            let data = lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>());
            (data >> 44) as usize
        }
    }

    unsafe fn is_shared_object(o: *mut LeanObject) -> bool {
        !lean_is_scalar(o) && lean_is_st(o) && (*o).m_rc > 1
    }

    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    struct CacheKey {
        expr: *mut LeanObject,
        offset: usize,
    }

    struct Instantiator {
        subst: *mut *mut LeanObject,
        len: usize,
        rev: bool,
        cache: HashMap<CacheKey, *mut LeanObject>,
    }

    impl Instantiator {
        unsafe fn new(subst: *mut *mut LeanObject, len: usize, rev: bool) -> Self {
            Self { subst, len, rev, cache: HashMap::new() }
        }

        unsafe fn subst_at(&self, idx: usize, offset: usize) -> *mut LeanObject {
            let subst_idx = idx - offset;
            if self.rev {
                *self.subst.add(self.len - subst_idx - 1)
            } else {
                *self.subst.add(subst_idx)
            }
        }

        unsafe fn cache_result(
            &mut self,
            key: CacheKey,
            result: *mut LeanObject,
            shared: bool,
        ) -> *mut LeanObject {
            if shared {
                lean_inc(result);
                self.cache.insert(key, result);
            }
            result
        }

        unsafe fn reuse_or(
            &mut self,
            key: CacheKey,
            original: *mut LeanObject,
            changed: bool,
            new_fields: &[*mut LeanObject],
            mk: impl FnOnce() -> *mut LeanObject,
            shared: bool,
        ) -> *mut LeanObject {
            if changed {
                self.cache_result(key, mk(), shared)
            } else {
                for &field in new_fields {
                    lean_dec(field);
                }
                lean_inc(original);
                self.cache_result(key, original, shared)
            }
        }

        unsafe fn visit(&mut self, e: *mut LeanObject, offset: usize) -> *mut LeanObject {
            if self.len == 0 || offset >= expr_loose_bvar_range(e) {
                lean_inc(e);
                return e;
            }

            let key = CacheKey { expr: e, offset };
            let shared = is_shared_object(e);
            if shared {
                if let Some(&cached) = self.cache.get(&key) {
                    lean_inc(cached);
                    return cached;
                }
            }

            match lean_obj_tag(e) {
                0 => {
                    let idx_obj = lean_ctor_get(e, 0);
                    if !lean_is_scalar(idx_obj) {
                        lean_inc(e);
                        return self.cache_result(key, e, shared);
                    }
                    let idx = lean_unbox(idx_obj);
                    if idx >= offset {
                        let end = offset.saturating_add(self.len);
                        if end < offset || idx < end {
                            let replacement = self.subst_at(idx, offset);
                            let lifted = if offset == 0 {
                                lean_inc(replacement);
                                replacement
                            } else {
                                lean_expr_lift_loose_bvars(replacement, lean_box(0), lean_box(offset))
                            };
                            self.cache_result(key, lifted, shared)
                        } else {
                            lean_expr_mk_bvar(lean_box(idx - self.len))
                        }
                    } else {
                        lean_inc(e);
                        self.cache_result(key, e, shared)
                    }
                }
                5 => {
                    let old_fn = lean_ctor_get(e, 0);
                    let old_arg = lean_ctor_get(e, 1);
                    let new_fn = self.visit(old_fn, offset);
                    let new_arg = self.visit(old_arg, offset);
                    self.reuse_or(key, e, new_fn != old_fn || new_arg != old_arg, &[new_fn, new_arg], || {
                        lean_expr_mk_app(new_fn, new_arg)
                    }, shared)
                }
                6 => {
                    let old_domain = lean_ctor_get(e, 1);
                    let old_body = lean_ctor_get(e, 2);
                    let domain = self.visit(old_domain, offset);
                    let body = self.visit(old_body, offset + 1);
                    self.reuse_or(key, e, domain != old_domain || body != old_body, &[domain, body], || {
                        let name = lean_ctor_get(e, 0);
                        lean_inc(name);
                        let bi = lean_ctor_get_uint8(e, 3 * core::mem::size_of::<*mut LeanObject>());
                        lean_expr_mk_lambda(name, domain, body, bi)
                    }, shared)
                }
                7 => {
                    let old_domain = lean_ctor_get(e, 1);
                    let old_body = lean_ctor_get(e, 2);
                    let domain = self.visit(old_domain, offset);
                    let body = self.visit(old_body, offset + 1);
                    self.reuse_or(key, e, domain != old_domain || body != old_body, &[domain, body], || {
                        let name = lean_ctor_get(e, 0);
                        lean_inc(name);
                        let bi = lean_ctor_get_uint8(e, 3 * core::mem::size_of::<*mut LeanObject>());
                        lean_expr_mk_forall(name, domain, body, bi)
                    }, shared)
                }
                8 => {
                    let old_type = lean_ctor_get(e, 1);
                    let old_value = lean_ctor_get(e, 2);
                    let old_body = lean_ctor_get(e, 3);
                    let typ = self.visit(old_type, offset);
                    let value = self.visit(old_value, offset);
                    let body = self.visit(old_body, offset + 1);
                    self.reuse_or(
                        key,
                        e,
                        typ != old_type || value != old_value || body != old_body,
                        &[typ, value, body],
                        || {
                            let name = lean_ctor_get(e, 0);
                            lean_inc(name);
                            let nondep = lean_ctor_get_uint8(e, 4 * core::mem::size_of::<*mut LeanObject>());
                            lean_expr_mk_let(name, typ, value, body, nondep)
                        },
                        shared,
                    )
                }
                10 => {
                    let old_expr = lean_ctor_get(e, 1);
                    let expr = self.visit(old_expr, offset);
                    self.reuse_or(key, e, expr != old_expr, &[expr], || {
                        let mdata = lean_ctor_get(e, 0);
                        lean_inc(mdata);
                        lean_expr_mk_mdata(mdata, expr)
                    }, shared)
                }
                11 => {
                    let old_struct = lean_ctor_get(e, 2);
                    let structure = self.visit(old_struct, offset);
                    self.reuse_or(key, e, structure != old_struct, &[structure], || {
                        let name = lean_ctor_get(e, 0);
                        let idx = lean_ctor_get(e, 1);
                        lean_inc(name);
                        lean_inc(idx);
                        lean_expr_mk_proj(name, idx, structure)
                    }, shared)
                }
                _ => {
                    lean_inc(e);
                    self.cache_result(key, e, shared)
                }
            }
        }
    }

    impl Drop for Instantiator {
        fn drop(&mut self) {
            unsafe {
                for &v in self.cache.values() {
                    lean_dec(v);
                }
            }
        }
    }

    unsafe fn instantiate_core(a: *mut LeanObject, subst: *mut *mut LeanObject, len: usize, rev: bool) -> *mut LeanObject {
        if len == 0 || expr_loose_bvar_range(a) == 0 {
            lean_inc(a);
            a
        } else {
            Instantiator::new(subst, len, rev).visit(a, 0)
        }
    }

    /// `Expr.instantiate1 (a e : Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate1(
        a: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut subst = [e];
        instantiate_core(a, subst.as_mut_ptr(), 1, false)
    }

    /// `Expr.instantiate (a : Expr) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        instantiate_core(a, lean_array_cptr(subst), lean_array_size(subst), false)
    }

    /// `Expr.instantiateRange (a : Expr) (begin end : Nat) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(begin) || !lean_is_scalar(end) {
            lean_internal_panic(c"invalid range for Expr.instantiateRange".as_ptr());
        }
        let sz = lean_array_size(subst);
        let b = lean_unbox(begin);
        let e = lean_unbox(end);
        if b > e || e > sz {
            lean_internal_panic(c"invalid range for Expr.instantiateRange".as_ptr());
        }
        instantiate_core(a, lean_array_cptr(subst).add(b), e - b, false)
    }

    /// `Expr.instantiateRev (a : Expr) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        instantiate_core(a, lean_array_cptr(subst), lean_array_size(subst), true)
    }

    /// `Expr.instantiateRevRange (a : Expr) (begin end : Nat) (subst : Array Expr) : Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(begin) || !lean_is_scalar(end) {
            lean_internal_panic(c"invalid range for Expr.instantiateRevRange".as_ptr());
        }
        let sz = lean_array_size(subst);
        let b = lean_unbox(begin);
        let e = lean_unbox(end);
        if b > e || e > sz {
            lean_internal_panic(c"invalid range for Expr.instantiateRevRange".as_ptr());
        }
        instantiate_core(a, lean_array_cptr(subst).add(b), e - b, true)
    }

}
