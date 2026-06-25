// Port of kernel/replace_fn.cpp
// Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// This file owns the single LEAN_EXPORT entry point `lean_replace_expr`.

mod kernel_replace_fn_impl {
    use super::*;
    use std::collections::HashMap;

    extern "C" {
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

    unsafe fn is_shared_object(o: *mut LeanObject) -> bool {
        !lean_is_scalar(o) && lean_is_st(o) && (*o).m_rc > 1
    }

    struct ReplaceExpr {
        f: *mut LeanObject,
        cache: HashMap<*mut LeanObject, *mut LeanObject>,
    }

    impl ReplaceExpr {
        unsafe fn new(f: *mut LeanObject) -> Self {
            Self { f, cache: HashMap::new() }
        }

        unsafe fn cache_result(
            &mut self,
            original: *mut LeanObject,
            result: *mut LeanObject,
            shared: bool,
        ) -> *mut LeanObject {
            if shared {
                lean_inc(result);
                self.cache.insert(original, result);
            }
            result
        }

        unsafe fn apply_callback(&mut self, e: *mut LeanObject) -> Option<*mut LeanObject> {
            lean_inc_ref(self.f);
            lean_inc(e);
            let r = lean_apply_1(self.f, e);
            if lean_is_scalar(r) {
                None
            } else {
                let replacement = lean_ctor_get(r, 0);
                lean_inc(replacement);
                lean_dec_ref(r);
                Some(replacement)
            }
        }

        unsafe fn reuse_or(
            &mut self,
            original: *mut LeanObject,
            changed: bool,
            new_fields: &[*mut LeanObject],
            mk: impl FnOnce() -> *mut LeanObject,
            shared: bool,
        ) -> *mut LeanObject {
            if changed {
                self.cache_result(original, mk(), shared)
            } else {
                for &field in new_fields {
                    lean_dec(field);
                }
                lean_inc(original);
                self.cache_result(original, original, shared)
            }
        }

        unsafe fn visit(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            let shared = is_shared_object(e);
            if shared {
                if let Some(&cached) = self.cache.get(&e) {
                    lean_inc(cached);
                    return cached;
                }
            }

            if let Some(replacement) = self.apply_callback(e) {
                return self.cache_result(e, replacement, shared);
            }

            match lean_obj_tag(e) {
                5 => {
                    let old_fn = lean_ctor_get(e, 0);
                    let old_arg = lean_ctor_get(e, 1);
                    let new_fn = self.visit(old_fn);
                    let new_arg = self.visit(old_arg);
                    self.reuse_or(e, new_fn != old_fn || new_arg != old_arg, &[new_fn, new_arg], || {
                        lean_expr_mk_app(new_fn, new_arg)
                    }, shared)
                }
                6 => {
                    let old_domain = lean_ctor_get(e, 1);
                    let old_body = lean_ctor_get(e, 2);
                    let domain = self.visit(old_domain);
                    let body = self.visit(old_body);
                    self.reuse_or(e, domain != old_domain || body != old_body, &[domain, body], || {
                        let name = lean_ctor_get(e, 0);
                        lean_inc(name);
                        let bi = lean_ctor_get_uint8(e, 3 * core::mem::size_of::<*mut LeanObject>());
                        lean_expr_mk_lambda(name, domain, body, bi)
                    }, shared)
                }
                7 => {
                    let old_domain = lean_ctor_get(e, 1);
                    let old_body = lean_ctor_get(e, 2);
                    let domain = self.visit(old_domain);
                    let body = self.visit(old_body);
                    self.reuse_or(e, domain != old_domain || body != old_body, &[domain, body], || {
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
                    let typ = self.visit(old_type);
                    let value = self.visit(old_value);
                    let body = self.visit(old_body);
                    self.reuse_or(
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
                    let expr = self.visit(old_expr);
                    self.reuse_or(e, expr != old_expr, &[expr], || {
                        let mdata = lean_ctor_get(e, 0);
                        lean_inc(mdata);
                        lean_expr_mk_mdata(mdata, expr)
                    }, shared)
                }
                11 => {
                    let old_struct = lean_ctor_get(e, 2);
                    let structure = self.visit(old_struct);
                    self.reuse_or(e, structure != old_struct, &[structure], || {
                        let name = lean_ctor_get(e, 0);
                        let idx = lean_ctor_get(e, 1);
                        lean_inc(name);
                        lean_inc(idx);
                        lean_expr_mk_proj(name, idx, structure)
                    }, shared)
                }
                _ => {
                    lean_inc(e);
                    self.cache_result(e, e, shared)
                }
            }
        }
    }

    impl Drop for ReplaceExpr {
        fn drop(&mut self) {
            unsafe {
                for &v in self.cache.values() {
                    lean_dec(v);
                }
            }
        }
    }

    /// `lean_replace_expr (f : Expr → Option Expr) (e : Expr) : Expr`
    ///
    /// Applies `f` to every subexpression of `e`; if `f` returns `some e'`,
    /// the subexpression is replaced and its children are not visited.
    #[no_mangle]
    pub unsafe extern "C" fn lean_replace_expr(
        f: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        ReplaceExpr::new(f).visit(e)
    }

}
