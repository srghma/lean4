// Port of kernel/expr_eq_fn.cpp
// Copyright (c) 2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: expr_eq_fn<> is a C++ template that pattern-matches on lean::expr
// sum types.  The comparison logic must stay in C++ because Rust cannot name
// lean::expr, lean::expr_kind, lean::level, etc.  This file owns the two
// LEAN_EXPORT entry points and delegates to C++ shims.

mod kernel_expr_eq_fn_impl {
    use super::*;

    /// Size of a pointer — used to compute scalar-field offsets in ctor objects.
    /// Must match the pointer size of the target platform (8 on 64-bit).
    const PTR_SIZE: usize = core::mem::size_of::<*mut LeanObject>();

    extern "C" {
        fn lean_nat_big_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_string_eq_cold(s1: *mut LeanObject, s2: *mut LeanObject) -> bool;
    }

    unsafe fn nat_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if a == b {
            true
        } else if lean_is_scalar(a) || lean_is_scalar(b) {
            false
        } else {
            lean_nat_big_eq(a, b)
        }
    }

    unsafe fn string_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if a == b {
            true
        } else if lean_string_size(a) != lean_string_size(b) {
            false
        } else {
            lean_string_eq_cold(a, b)
        }
    }

    unsafe fn level_list_eq(mut a: *mut LeanObject, mut b: *mut LeanObject, use_binder_info: bool) -> bool {
        loop {
            if a == b {
                return true;
            }
            let tag = lean_obj_tag(a);
            if tag != lean_obj_tag(b) {
                return false;
            }
            match tag {
                0 => return true,
                1 => {
                    if level_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0), use_binder_info) == 0 {
                        return false;
                    }
                    a = lean_ctor_get(a, 1);
                    b = lean_ctor_get(b, 1);
                }
                _ => return false,
            }
        }
    }

    unsafe fn literal_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if a == b {
            return true;
        }
        let tag = lean_obj_tag(a);
        if tag != lean_obj_tag(b) {
            return false;
        }
        match tag {
            0 => nat_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            1 => string_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            _ => false,
        }
    }

    unsafe fn pair_fst(p: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(p, 0)
    }

    unsafe fn pair_snd(p: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(p, 1)
    }

    unsafe fn data_value_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if a == b {
            return true;
        }
        let tag = lean_obj_tag(a);
        if tag != lean_obj_tag(b) {
            return false;
        }
        match tag {
            0 => string_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            1 => lean_ctor_get(a, 0) == lean_ctor_get(b, 0),
            2 => lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0,
            3 => nat_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            4 => crate::runtime_object_nat_int_impl::lean_int_big_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            // Syntax metadata is not part of the old C++ data_value helper surface; keep
            // the pointer fast path here instead of duplicating the full Syntax BEq layout.
            5 => lean_ctor_get(a, 0) == lean_ctor_get(b, 0),
            _ => false,
        }
    }

    unsafe fn kvmap_entries(m: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(m, 0)
    }

    unsafe fn kvmap_find(mut entries: *mut LeanObject, key: *mut LeanObject) -> *mut LeanObject {
        loop {
            match lean_obj_tag(entries) {
                0 => return core::ptr::null_mut(),
                1 => {
                    let entry = lean_ctor_get(entries, 0);
                    if lean_name_eq(pair_fst(entry), key) != 0 {
                        return pair_snd(entry);
                    }
                    entries = lean_ctor_get(entries, 1);
                }
                _ => return core::ptr::null_mut(),
            }
        }
    }

    unsafe fn kvmap_subset(mut entries: *mut LeanObject, other: *mut LeanObject) -> bool {
        loop {
            match lean_obj_tag(entries) {
                0 => return true,
                1 => {
                    let entry = lean_ctor_get(entries, 0);
                    let other_value = kvmap_find(kvmap_entries(other), pair_fst(entry));
                    if other_value.is_null() || !data_value_eq(pair_snd(entry), other_value) {
                        return false;
                    }
                    entries = lean_ctor_get(entries, 1);
                }
                _ => return false,
            }
        }
    }

    unsafe fn kvmap_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if a == b {
            return true;
        }
        kvmap_subset(kvmap_entries(a), b) && kvmap_subset(kvmap_entries(b), a)
    }

    unsafe fn level_eq(a: *mut LeanObject, b: *mut LeanObject, _use_binder_info: bool) -> u8 {
        lean_level_eq(a, b)
    }

    unsafe fn expr_eq(a: *mut LeanObject, b: *mut LeanObject, use_binder_info: bool) -> bool {
        if a == b {
            return true;
        }
        let tag = lean_obj_tag(a);
        if tag != lean_obj_tag(b) {
            return false;
        }
        match tag {
            // bvar
            0 => nat_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            // fvar, mvar
            1 | 2 => lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0,
            // sort
            3 => lean_level_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0,
            // const
            4 => {
                lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
                    && level_list_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_binder_info)
            }
            // app
            5 => {
                expr_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0), use_binder_info)
                    && expr_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_binder_info)
            }
            // lam, forallE
            6 | 7 => {
                (!use_binder_info
                    || (lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
                        && lean_ctor_get_uint8(a, 3 * PTR_SIZE) == lean_ctor_get_uint8(b, 3 * PTR_SIZE)))
                    && expr_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_binder_info)
                    && expr_eq(lean_ctor_get(a, 2), lean_ctor_get(b, 2), use_binder_info)
            }
            // letE
            8 => {
                (!use_binder_info || lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0)
                    && expr_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_binder_info)
                    && expr_eq(lean_ctor_get(a, 2), lean_ctor_get(b, 2), use_binder_info)
                    && expr_eq(lean_ctor_get(a, 3), lean_ctor_get(b, 3), use_binder_info)
                    && lean_ctor_get_uint8(a, 4 * PTR_SIZE) == lean_ctor_get_uint8(b, 4 * PTR_SIZE)
            }
            // lit
            9 => literal_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            // mdata
            10 => {
                kvmap_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0))
                    && expr_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_binder_info)
            }
            // proj
            11 => {
                lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
                    && nat_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1))
                    && expr_eq(lean_ctor_get(a, 2), lean_ctor_get(b, 2), use_binder_info)
            }
            _ => false,
        }
    }

    /// `lean_expr_eqv` — structural equality ignoring binder info.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_eqv(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        expr_eq(a, b, false) as u8
    }

    /// `lean_expr_equal` — structural equality including binder info.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_equal(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        expr_eq(a, b, true) as u8
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::ffi::CString;

        unsafe fn mk_name(text: &str) -> *mut LeanObject {
            let c_text = CString::new(text).unwrap();
            let s = lean_mk_string(c_text.as_ptr());
            lean_name_mk_string(lean_box(0), s)
        }

        unsafe fn mk_one_name_field_expr(tag: u32, name: *mut LeanObject) -> *mut LeanObject {
            let e = lean_runtime_alloc_ctor_export(tag, 1, core::mem::size_of::<u64>() as u32);
            lean_ctor_set(e, 0, name);
            e
        }

        unsafe fn mk_pair(fst: *mut LeanObject, snd: *mut LeanObject) -> *mut LeanObject {
            let p = lean_runtime_alloc_ctor_export(0, 2, 0);
            lean_ctor_set(p, 0, fst);
            lean_ctor_set(p, 1, snd);
            p
        }

        unsafe fn mk_list1(head: *mut LeanObject) -> *mut LeanObject {
            let cons = lean_runtime_alloc_ctor_export(1, 2, 0);
            lean_ctor_set(cons, 0, head);
            lean_ctor_set(cons, 1, lean_box(0));
            cons
        }

        unsafe fn mk_data_value_bool(value: bool) -> *mut LeanObject {
            let v = lean_runtime_alloc_ctor_export(1, 1, 0);
            lean_ctor_set(v, 0, lean_box(value as usize));
            v
        }

        unsafe fn mk_kvmap_bool(key: &str, value: bool) -> *mut LeanObject {
            let entry = mk_pair(mk_name(key), mk_data_value_bool(value));
            let map = lean_runtime_alloc_ctor_export(0, 1, 0);
            lean_ctor_set(map, 0, mk_list1(entry));
            map
        }

        unsafe fn mk_mdata_expr(mdata: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject {
            let e = lean_runtime_alloc_ctor_export(10, 2, core::mem::size_of::<u64>() as u32);
            lean_ctor_set(e, 0, mdata);
            lean_ctor_set(e, 1, expr);
            e
        }

        #[test]
        fn fvar_and_mvar_compare_their_name_fields() {
            unsafe {
                let x1 = mk_name("x");
                let x2 = mk_name("x");
                let y = mk_name("y");

                let fvar_x1 = mk_one_name_field_expr(1, x1);
                let fvar_x2 = mk_one_name_field_expr(1, x2);
                let fvar_y = mk_one_name_field_expr(1, y);
                assert_eq!(lean_expr_equal(fvar_x1, fvar_x2), 1);
                assert_eq!(lean_expr_equal(fvar_x1, fvar_y), 0);

                let mvar_x1 = mk_one_name_field_expr(2, x1);
                let mvar_x2 = mk_one_name_field_expr(2, x2);
                assert_eq!(lean_expr_equal(mvar_x1, mvar_x2), 1);
            }
        }

        #[test]
        fn mdata_compares_kvmap_by_value() {
            unsafe {
                let x1 = mk_one_name_field_expr(1, mk_name("x"));
                let x2 = mk_one_name_field_expr(1, mk_name("x"));
                let mdata1 = mk_kvmap_bool("annotation", true);
                let mdata2 = mk_kvmap_bool("annotation", true);
                assert_ne!(mdata1, mdata2);

                let e1 = mk_mdata_expr(mdata1, x1);
                let e2 = mk_mdata_expr(mdata2, x2);
                assert_eq!(lean_expr_equal(e1, e2), 1);
            }
        }
    }
}
