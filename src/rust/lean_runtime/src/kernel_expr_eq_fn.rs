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

    unsafe fn one_field_name_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
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
            1 | 2 => one_field_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
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
                lean_ctor_get(a, 0) == lean_ctor_get(b, 0)
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

}
