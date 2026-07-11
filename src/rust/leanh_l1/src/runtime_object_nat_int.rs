/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of Natural numbers, Integers, UInt, IntX sections from src/runtime/object.cpp.

use core::ffi::{c_char, c_int, c_long, c_ulong};

use gmp_mpfr_sys::gmp::{
    mpz_add, mpz_add_ui, mpz_and, mpz_clear, mpz_cmp, mpz_cmp_si, mpz_divexact, mpz_fdiv_q_2exp,
    mpz_fdiv_r_2exp, mpz_gcd, mpz_get_si, mpz_get_ui, mpz_init, mpz_init_set, mpz_init_set_si,
    mpz_init_set_str, mpz_init_set_ui, mpz_ior, mpz_mul, mpz_mul_2exp, mpz_mul_si, mpz_mul_ui,
    mpz_neg, mpz_pow_ui, mpz_set, mpz_sub, mpz_sub_ui, mpz_t, mpz_tdiv_q, mpz_tdiv_q_2exp,
    mpz_tdiv_q_ui, mpz_tdiv_qr, mpz_tdiv_r, mpz_xor,
};

use crate::datatypes::{LEAN_MAX_SMALL_NAT, LEAN_MPZ_TAG, LeanMpzObject, LeanObject};
use crate::emitted::{
    lean_box::lean_box, lean_dec::lean_dec, lean_inc::lean_inc, lean_is_scalar::lean_is_scalar,
    lean_unbox::lean_unbox,
};
use crate::r#priv::{
    lean_alloc_small_object::lean_alloc_small_object, lean_scalar_to_int::lean_scalar_to_int,
    lean_scalar_to_int64::lean_scalar_to_int64,
};
use crate::runtime_mpz::{
    mpz_ctor_uint64, mpz_get_size_t, mpz_is_size_t, mpz_log2, mpz_sgn, uninit_mpzt,
};
use crate::runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic;

const LEAN_MAX_SMALL_INT: i32 = i32::MAX;
const LEAN_MIN_SMALL_INT: i32 = i32::MIN;

#[inline]
pub(crate) unsafe fn lean_mpz_val(o: *const LeanObject) -> *const mpz_t {
    (o as *const u8).add(core::mem::size_of::<LeanObject>()) as *const mpz_t
}

#[inline]
pub(crate) unsafe fn lean_mpz_val_mut(o: *mut LeanObject) -> *mut mpz_t {
    (o as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut mpz_t
}

pub unsafe fn lean_alloc_mpz(mpz: *const mpz_t) -> *mut LeanObject {
    let sz = core::mem::size_of::<LeanMpzObject>();
    let obj = lean_alloc_small_object(sz);
    let saved_cs_size = (*obj).cs_size;
    let slot = lean_mpz_val_mut(obj);
    mpz_init_set(slot, mpz);
    (*obj).rc = 1;
    (*obj).tag = LEAN_MPZ_TAG;
    (*obj).other = 0;
    (*obj).cs_size = saved_cs_size;
    obj
}

pub(crate) unsafe fn mpz_to_nat(m: *mut mpz_t) -> *mut LeanObject {
    if mpz_is_size_t(m) {
        let v = mpz_get_size_t(m);
        if v <= LEAN_MAX_SMALL_NAT {
            mpz_clear(m);
            return lean_box(v);
        }
    }
    let r = lean_alloc_mpz(m);
    mpz_clear(m);
    r
}

pub(crate) unsafe fn mpz_to_nat_core(m: *mut mpz_t) -> *mut LeanObject {
    let r = lean_alloc_mpz(m);
    mpz_clear(m);
    r
}

unsafe fn mpz_to_int(m: *mut mpz_t) -> *mut LeanObject {
    let cmp_max = mpz_cmp_si(m, LEAN_MAX_SMALL_INT as c_long);
    let cmp_min = mpz_cmp_si(m, LEAN_MIN_SMALL_INT as c_long);
    if cmp_min >= 0 && cmp_max <= 0 {
        let v = mpz_get_si(m) as i32 as u32 as usize;
        mpz_clear(m);
        return lean_box(v);
    }
    let r = lean_alloc_mpz(m);
    mpz_clear(m);
    r
}

unsafe fn mpz_to_int_core(m: *mut mpz_t) -> *mut LeanObject {
    let r = lean_alloc_mpz(m);
    mpz_clear(m);
    r
}

#[inline]
pub unsafe fn lean_int64_to_int(n: i64) -> *mut LeanObject {
    if (LEAN_MIN_SMALL_INT as i64) <= n && n <= (LEAN_MAX_SMALL_INT as i64) {
        lean_box(n as i32 as u32 as usize)
    } else {
        lean_big_int64_to_int(n)
    }
}

// ── Natural numbers ─────────────────────────────────────────────────────

pub unsafe fn lean_extract_mpz_value(o: *const LeanObject, v: *mut mpz_t) {
    mpz_set(v, lean_mpz_val(o));
}

pub unsafe fn lean_mpz_hash(o: *const LeanObject) -> u32 {
    mpz_get_si(lean_mpz_val(o)) as i32 as u32
}

pub unsafe fn lean_mpz_eq(o1: *const LeanObject, o2: *const LeanObject) -> bool {
    mpz_cmp(lean_mpz_val(o1), lean_mpz_val(o2)) == 0
}

pub unsafe fn lean_alloc_mpz_from_mpz(o: *const LeanObject) -> *mut LeanObject {
    lean_alloc_mpz(lean_mpz_val(o))
}

pub unsafe fn lean_big_uint64_to_nat(n: u64) -> *mut LeanObject {
    if n <= LEAN_MAX_SMALL_NAT as u64 {
        return lean_box(n as usize);
    }
    let mut m = uninit_mpzt();
    mpz_ctor_uint64(&mut m, n);
    mpz_to_nat_core(&mut m)
}

pub unsafe fn lean_nat_big_succ(a: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init_set(&mut m, lean_mpz_val(a));
    mpz_add_ui(&mut m, &m, 1);
    mpz_to_nat_core(&mut m)
}

pub unsafe fn lean_nat_big_add(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    if lean_is_scalar(a1) {
        mpz_add_ui(&mut m, lean_mpz_val(a2), lean_unbox(a1) as c_ulong);
    } else if lean_is_scalar(a2) {
        mpz_add_ui(&mut m, lean_mpz_val(a1), lean_unbox(a2) as c_ulong);
    } else {
        mpz_add(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
    }
    mpz_to_nat_core(&mut m)
}

pub unsafe fn lean_nat_big_sub(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) {
        lean_box(0)
    } else if lean_is_scalar(a2) {
        let mut m = uninit_mpzt();
        mpz_init_set(&mut m, lean_mpz_val(a1));
        mpz_sub_ui(&mut m, &m, lean_unbox(a2) as c_ulong);
        mpz_to_nat(&mut m)
    } else {
        if mpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) < 0 {
            return lean_box(0);
        }
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_sub(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        mpz_to_nat(&mut m)
    }
}

pub unsafe fn lean_nat_big_mul(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    if lean_is_scalar(a1) {
        mpz_mul_ui(&mut m, lean_mpz_val(a2), lean_unbox(a1) as c_ulong);
    } else if lean_is_scalar(a2) {
        mpz_mul_ui(&mut m, lean_mpz_val(a1), lean_unbox(a2) as c_ulong);
    } else {
        mpz_mul(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
    }
    mpz_to_nat(&mut m)
}

pub unsafe fn lean_nat_overflow_mul(a1: usize, a2: usize) -> *mut LeanObject {
    let mut m1 = uninit_mpzt();
    mpz_init_set_ui(&mut m1, a1 as c_ulong);
    let mut m2 = uninit_mpzt();
    mpz_init_set_ui(&mut m2, a2 as c_ulong);
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    mpz_mul(&mut m, &m1, &m2);
    mpz_clear(&mut m1);
    mpz_clear(&mut m2);
    mpz_to_nat(&mut m)
}

pub unsafe fn lean_nat_big_div(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) {
        lean_box(0)
    } else if lean_is_scalar(a2) {
        let n2 = lean_unbox(a2);
        if n2 == 0 {
            return a2;
        }
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_tdiv_q_ui(&mut m, lean_mpz_val(a1), n2 as c_ulong);
        mpz_to_nat(&mut m)
    } else {
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_tdiv_q(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        mpz_to_nat(&mut m)
    }
}

pub unsafe fn lean_nat_big_div_exact(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) {
        lean_box(0)
    } else if lean_is_scalar(a2) {
        let mut d = uninit_mpzt();
        mpz_init_set_ui(&mut d, lean_unbox(a2) as c_ulong);
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_divexact(&mut m, lean_mpz_val(a1), &d);
        mpz_clear(&mut d);
        mpz_to_nat(&mut m)
    } else {
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_divexact(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        mpz_to_nat(&mut m)
    }
}

pub unsafe fn lean_nat_big_mod(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) {
        a1
    } else if lean_is_scalar(a2) {
        let n2 = lean_unbox(a2);
        if n2 == 0 {
            lean_inc(a1);
            return a1;
        }
        let mut d = uninit_mpzt();
        mpz_init_set_ui(&mut d, n2 as c_ulong);
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_tdiv_r(&mut m, lean_mpz_val(a1), &d);
        mpz_clear(&mut d);
        mpz_to_nat(&mut m)
    } else {
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_tdiv_r(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        mpz_to_nat(&mut m)
    }
}

pub unsafe fn lean_nat_big_eq(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if lean_is_scalar(a1) || lean_is_scalar(a2) {
        return false;
    }
    mpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) == 0
}

pub unsafe fn lean_nat_big_le(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if lean_is_scalar(a1) {
        return true;
    } else if lean_is_scalar(a2) {
        return false;
    }
    mpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) <= 0
}

pub unsafe fn lean_nat_big_lt(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if lean_is_scalar(a1) {
        return true;
    } else if lean_is_scalar(a2) {
        return false;
    }
    mpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) < 0
}

#[inline]
pub unsafe fn lean_nat_add(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        lean_box(lean_unbox(a1).wrapping_add(lean_unbox(a2)))
    } else {
        lean_nat_big_add(a1, a2)
    }
}

#[inline]
pub unsafe fn lean_nat_mul(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        let n1 = lean_unbox(a1);
        if n1 == 0 {
            return a1;
        }
        let n2 = lean_unbox(a2);
        let r = n1.wrapping_mul(n2);
        if r <= LEAN_MAX_SMALL_NAT && r / n1 == n2 {
            lean_box(r)
        } else {
            lean_nat_overflow_mul(n1, n2)
        }
    } else {
        lean_nat_big_mul(a1, a2)
    }
}

#[inline]
pub unsafe fn lean_nat_div(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        let n1 = lean_unbox(a1);
        let n2 = lean_unbox(a2);
        lean_box(if n2 == 0 { 0 } else { n1 / n2 })
    } else {
        lean_nat_big_div(a1, a2)
    }
}

#[inline]
pub unsafe fn lean_nat_mod(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        let n1 = lean_unbox(a1);
        let n2 = lean_unbox(a2);
        lean_box(if n2 == 0 { n1 } else { n1 % n2 })
    } else {
        lean_nat_big_mod(a1, a2)
    }
}

#[inline]
pub unsafe fn lean_nat_eq(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if core::ptr::eq(a1, a2) {
        return true;
    }
    if lean_is_scalar(a1) || lean_is_scalar(a2) {
        return false;
    }
    lean_nat_big_eq(a1, a2)
}

#[inline]
pub unsafe fn lean_nat_dec_eq(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    lean_nat_eq(a1, a2)
}

#[inline]
pub unsafe fn lean_nat_le(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        return a1 <= a2;
    }
    lean_nat_big_le(a1, a2)
}

#[inline]
pub unsafe fn lean_nat_dec_le(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    lean_nat_le(a1, a2)
}

#[inline]
pub unsafe fn lean_nat_lt(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        return a1 < a2;
    }
    lean_nat_big_lt(a1, a2)
}

#[inline]
pub unsafe fn lean_nat_dec_lt(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    lean_nat_lt(a1, a2)
}

#[inline]
pub unsafe fn lean_nat_sub(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        let n1 = lean_unbox(a1);
        let n2 = lean_unbox(a2);
        if n1 < n2 {
            lean_box(0)
        } else {
            lean_box(n1 - n2)
        }
    } else {
        lean_nat_big_sub(a1, a2)
    }
}

#[inline]
pub unsafe fn lean_nat_pred(n: *mut LeanObject) -> *mut LeanObject {
    lean_nat_sub(n, lean_box(1))
}

pub unsafe fn lean_nat_big_land(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    if lean_is_scalar(a1) {
        let mut s = uninit_mpzt();
        mpz_init_set_ui(&mut s, lean_unbox(a1) as c_ulong);
        mpz_and(&mut m, &s, lean_mpz_val(a2));
        mpz_clear(&mut s);
    } else if lean_is_scalar(a2) {
        let mut s = uninit_mpzt();
        mpz_init_set_ui(&mut s, lean_unbox(a2) as c_ulong);
        mpz_and(&mut m, lean_mpz_val(a1), &s);
        mpz_clear(&mut s);
    } else {
        mpz_and(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
    }
    mpz_to_nat(&mut m)
}

pub unsafe fn lean_nat_big_lor(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    if lean_is_scalar(a1) {
        let mut s = uninit_mpzt();
        mpz_init_set_ui(&mut s, lean_unbox(a1) as c_ulong);
        mpz_ior(&mut m, &s, lean_mpz_val(a2));
        mpz_clear(&mut s);
    } else if lean_is_scalar(a2) {
        let mut s = uninit_mpzt();
        mpz_init_set_ui(&mut s, lean_unbox(a2) as c_ulong);
        mpz_ior(&mut m, lean_mpz_val(a1), &s);
        mpz_clear(&mut s);
    } else {
        mpz_ior(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
    }
    mpz_to_nat(&mut m)
}

pub unsafe fn lean_nat_big_xor(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    if lean_is_scalar(a1) {
        let mut s = uninit_mpzt();
        mpz_init_set_ui(&mut s, lean_unbox(a1) as c_ulong);
        mpz_xor(&mut m, &s, lean_mpz_val(a2));
        mpz_clear(&mut s);
    } else if lean_is_scalar(a2) {
        let mut s = uninit_mpzt();
        mpz_init_set_ui(&mut s, lean_unbox(a2) as c_ulong);
        mpz_xor(&mut m, lean_mpz_val(a1), &s);
        mpz_clear(&mut s);
    } else {
        mpz_xor(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
    }
    mpz_to_nat(&mut m)
}

pub unsafe fn lean_nat_shiftl(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) && lean_unbox(a1) == 0 {
        return lean_box(0);
    }
    if !lean_is_scalar(a2) || lean_unbox(a2) > u32::MAX as usize {
        lean_internal_panic(c"Nat.shiftl exponent is too big".as_ptr());
    }
    let k = lean_unbox(a2) as u64;
    let mut m = uninit_mpzt();
    if lean_is_scalar(a1) {
        mpz_init_set_ui(&mut m, lean_unbox(a1) as c_ulong);
    } else {
        mpz_init_set(&mut m, lean_mpz_val(a1));
    }
    mpz_mul_2exp(&mut m, &m, k);
    mpz_to_nat(&mut m)
}

pub unsafe fn lean_nat_big_shiftr(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar(a2) {
        return lean_box(0);
    }
    let s = lean_unbox(a2);
    let mut m = uninit_mpzt();
    if lean_is_scalar(a1) {
        mpz_init_set_ui(&mut m, lean_unbox(a1) as c_ulong);
    } else {
        mpz_init_set(&mut m, lean_mpz_val(a1));
    }
    if s > u32::MAX as usize {
        if mpz_log2(&m) >= s {
            mpz_clear(&mut m);
            lean_internal_panic(c"Nat.shiftr exponent is too big".as_ptr());
        }
        mpz_clear(&mut m);
        return lean_box(0);
    }
    mpz_tdiv_q_2exp(&mut m, &m, s as u64);
    mpz_to_nat(&mut m)
}

pub unsafe fn lean_nat_pow(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar(a2) || lean_unbox(a2) > u32::MAX as usize {
        lean_internal_panic(c"Nat.pow exponent is too big".as_ptr());
    }
    let exp = lean_unbox(a2) as c_ulong;
    let mut base = uninit_mpzt();
    if lean_is_scalar(a1) {
        mpz_init_set_ui(&mut base, lean_unbox(a1) as c_ulong);
    } else {
        mpz_init_set(&mut base, lean_mpz_val(a1));
    }
    let mut result = uninit_mpzt();
    mpz_init(&mut result);
    mpz_pow_ui(&mut result, &base, exp);
    mpz_clear(&mut base);
    mpz_to_nat(&mut result)
}

pub unsafe fn lean_nat_gcd(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut m1 = uninit_mpzt();
    let mut m2 = uninit_mpzt();
    if lean_is_scalar(a1) {
        mpz_init_set_ui(&mut m1, lean_unbox(a1) as c_ulong);
    } else {
        mpz_init_set(&mut m1, lean_mpz_val(a1));
    }
    if lean_is_scalar(a2) {
        mpz_init_set_ui(&mut m2, lean_unbox(a2) as c_ulong);
    } else {
        mpz_init_set(&mut m2, lean_mpz_val(a2));
    }
    let mut g = uninit_mpzt();
    mpz_init(&mut g);
    mpz_gcd(&mut g, &m1, &m2);
    mpz_clear(&mut m1);
    mpz_clear(&mut m2);
    mpz_to_nat(&mut g)
}

pub unsafe fn lean_nat_log2(a: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) {
        let mut n = lean_unbox(a);
        let mut res: usize = 0;
        while n >= 2 {
            res += 1;
            n /= 2;
        }
        lean_box(res)
    } else {
        lean_box(mpz_log2(lean_mpz_val(a)))
    }
}

#[inline]
pub unsafe fn lean_nat_to_int(a: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) {
        let v = lean_unbox(a);
        if v <= LEAN_MAX_SMALL_INT as usize {
            a
        } else {
            lean_big_size_t_to_int(v)
        }
    } else {
        a
    }
}

#[inline]
pub unsafe fn lean_int_lt(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        return lean_scalar_to_int64(a1) < lean_scalar_to_int64(a2);
    }
    lean_int_big_lt(a1, a2)
}

#[inline]
pub unsafe fn lean_int_to_nat(a: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(!lean_int_lt(a, lean_box(0)));
    if lean_is_scalar(a) {
        a
    } else {
        lean_big_int_to_nat(a)
    }
}

#[inline]
pub unsafe fn lean_nat_abs(i: *mut LeanObject) -> *mut LeanObject {
    if lean_int_lt(i, lean_box(0)) {
        lean_int_to_nat(lean_int_neg(i))
    } else {
        lean_inc(i);
        lean_int_to_nat(i)
    }
}

// ── Integers ────────────────────────────────────────────────────────────

#[inline]
pub unsafe fn lean_int_neg(a: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) {
        lean_int64_to_int(-lean_scalar_to_int64(a))
    } else {
        lean_int_big_neg(a)
    }
}

pub unsafe fn lean_big_int_to_nat(a: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init_set(&mut m, lean_mpz_val(a));
    lean_dec(a);
    mpz_to_nat(&mut m)
}

pub unsafe fn lean_cstr_to_int(n: *const c_char) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init_set_str(&mut m, n, 10);
    mpz_to_int(&mut m)
}

pub unsafe fn lean_big_int_to_int(n: c_int) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init_set_si(&mut m, n as c_long);
    mpz_to_int_core(&mut m)
}

pub unsafe fn lean_big_size_t_to_int(n: usize) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init_set_ui(&mut m, n as c_ulong);
    mpz_to_int_core(&mut m)
}

pub unsafe fn lean_big_int64_to_int(n: i64) -> *mut LeanObject {
    if n >= LEAN_MIN_SMALL_INT as i64 && n <= LEAN_MAX_SMALL_INT as i64 {
        return lean_box(n as i32 as u32 as usize);
    }
    let mut m = uninit_mpzt();
    let w: u64 = if n < 0 {
        (-(n as i128)) as u64
    } else {
        n as u64
    };
    mpz_ctor_uint64(&mut m, w);
    if n < 0 {
        mpz_neg(&mut m, &m);
    }
    mpz_to_int_core(&mut m)
}

pub unsafe fn lean_int_big_neg(a: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    mpz_neg(&mut m, lean_mpz_val(a));
    mpz_to_int(&mut m)
}

pub unsafe fn lean_int_big_add(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    if lean_is_scalar(a1) {
        let i1 = lean_scalar_to_int(a1);
        if i1 >= 0 {
            mpz_add_ui(&mut m, lean_mpz_val(a2), i1 as c_ulong);
        } else {
            mpz_sub_ui(&mut m, lean_mpz_val(a2), (-(i1 as i64)) as c_ulong);
        }
    } else if lean_is_scalar(a2) {
        let i2 = lean_scalar_to_int(a2);
        if i2 >= 0 {
            mpz_add_ui(&mut m, lean_mpz_val(a1), i2 as c_ulong);
        } else {
            mpz_sub_ui(&mut m, lean_mpz_val(a1), (-(i2 as i64)) as c_ulong);
        }
    } else {
        mpz_add(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
    }
    mpz_to_int(&mut m)
}

pub unsafe fn lean_int_big_sub(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    if lean_is_scalar(a1) {
        let mut n = uninit_mpzt();
        mpz_init_set_si(&mut n, lean_scalar_to_int(a1) as c_long);
        mpz_sub(&mut m, &n, lean_mpz_val(a2));
        mpz_clear(&mut n);
    } else if lean_is_scalar(a2) {
        let i2 = lean_scalar_to_int(a2);
        if i2 >= 0 {
            mpz_sub_ui(&mut m, lean_mpz_val(a1), i2 as c_ulong);
        } else {
            mpz_add_ui(&mut m, lean_mpz_val(a1), (-(i2 as i64)) as c_ulong);
        }
    } else {
        mpz_sub(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
    }
    mpz_to_int(&mut m)
}

pub unsafe fn lean_int_big_mul(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init(&mut m);
    if lean_is_scalar(a1) {
        mpz_mul_si(&mut m, lean_mpz_val(a2), lean_scalar_to_int(a1) as c_long);
    } else if lean_is_scalar(a2) {
        mpz_mul_si(&mut m, lean_mpz_val(a1), lean_scalar_to_int(a2) as c_long);
    } else {
        mpz_mul(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
    }
    mpz_to_int(&mut m)
}

pub unsafe fn lean_int_big_div(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) {
        let mut n = uninit_mpzt();
        mpz_init_set_si(&mut n, lean_scalar_to_int(a1) as c_long);
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_tdiv_q(&mut m, &n, lean_mpz_val(a2));
        mpz_clear(&mut n);
        mpz_to_int(&mut m)
    } else if lean_is_scalar(a2) {
        let d = lean_scalar_to_int(a2);
        if d == 0 {
            return a2;
        }
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        if d > 0 {
            mpz_tdiv_q_ui(&mut m, lean_mpz_val(a1), d as c_ulong);
        } else {
            let mut dn = uninit_mpzt();
            mpz_init_set_si(&mut dn, d as c_long);
            mpz_tdiv_q(&mut m, lean_mpz_val(a1), &dn);
            mpz_clear(&mut dn);
        }
        mpz_to_int(&mut m)
    } else {
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_tdiv_q(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        mpz_to_int(&mut m)
    }
}

pub unsafe fn lean_int_big_div_exact(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) {
        let n = lean_scalar_to_int(a1);
        if n == 0 {
            return a1;
        }
        lean_box((-1i32) as u32 as usize)
    } else if lean_is_scalar(a2) {
        let mut dn = uninit_mpzt();
        mpz_init_set_si(&mut dn, lean_scalar_to_int(a2) as c_long);
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_divexact(&mut m, lean_mpz_val(a1), &dn);
        mpz_clear(&mut dn);
        mpz_to_int(&mut m)
    } else {
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_divexact(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        mpz_to_int(&mut m)
    }
}

pub unsafe fn lean_int_big_mod(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) {
        let mut n = uninit_mpzt();
        mpz_init_set_si(&mut n, lean_scalar_to_int(a1) as c_long);
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_tdiv_r(&mut m, &n, lean_mpz_val(a2));
        mpz_clear(&mut n);
        mpz_to_int(&mut m)
    } else if lean_is_scalar(a2) {
        let i2 = lean_scalar_to_int(a2);
        if i2 == 0 {
            lean_inc(a1);
            return a1;
        }
        let mut d = uninit_mpzt();
        mpz_init_set_si(&mut d, i2 as c_long);
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_tdiv_r(&mut m, lean_mpz_val(a1), &d);
        mpz_clear(&mut d);
        mpz_to_int(&mut m)
    } else {
        let mut m = uninit_mpzt();
        mpz_init(&mut m);
        mpz_tdiv_r(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        mpz_to_int(&mut m)
    }
}

unsafe fn ediv_impl(n: *const mpz_t, d: *const mpz_t) -> mpz_t {
    let mut result = uninit_mpzt();
    mpz_init(&mut result);
    let mut r = uninit_mpzt();
    mpz_init(&mut r);
    mpz_tdiv_qr(&mut result, &mut r, n, d);
    if mpz_sgn(&r) < 0 {
        if mpz_sgn(d) > 0 {
            mpz_sub_ui(&mut result, &result, 1);
        } else {
            mpz_add_ui(&mut result, &result, 1);
        }
    }
    mpz_clear(&mut r);
    result
}

unsafe fn emod_impl(n: *const mpz_t, d: *const mpz_t) -> mpz_t {
    let mut result = uninit_mpzt();
    mpz_init(&mut result);
    mpz_tdiv_r(&mut result, n, d);
    if mpz_sgn(&result) < 0 {
        if mpz_sgn(d) > 0 {
            mpz_add(&mut result, &result, d);
        } else {
            mpz_sub(&mut result, &result, d);
        }
    }
    result
}

pub unsafe fn lean_int_big_ediv(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) {
        let mut n = uninit_mpzt();
        mpz_init_set_si(&mut n, lean_scalar_to_int(a1) as c_long);
        let mut m = ediv_impl(&n, lean_mpz_val(a2));
        mpz_clear(&mut n);
        mpz_to_int(&mut m)
    } else if lean_is_scalar(a2) {
        let d = lean_scalar_to_int(a2);
        if d == 0 {
            return a2;
        }
        let mut dn = uninit_mpzt();
        mpz_init_set_si(&mut dn, d as c_long);
        let mut m = ediv_impl(lean_mpz_val(a1), &dn);
        mpz_clear(&mut dn);
        mpz_to_int(&mut m)
    } else {
        let mut m = ediv_impl(lean_mpz_val(a1), lean_mpz_val(a2));
        mpz_to_int(&mut m)
    }
}

pub unsafe fn lean_int_big_emod(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a1) {
        let mut n = uninit_mpzt();
        mpz_init_set_si(&mut n, lean_scalar_to_int(a1) as c_long);
        let mut m = emod_impl(&n, lean_mpz_val(a2));
        mpz_clear(&mut n);
        mpz_to_int(&mut m)
    } else if lean_is_scalar(a2) {
        let i2 = lean_scalar_to_int(a2);
        if i2 == 0 {
            lean_inc(a1);
            return a1;
        }
        let mut dn = uninit_mpzt();
        mpz_init_set_si(&mut dn, i2 as c_long);
        let mut m = emod_impl(lean_mpz_val(a1), &dn);
        mpz_clear(&mut dn);
        mpz_to_int(&mut m)
    } else {
        let mut m = emod_impl(lean_mpz_val(a1), lean_mpz_val(a2));
        mpz_to_int(&mut m)
    }
}

pub unsafe fn lean_int_big_eq(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if lean_is_scalar(a1) || lean_is_scalar(a2) {
        return false;
    }
    mpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) == 0
}

pub unsafe fn lean_int_big_le(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if lean_is_scalar(a1) {
        mpz_cmp_si(lean_mpz_val(a2), lean_scalar_to_int(a1) as c_long) >= 0
    } else if lean_is_scalar(a2) {
        mpz_cmp_si(lean_mpz_val(a1), lean_scalar_to_int(a2) as c_long) <= 0
    } else {
        mpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) <= 0
    }
}

pub unsafe fn lean_int_big_lt(a1: *const LeanObject, a2: *const LeanObject) -> bool {
    if lean_is_scalar(a1) {
        mpz_cmp_si(lean_mpz_val(a2), lean_scalar_to_int(a1) as c_long) > 0
    } else if lean_is_scalar(a2) {
        mpz_cmp_si(lean_mpz_val(a1), lean_scalar_to_int(a2) as c_long) < 0
    } else {
        mpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) < 0
    }
}

pub unsafe fn lean_int_big_nonneg(a: *const LeanObject) -> bool {
    mpz_sgn(lean_mpz_val(a)) >= 0
}

// ── UInt ────────────────────────────────────────────────────────────────

unsafe fn fdiv_r_2exp_ui(m: *const mpz_t, bits: u64) -> u64 {
    let mut tmp = uninit_mpzt();
    mpz_init(&mut tmp);
    mpz_fdiv_r_2exp(&mut tmp, m, bits);
    let v = mpz_get_ui(&tmp) as u64;
    mpz_clear(&mut tmp);
    v
}

unsafe fn fdiv_q_2exp_ui(m: *const mpz_t, bits: u64) -> u64 {
    let mut tmp = uninit_mpzt();
    mpz_init(&mut tmp);
    mpz_fdiv_q_2exp(&mut tmp, m, bits);
    let v = mpz_get_ui(&tmp) as u64;
    mpz_clear(&mut tmp);
    v
}

unsafe fn mod64(m: *const mpz_t) -> u64 {
    let mut r = uninit_mpzt();
    mpz_init(&mut r);
    mpz_fdiv_r_2exp(&mut r, m, 64);
    let lo = fdiv_r_2exp_ui(&r, 32);
    let hi = fdiv_q_2exp_ui(&r, 32);
    mpz_clear(&mut r);
    lo | (hi << 32)
}

pub unsafe fn lean_uint8_of_big_nat(a: *const LeanObject) -> u8 {
    fdiv_r_2exp_ui(lean_mpz_val(a), 8) as u8
}

pub unsafe fn lean_uint16_of_big_nat(a: *const LeanObject) -> u16 {
    fdiv_r_2exp_ui(lean_mpz_val(a), 16) as u16
}

pub unsafe fn lean_uint32_of_big_nat(a: *const LeanObject) -> u32 {
    fdiv_r_2exp_ui(lean_mpz_val(a), 32) as u32
}

pub unsafe fn lean_uint64_of_big_nat(a: *const LeanObject) -> u64 {
    mod64(lean_mpz_val(a))
}

pub unsafe fn lean_usize_of_big_nat(a: *const LeanObject) -> usize {
    mpz_get_size_t(lean_mpz_val(a))
}

// ── IntX ────────────────────────────────────────────────────────────────

pub unsafe fn lean_int8_of_big_int(a: *const LeanObject) -> i8 {
    fdiv_r_2exp_ui(lean_mpz_val(a), 8) as u8 as i8
}

pub unsafe fn lean_int16_of_big_int(a: *const LeanObject) -> i16 {
    fdiv_r_2exp_ui(lean_mpz_val(a), 16) as u16 as i16
}

pub unsafe fn lean_int32_of_big_int(a: *const LeanObject) -> i32 {
    fdiv_r_2exp_ui(lean_mpz_val(a), 32) as u32 as i32
}

pub unsafe fn lean_int64_of_big_int(a: *const LeanObject) -> i64 {
    mod64(lean_mpz_val(a)) as i64
}

pub unsafe fn lean_isize_of_big_int(a: *const LeanObject) -> isize {
    if core::mem::size_of::<isize>() == 8 {
        mod64(lean_mpz_val(a)) as i64 as isize
    } else {
        fdiv_r_2exp_ui(lean_mpz_val(a), 32) as u32 as i32 as isize
    }
}
