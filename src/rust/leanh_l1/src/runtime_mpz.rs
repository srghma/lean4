// Port of src/runtime/mpz.cpp (GMP path only)
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
//
// The lean::mpz class is embedded by value in lean_mpz_object (lean.h).
// Its memory layout must match exactly.
//
// In C GMP, mpz_t is a one-element __mpz_struct array. gmp-mpfr-sys exposes
// the underlying value as a single mpz_t struct, so Rust code should not wrap
// it in another singleton array.
//
// All functions are exported with C++ mangled names so existing C++ callers
// link without modification.  The C++ shim mpz_helpers.cpp provides
// to_string() and operator<< which need std::string/ostream ABI.

use core::ffi::{c_int, c_long, c_ulong};
use core::ptr::NonNull;
use gmp_mpfr_sys::gmp::{
    mpz_add, mpz_add_ui, mpz_and, mpz_clear, mpz_cmp as gmp_mpz_cmp, mpz_cmp_si, mpz_cmp_ui,
    mpz_divexact as gmp_mpz_divexact, mpz_fdiv_q_2exp, mpz_fdiv_r_2exp, mpz_fits_sint_p,
    mpz_fits_uint_p, mpz_gcd, mpz_get_si, mpz_get_ui, mpz_getlimbn, mpz_init, mpz_init_set,
    mpz_init_set_si, mpz_init_set_str, mpz_init_set_ui, mpz_ior, mpz_mul, mpz_mul_2exp, mpz_mul_si,
    mpz_mul_ui, mpz_neg, mpz_pow_ui, mpz_set, mpz_size, mpz_sizeinbase, mpz_sub, mpz_sub_ui, mpz_t,
    mpz_tdiv_q, mpz_tdiv_q_2exp, mpz_tdiv_q_ui, mpz_tdiv_qr, mpz_tdiv_r, mpz_xor,
};

// mpz_sgn is a GMP macro; implement it directly from the struct fields.
// lean::mpz::sgn() const
#[inline]
pub unsafe fn mpz_sgn(op: *const mpz_t) -> c_int {
    let size = (*op).size;
    if size < 0 {
        -1
    } else if size > 0 {
        1
    } else {
        0
    }
}

// Zero-initialised mpz_t suitable for stack allocation before mpz_init.
#[inline]
pub(crate) fn uninit_mpzt() -> mpz_t {
    mpz_t {
        alloc: 0,
        size: 0,
        d: NonNull::dangling(),
    }
}

// lean::mpz::mpz()
pub use gmp_mpfr_sys::gmp::mpz_init as mpz_ctor_default;

// lean::mpz::mpz(char const*)
pub unsafe fn mpz_ctor_str(self_: *mut mpz_t, s: *const core::ffi::c_char) {
    mpz_init_set_str(self_, s, 10);
}

// lean::mpz::mpz(unsigned int)
pub unsafe fn mpz_ctor_uint(self_: *mut mpz_t, v: u32) {
    mpz_init_set_ui(self_, v as c_ulong);
}

// lean::mpz::mpz(int)
pub unsafe fn mpz_ctor_int(self_: *mut mpz_t, v: i32) {
    mpz_init_set_si(self_, v as c_long);
}

// lean::mpz::mpz(uint64)  — uint64 = unsigned long on Linux x64 → mangled 'm'
pub unsafe fn mpz_ctor_uint64(self_: *mut mpz_t, v: u64) {
    // Lower 32 bits, then add upper 32 shifted left (portable across 32/64-bit GMP).
    mpz_init_set_ui(self_, (v as u32) as c_ulong);
    let hi = (v >> 32) as u32;
    if hi != 0 {
        let mut tmp = uninit_mpzt();
        mpz_init_set_ui(&mut tmp, hi as c_ulong);
        mpz_mul_2exp(&mut tmp, &tmp, 32);
        mpz_add(self_, self_, &tmp);
        mpz_clear(&mut tmp);
    }
}

// lean::mpz::mpz(int64) — int64 = long on Linux x64 → mangled 'l'
pub unsafe fn mpz_ctor_int64(self_: *mut mpz_t, v: i64) {
    let w: u64 = if v < 0 {
        (-(v as i128)) as u64
    } else {
        v as u64
    };
    mpz_ctor_uint64(self_, w);
    if v < 0 {
        mpz_neg(self_, self_);
    }
}

// lean::mpz::mpz(mpz const&)
pub unsafe fn mpz_ctor_copy(self_: *mut mpz_t, other: *const mpz_t) {
    mpz_init_set(self_, other);
}

// lean::mpz::mpz(mpz&&)  — move constructor: init to 0, swap
pub unsafe fn mpz_ctor_move(self_: *mut mpz_t, other: *mut mpz_t) {
    mpz_init(self_);
    mpz_swap(self_, other);
}

// lean::mpz::mpz(__mpz_struct const*)  — construct from raw mpz_t pointer
pub unsafe fn mpz_ctor_mpzt(self_: *mut mpz_t, v: *const mpz_t) {
    mpz_init_set(self_, v);
}

// lean::mpz::~mpz()
pub unsafe fn mpz_dtor(self_: *mut mpz_t) {
    mpz_clear(self_);
}

// lean::mpz::set(mpz_t r) const  — copies self's value into raw mpz_t r
pub unsafe fn mpz_set_raw(self_: *const mpz_t, r: *mut mpz_t) {
    mpz_set(r, self_);
}

// lean::swap(mpz&, mpz&)
pub use gmp_mpfr_sys::gmp::mpz_swap;

// lean::mpz::is_int() const
pub unsafe fn mpz_is_int(self_: *const mpz_t) -> bool {
    mpz_fits_sint_p(self_) != 0
}

// lean::mpz::is_unsigned_int() const
pub unsafe fn mpz_is_unsigned_int(self_: *const mpz_t) -> bool {
    mpz_fits_uint_p(self_) != 0
}

// lean::mpz::is_size_t() const
pub unsafe fn mpz_is_size_t(self_: *const mpz_t) -> bool {
    // sizeof(size_t) == sizeof(mp_limb_t) on LP64; nonneg AND at most one limb
    mpz_sgn(self_) >= 0 && mpz_size(self_) <= 1
}

// lean::mpz::get_int() const
pub unsafe fn mpz_get_int(self_: *const mpz_t) -> i32 {
    mpz_get_si(self_) as i32
}

// lean::mpz::get_unsigned_int() const
pub unsafe fn mpz_get_unsigned_int(self_: *const mpz_t) -> u32 {
    mpz_get_ui(self_) as u32
}

// lean::mpz::get_size_t() const
pub unsafe fn mpz_get_size_t(self_: *const mpz_t) -> usize {
    mpz_getlimbn(self_, 0) as usize
}

// lean::cmp(mpz const&, mpz const&)
pub unsafe fn mpz_cmp(a: *const mpz_t, b: *const mpz_t) -> c_int {
    gmp_mpz_cmp(a, b)
}

// lean::cmp(mpz const&, unsigned)
pub unsafe fn mpz_cmp_uint(a: *const mpz_t, b: u32) -> c_int {
    mpz_cmp_ui(a, b as c_ulong)
}

// lean::cmp(mpz const&, int)
pub unsafe fn mpz_cmp_int(a: *const mpz_t, b: i32) -> c_int {
    mpz_cmp_si(a, b as c_long)
}

// In-place binary operators: self op= other; return self
macro_rules! binop {
    ($fn_name:ident, $gmp_fn:ident) => {
        pub unsafe fn $fn_name(self_: *mut mpz_t, other: *const mpz_t) -> *mut mpz_t {
            $gmp_fn(self_, self_, other);
            self_
        }
    };
}
binop!(mpz_add_assign, mpz_add);
binop!(mpz_sub_assign, mpz_sub);
binop!(mpz_mul_assign, mpz_mul);
binop!(mpz_div_assign_mpz, mpz_tdiv_q);
binop!(mpz_rem_assign, mpz_tdiv_r);
binop!(mpz_and_assign, mpz_and);
binop!(mpz_or_assign, mpz_ior);
binop!(mpz_xor_assign, mpz_xor);

// += unsigned
pub unsafe fn mpz_add_uint(self_: *mut mpz_t, u: u32) -> *mut mpz_t {
    mpz_add_ui(self_, self_, u as c_ulong);
    self_
}
// -= unsigned
pub unsafe fn mpz_sub_uint(self_: *mut mpz_t, u: u32) -> *mut mpz_t {
    mpz_sub_ui(self_, self_, u as c_ulong);
    self_
}
// *= unsigned
pub unsafe fn mpz_mul_uint(self_: *mut mpz_t, u: u32) -> *mut mpz_t {
    mpz_mul_ui(self_, self_, u as c_ulong);
    self_
}
// /= unsigned
pub unsafe fn mpz_div_uint(self_: *mut mpz_t, u: u32) -> *mut mpz_t {
    mpz_tdiv_q_ui(self_, self_, u as c_ulong);
    self_
}
// += int
pub unsafe fn mpz_add_int(self_: *mut mpz_t, u: i32) -> *mut mpz_t {
    if u >= 0 {
        mpz_add_ui(self_, self_, u as c_ulong);
    } else {
        mpz_sub_ui(self_, self_, (-(u as i64)) as c_ulong);
    }
    self_
}
// -= int
pub unsafe fn mpz_sub_int(self_: *mut mpz_t, u: i32) -> *mut mpz_t {
    if u >= 0 {
        mpz_sub_ui(self_, self_, u as c_ulong);
    } else {
        mpz_add_ui(self_, self_, (-(u as i64)) as c_ulong);
    }
    self_
}
// *= int
pub unsafe fn mpz_mul_int(self_: *mut mpz_t, u: i32) -> *mut mpz_t {
    mpz_mul_si(self_, self_, u as c_long);
    self_
}

// lean::mpz::pow(unsigned) const — returns mpz via hidden first-arg (SRET)
pub unsafe fn mpz_pow(result: *mut mpz_t, self_: *const mpz_t, exp: u32) {
    mpz_init(result);
    mpz_pow_ui(result, self_, exp as c_ulong);
}

// lean::mpz::log2() const
pub unsafe fn mpz_log2(self_: *const mpz_t) -> usize {
    if mpz_sgn(self_) <= 0 {
        return 0;
    }
    let r = mpz_sizeinbase(self_, 2);
    if r > 0 { r - 1 } else { 0 }
}

// lean::mul2k(mpz&, mpz const&, unsigned)
pub unsafe fn mul2k(a: *mut mpz_t, b: *const mpz_t, k: u32) {
    mpz_mul_2exp(a, b, k as u64);
}

// lean::div2k(mpz&, mpz const&, unsigned)
pub unsafe fn div2k(a: *mut mpz_t, b: *const mpz_t, k: u32) {
    mpz_tdiv_q_2exp(a, b, k as u64);
}

// Helpers for mod/smod: floor division remainder for 2^bits (returns low 32 bits)
pub unsafe fn fdiv_r_2exp_ui(self_: *const mpz_t, bits: u64) -> u64 {
    let mut tmp = uninit_mpzt();
    mpz_init(&mut tmp);
    mpz_fdiv_r_2exp(&mut tmp, self_, bits);
    let v = mpz_get_ui(&tmp) as u64;
    mpz_clear(&mut tmp);
    v
}
pub unsafe fn fdiv_q_2exp_ui(self_: *const mpz_t, bits: u64) -> u64 {
    let mut tmp = uninit_mpzt();
    mpz_init(&mut tmp);
    mpz_fdiv_q_2exp(&mut tmp, self_, bits);
    let v = mpz_get_ui(&tmp) as u64;
    mpz_clear(&mut tmp);
    v
}

pub unsafe fn mpz_mod8(self_: *const mpz_t) -> u8 {
    fdiv_r_2exp_ui(self_, 8) as u8
}
pub unsafe fn mpz_mod16(self_: *const mpz_t) -> u16 {
    fdiv_r_2exp_ui(self_, 16) as u16
}
pub unsafe fn mpz_mod32(self_: *const mpz_t) -> u32 {
    fdiv_r_2exp_ui(self_, 32) as u32
}
pub unsafe fn mpz_mod64(self_: *const mpz_t) -> u64 {
    let mut r = uninit_mpzt();
    mpz_init(&mut r);
    mpz_fdiv_r_2exp(&mut r, self_, 64);
    let lo = fdiv_r_2exp_ui(&r, 32);
    let hi = fdiv_q_2exp_ui(&r, 32);
    mpz_clear(&mut r);
    lo | (hi << 32)
}
pub unsafe fn mpz_smod8(self_: *const mpz_t) -> i8 {
    mpz_mod8(self_) as i8
}
pub unsafe fn mpz_smod16(self_: *const mpz_t) -> i16 {
    mpz_mod16(self_) as i16
}
pub unsafe fn mpz_smod32(self_: *const mpz_t) -> i32 {
    mpz_mod32(self_) as i32
}
pub unsafe fn mpz_smod64(self_: *const mpz_t) -> i64 {
    mpz_mod64(self_) as i64
}

// lean::mpz::ediv(mpz const&, mpz const&) static — SRET result
pub unsafe fn mpz_ediv(result: *mut mpz_t, n: *const mpz_t, d: *const mpz_t) {
    mpz_init(result);
    let mut r = uninit_mpzt();
    mpz_init(&mut r);
    mpz_tdiv_qr(result, &mut r, n, d);
    if mpz_sgn(&r) < 0 {
        if mpz_sgn(d) > 0 {
            mpz_sub_ui(result, result, 1);
        } else {
            mpz_add_ui(result, result, 1);
        }
    }
    mpz_clear(&mut r);
}

// lean::mpz::emod(mpz const&, mpz const&) static — SRET result
pub unsafe fn mpz_emod(result: *mut mpz_t, n: *const mpz_t, d: *const mpz_t) {
    mpz_init(result);
    mpz_tdiv_r(result, n, d);
    if mpz_sgn(result) < 0 {
        if mpz_sgn(d) > 0 {
            mpz_add(result, result, d);
        } else {
            mpz_sub(result, result, d);
        }
    }
}

// lean::mpz::divexact(mpz const&, mpz const&) static — SRET result
pub unsafe fn mpz_divexact(result: *mut mpz_t, n: *const mpz_t, d: *const mpz_t) {
    mpz_init(result);
    gmp_mpz_divexact(result, n, d);
}

// lean::power(mpz&, mpz const&, unsigned)
pub unsafe fn power_fn(a: *mut mpz_t, b: *const mpz_t, k: u32) {
    mpz_pow_ui(a, b, k as c_ulong);
}

// lean::gcd(mpz&, mpz const&, mpz const&)
pub unsafe fn gcd_fn(g: *mut mpz_t, a: *const mpz_t, b: *const mpz_t) {
    mpz_gcd(g, a, b);
}
