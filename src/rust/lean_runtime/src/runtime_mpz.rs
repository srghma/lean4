// Port of src/runtime/mpz.cpp
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// The C++ `lean::mpz` class is embedded by value inside `lean_mpz_object`
// (defined in lean.h).  Its memory layout therefore cannot change.
//
// Two compilation paths:
//   cfg(lean_use_gmp)   — wraps GMP's mpz_t via extern "C" mpz_* functions
//   cfg(not(lean_use_gmp)) — uses the hand-rolled mpn_* routines from runtime_mpn.rs
//
// The exported symbols use C++ mangled names so that existing C++ callers
// (compact.cpp, object.cpp, ir_interpreter.cpp …) link without modification.

mod runtime_mpz_impl {
    use core::ffi::{c_char, c_int};

    // -----------------------------------------------------------------------
    // mpn_digit type (u32 on 32-bit platforms, u32 always per mpn.h)
    // lean/lean.h typedef: `typedef unsigned mpn_digit;`
    // -----------------------------------------------------------------------
    type MpnDigit = u32;

    // -----------------------------------------------------------------------
    // GMP C-API declarations (used when cfg(lean_use_gmp))
    // -----------------------------------------------------------------------
    #[cfg(lean_use_gmp)]
    mod gmp_sys {
        use core::ffi::{c_char, c_int, c_long, c_ulong};

        // GMP's __mpz_struct — three fields, matches gmp.h exactly.
        #[repr(C)]
        pub struct MpzStruct {
            pub _mp_alloc: c_int,
            pub _mp_size: c_int,
            pub _mp_d: *mut u64, // mp_limb_t — 64-bit on LP64
        }

        // mpz_t is [__mpz_struct; 1]
        pub type MpzT = [MpzStruct; 1];

        extern "C" {
            pub fn __gmpz_init(x: *mut MpzT);
            pub fn __gmpz_init_set(rop: *mut MpzT, op: *const MpzT);
            pub fn __gmpz_init_set_str(rop: *mut MpzT, str: *const c_char, base: c_int) -> c_int;
            pub fn __gmpz_init_set_ui(rop: *mut MpzT, op: c_ulong);
            pub fn __gmpz_init_set_si(rop: *mut MpzT, op: c_long);
            pub fn __gmpz_clear(x: *mut MpzT);
            pub fn __gmpz_set(rop: *mut MpzT, op: *const MpzT);
            pub fn __gmpz_set_str(rop: *mut MpzT, str: *const c_char, base: c_int) -> c_int;
            pub fn __gmpz_set_ui(rop: *mut MpzT, op: c_ulong);
            pub fn __gmpz_set_si(rop: *mut MpzT, op: c_long);
            pub fn __gmpz_swap(rop1: *mut MpzT, rop2: *mut MpzT);
            pub fn __gmpz_sgn_func(op: *const MpzT) -> c_int; // actually a macro; use mpz_sgn
            pub fn __gmpz_fits_sint_p(op: *const MpzT) -> c_int;
            pub fn __gmpz_fits_uint_p(op: *const MpzT) -> c_int;
            pub fn __gmpz_size(op: *const MpzT) -> usize;
            pub fn __gmpz_getlimbn(op: *const MpzT, n: usize) -> u64;
            pub fn __gmpz_get_si(op: *const MpzT) -> c_long;
            pub fn __gmpz_get_ui(op: *const MpzT) -> c_ulong;
            pub fn __gmpz_get_str(str: *mut c_char, base: c_int, op: *const MpzT) -> *mut c_char;
            pub fn __gmpz_sizeinbase(op: *const MpzT, base: c_int) -> usize;
            pub fn __gmpz_cmp(op1: *const MpzT, op2: *const MpzT) -> c_int;
            pub fn __gmpz_cmp_ui(op1: *const MpzT, op2: c_ulong) -> c_int;
            pub fn __gmpz_cmp_si(op1: *const MpzT, op2: c_long) -> c_int;
            pub fn __gmpz_add(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
            pub fn __gmpz_add_ui(rop: *mut MpzT, op1: *const MpzT, op2: c_ulong);
            pub fn __gmpz_sub(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
            pub fn __gmpz_sub_ui(rop: *mut MpzT, op1: *const MpzT, op2: c_ulong);
            pub fn __gmpz_ui_sub(rop: *mut MpzT, op1: c_ulong, op2: *const MpzT);
            pub fn __gmpz_mul(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
            pub fn __gmpz_mul_ui(rop: *mut MpzT, op1: *const MpzT, op2: c_ulong);
            pub fn __gmpz_mul_si(rop: *mut MpzT, op1: *const MpzT, op2: c_long);
            pub fn __gmpz_mul_2exp(rop: *mut MpzT, op1: *const MpzT, op2: u64);
            pub fn __gmpz_neg(rop: *mut MpzT, op: *const MpzT);
            pub fn __gmpz_abs(rop: *mut MpzT, op: *const MpzT);
            pub fn __gmpz_tdiv_q(q: *mut MpzT, n: *const MpzT, d: *const MpzT);
            pub fn __gmpz_tdiv_q_ui(q: *mut MpzT, n: *const MpzT, d: c_ulong);
            pub fn __gmpz_tdiv_q_2exp(q: *mut MpzT, n: *const MpzT, b: u64);
            pub fn __gmpz_tdiv_qr(q: *mut MpzT, r: *mut MpzT, n: *const MpzT, d: *const MpzT);
            pub fn __gmpz_tdiv_r(r: *mut MpzT, n: *const MpzT, d: *const MpzT);
            pub fn __gmpz_divexact(q: *mut MpzT, n: *const MpzT, d: *const MpzT);
            pub fn __gmpz_fdiv_r_2exp(r: *mut MpzT, n: *const MpzT, b: u64);
            pub fn __gmpz_fdiv_q_2exp(q: *mut MpzT, n: *const MpzT, b: u64);
            pub fn __gmpz_pow_ui(rop: *mut MpzT, base: *const MpzT, exp: c_ulong);
            pub fn __gmpz_and(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
            pub fn __gmpz_ior(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
            pub fn __gmpz_xor(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
            pub fn __gmpz_gcd(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
        }

        // mpz_sgn is a GMP macro — implement it directly
        #[inline]
        pub unsafe fn mpz_sgn(op: *const MpzT) -> c_int {
            let size = (*op)[0]._mp_size;
            if size < 0 { -1 } else if size > 0 { 1 } else { 0 }
        }
    }

    // -----------------------------------------------------------------------
    // mpn_* functions from runtime_mpn.rs / mpn.cpp
    // -----------------------------------------------------------------------
    #[cfg(not(lean_use_gmp))]
    extern "C" {
        fn mpn_add(
            a: *const MpnDigit, a_size: usize,
            b: *const MpnDigit, b_size: usize,
            r: *mut MpnDigit, r_size: usize,
            real_sz: *mut usize,
        );
        fn mpn_sub(
            a: *const MpnDigit, a_size: usize,
            b: *const MpnDigit, b_size: usize,
            r: *mut MpnDigit,
            borrow: *mut MpnDigit,
        );
        fn mpn_mul(
            a: *const MpnDigit, a_size: usize,
            b: *const MpnDigit, b_size: usize,
            r: *mut MpnDigit,
        );
        fn mpn_div(
            a: *const MpnDigit, a_size: usize,
            b: *const MpnDigit, b_size: usize,
            q: *mut MpnDigit,
            r: *mut MpnDigit,
        );
        fn mpn_compare(
            a: *const MpnDigit, a_size: usize,
            b: *const MpnDigit, b_size: usize,
        ) -> c_int;
        fn mpn_to_string(
            digits: *const MpnDigit,
            size: usize,
            buf: *mut c_char,
            buf_size: usize,
        ) -> *const c_char;
    }

    // -----------------------------------------------------------------------
    // Allocator helpers (from lean.h / alloc.rs)
    // -----------------------------------------------------------------------
    extern "C" {
        fn lean_internal_panic_out_of_memory() -> !;
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_alloc_mem(size: usize) -> *mut MpnDigit {
        // Use lean's allocator when small, system malloc otherwise.
        // Matches the C++ mpz_alloc() helper.
        extern "C" {
            fn lean_sys_alloc(sz: usize) -> *mut u8;
        }
        let r = lean_sys_alloc(
            size.checked_mul(core::mem::size_of::<MpnDigit>())
                .unwrap_or_else(|| lean_internal_panic_out_of_memory()),
        ) as *mut MpnDigit;
        if r.is_null() {
            lean_internal_panic_out_of_memory()
        }
        r
    }

    #[cfg(not(lean_use_gmp))]
    unsafe fn mpz_free_mem(ptr: *mut MpnDigit, size: usize) {
        extern "C" {
            fn lean_sys_free_sized(ptr: *mut u8, sz: usize);
        }
        lean_sys_free_sized(
            ptr as *mut u8,
            size * core::mem::size_of::<MpnDigit>(),
        );
    }

    // -----------------------------------------------------------------------
    // The Rust mpz struct — layout must match lean.h `struct lean_mpz` /
    // the `mpz` class embedded in `mpz_object`.
    //
    // GMP layout:   [mpz_t m_val]   (= [__mpz_struct; 1])
    // non-GMP layout: [bool m_sign, size_t m_size, mpn_digit* m_digits]
    //
    // We don't define the struct in Rust because it's only ever accessed
    // through the C ABI (the object lives inside a lean_object heap allocation
    // managed by lean.h).  All the methods below are exported as mangled C++
    // symbols so the existing C++ callers link without change.
    // -----------------------------------------------------------------------

    // -----------------------------------------------------------------------
    // GMP implementation
    // -----------------------------------------------------------------------
    #[cfg(lean_use_gmp)]
    mod gmp_impl {
        use super::gmp_sys::*;
        use super::*;
        use core::ffi::{c_char, c_int};

        // Constructors called from the C++ placement-new equivalents.
        // In the Rust port we just export the individual init helpers used by
        // object.cpp / compact.cpp through their mangled names.

        // lean::mpz::mpz()
        #[export_name = "_ZN4lean3mpzC1Ev"]
        pub unsafe extern "C" fn mpz_ctor_default(self_: *mut MpzT) {
            __gmpz_init(self_);
        }

        // lean::mpz::mpz(char const*)
        #[export_name = "_ZN4lean3mpzC1EPKc"]
        pub unsafe extern "C" fn mpz_ctor_str(self_: *mut MpzT, s: *const c_char) {
            __gmpz_init_set_str(self_, s, 10);
        }

        // lean::mpz::mpz(unsigned int)
        #[export_name = "_ZN4lean3mpzC1Ej"]
        pub unsafe extern "C" fn mpz_ctor_uint(self_: *mut MpzT, v: u32) {
            __gmpz_init_set_ui(self_, v as _);
        }

        // lean::mpz::mpz(int)
        #[export_name = "_ZN4lean3mpzC1Ei"]
        pub unsafe extern "C" fn mpz_ctor_int(self_: *mut MpzT, v: i32) {
            __gmpz_init_set_si(self_, v as _);
        }

        // lean::mpz::mpz(uint64)
        #[export_name = "_ZN4lean3mpzC1Ey"]
        pub unsafe extern "C" fn mpz_ctor_uint64(self_: *mut MpzT, v: u64) {
            __gmpz_init_set_ui(self_, (v as u32) as _);
            // Add upper 32 bits: tmp = (v >> 32); tmp <<= 32; self += tmp
            let mut tmp: MpzT = [MpzStruct { _mp_alloc: 0, _mp_size: 0, _mp_d: core::ptr::null_mut() }];
            __gmpz_init_set_ui(&mut tmp, (v >> 32) as _);
            __gmpz_mul_2exp(&mut tmp, &tmp, 32);
            __gmpz_add(self_, self_, &tmp);
            __gmpz_clear(&mut tmp);
        }

        // lean::mpz::mpz(int64)
        #[export_name = "_ZN4lean3mpzC1Ex"]
        pub unsafe extern "C" fn mpz_ctor_int64(self_: *mut MpzT, v: i64) {
            let w: u64 = if v < 0 { -(v as i128) as u64 } else { v as u64 };
            mpz_ctor_uint64(self_, w as u32 as u64);
            let mut tmp: MpzT = [MpzStruct { _mp_alloc: 0, _mp_size: 0, _mp_d: core::ptr::null_mut() }];
            __gmpz_init_set_ui(&mut tmp, (w >> 32) as _);
            __gmpz_mul_2exp(&mut tmp, &tmp, 32);
            __gmpz_add(self_, self_, &tmp);
            __gmpz_clear(&mut tmp);
            if v < 0 {
                __gmpz_neg(self_, self_);
            }
        }

        // lean::mpz::mpz(mpz const&)  — copy
        #[export_name = "_ZN4lean3mpzC1ERKS0_"]
        pub unsafe extern "C" fn mpz_ctor_copy(self_: *mut MpzT, other: *const MpzT) {
            __gmpz_init_set(self_, other);
        }

        // lean::mpz::~mpz()
        #[export_name = "_ZN4lean3mpzD1Ev"]
        pub unsafe extern "C" fn mpz_dtor(self_: *mut MpzT) {
            __gmpz_clear(self_);
        }

        // lean::swap(mpz&, mpz&)
        #[export_name = "_ZN4lean4swapERNS_3mpzES1_"]
        pub unsafe extern "C" fn mpz_swap(a: *mut MpzT, b: *mut MpzT) {
            __gmpz_swap(a, b);
        }

        // lean::mpz::sgn() const
        #[export_name = "_ZNK4lean3mpz3sgnEv"]
        pub unsafe extern "C" fn mpz_sgn(self_: *const MpzT) -> c_int {
            gmp_sys::mpz_sgn(self_)
        }

        // lean::mpz::is_int() const
        #[export_name = "_ZNK4lean3mpz6is_intEv"]
        pub unsafe extern "C" fn mpz_is_int(self_: *const MpzT) -> bool {
            __gmpz_fits_sint_p(self_) != 0
        }

        // lean::mpz::is_unsigned_int() const
        #[export_name = "_ZNK4lean3mpz15is_unsigned_intEv"]
        pub unsafe extern "C" fn mpz_is_unsigned_int(self_: *const MpzT) -> bool {
            __gmpz_fits_uint_p(self_) != 0
        }

        // lean::mpz::is_size_t() const
        #[export_name = "_ZNK4lean3mpz9is_size_tEv"]
        pub unsafe extern "C" fn mpz_is_size_t(self_: *const MpzT) -> bool {
            // GMP: nonneg AND mpz_size <= 1 (one mp_limb_t = one size_t on LP64)
            gmp_sys::mpz_sgn(self_) >= 0 && __gmpz_size(self_) <= 1
        }

        // lean::mpz::get_int() const
        #[export_name = "_ZNK4lean3mpz7get_intEv"]
        pub unsafe extern "C" fn mpz_get_int(self_: *const MpzT) -> i32 {
            __gmpz_get_si(self_) as i32
        }

        // lean::mpz::get_unsigned_int() const
        #[export_name = "_ZNK4lean3mpz16get_unsigned_intEv"]
        pub unsafe extern "C" fn mpz_get_unsigned_int(self_: *const MpzT) -> u32 {
            __gmpz_get_ui(self_) as u32
        }

        // lean::mpz::get_size_t() const
        #[export_name = "_ZNK4lean3mpz10get_size_tEv"]
        pub unsafe extern "C" fn mpz_get_size_t(self_: *const MpzT) -> usize {
            __gmpz_getlimbn(self_, 0) as usize
        }

        // lean::cmp(mpz const&, mpz const&)
        #[export_name = "_ZN4lean3cmpERKNS_3mpzES2_"]
        pub unsafe extern "C" fn mpz_cmp(a: *const MpzT, b: *const MpzT) -> c_int {
            __gmpz_cmp(a, b)
        }

        // lean::cmp(mpz const&, unsigned)
        #[export_name = "_ZN4lean3cmpERKNS_3mpzEj"]
        pub unsafe extern "C" fn mpz_cmp_uint(a: *const MpzT, b: u32) -> c_int {
            __gmpz_cmp_ui(a, b as _)
        }

        // lean::cmp(mpz const&, int)
        #[export_name = "_ZN4lean3cmpERKNS_3mpzEi"]
        pub unsafe extern "C" fn mpz_cmp_int(a: *const MpzT, b: i32) -> c_int {
            __gmpz_cmp_si(a, b as _)
        }

        // Arithmetic in-place operators (all return *mut MpzT = self)
        macro_rules! binop {
            ($export:literal, $fn_name:ident, $gmp_fn:ident) => {
                #[export_name = $export]
                pub unsafe extern "C" fn $fn_name(
                    self_: *mut MpzT,
                    other: *const MpzT,
                ) -> *mut MpzT {
                    $gmp_fn(self_, self_, other);
                    self_
                }
            };
        }
        binop!("_ZN4lean3mpzpLERKS0_", mpz_add_assign, __gmpz_add);
        binop!("_ZN4lean3mpzmIERKS0_", mpz_sub_assign, __gmpz_sub);
        binop!("_ZN4lean3mpzmLERKS0_", mpz_mul_assign, __gmpz_mul);
        binop!("_ZN4lean3mpzdVERKS0_", mpz_div_assign_mpz, __gmpz_tdiv_q);
        binop!("_ZN4lean3mpzrMERKS0_", mpz_rem_assign, __gmpz_tdiv_r);
        binop!("_ZN4lean3mpzaNERKS0_", mpz_and_assign, __gmpz_and);
        binop!("_ZN4lean3mpzoRERKS0_", mpz_or_assign, __gmpz_ior);
        binop!("_ZN4lean3mpzeOERKS0_", mpz_xor_assign, __gmpz_xor);

        // += unsigned
        #[export_name = "_ZN4lean3mpzpLEj"]
        pub unsafe extern "C" fn mpz_add_uint(self_: *mut MpzT, u: u32) -> *mut MpzT {
            __gmpz_add_ui(self_, self_, u as _);
            self_
        }
        // -= unsigned
        #[export_name = "_ZN4lean3mpzmIEj"]
        pub unsafe extern "C" fn mpz_sub_uint(self_: *mut MpzT, u: u32) -> *mut MpzT {
            __gmpz_sub_ui(self_, self_, u as _);
            self_
        }
        // *= unsigned
        #[export_name = "_ZN4lean3mpzmLEj"]
        pub unsafe extern "C" fn mpz_mul_uint(self_: *mut MpzT, u: u32) -> *mut MpzT {
            __gmpz_mul_ui(self_, self_, u as _);
            self_
        }
        // *= int
        #[export_name = "_ZN4lean3mpzmLEi"]
        pub unsafe extern "C" fn mpz_mul_int(self_: *mut MpzT, u: i32) -> *mut MpzT {
            __gmpz_mul_si(self_, self_, u as _);
            self_
        }
        // /= unsigned
        #[export_name = "_ZN4lean3mpzdVEj"]
        pub unsafe extern "C" fn mpz_div_uint(self_: *mut MpzT, u: u32) -> *mut MpzT {
            __gmpz_tdiv_q_ui(self_, self_, u as _);
            self_
        }
        // += int
        #[export_name = "_ZN4lean3mpzpLEi"]
        pub unsafe extern "C" fn mpz_add_int(self_: *mut MpzT, u: i32) -> *mut MpzT {
            if u >= 0 {
                __gmpz_add_ui(self_, self_, u as _);
            } else {
                __gmpz_sub_ui(self_, self_, (-(u as i64)) as _);
            }
            self_
        }
        // -= int
        #[export_name = "_ZN4lean3mpzmIEi"]
        pub unsafe extern "C" fn mpz_sub_int(self_: *mut MpzT, u: i32) -> *mut MpzT {
            if u >= 0 {
                __gmpz_sub_ui(self_, self_, u as _);
            } else {
                __gmpz_add_ui(self_, self_, (-(u as i64)) as _);
            }
            self_
        }

        // lean::mpz::pow(unsigned) const
        #[export_name = "_ZNK4lean3mpz3powEj"]
        pub unsafe extern "C" fn mpz_pow(self_: *const MpzT, exp: u32, result: *mut MpzT) {
            // C++ returns by value; we follow the Itanium ABI hidden-first-arg convention
            __gmpz_init(result);
            __gmpz_pow_ui(result, self_, exp as _);
        }

        // lean::mpz::log2() const
        #[export_name = "_ZNK4lean3mpz4log2Ev"]
        pub unsafe extern "C" fn mpz_log2(self_: *const MpzT) -> usize {
            if gmp_sys::mpz_sgn(self_) <= 0 { return 0; }
            let r = __gmpz_sizeinbase(self_, 2);
            if r > 0 { r - 1 } else { 0 }
        }

        // lean::mul2k(mpz&, mpz const&, unsigned)
        #[export_name = "_ZN4lean4mul2kERNS_3mpzERKS0_j"]
        pub unsafe extern "C" fn mul2k(a: *mut MpzT, b: *const MpzT, k: u32) {
            __gmpz_mul_2exp(a, b, k as u64);
        }

        // lean::div2k(mpz&, mpz const&, unsigned)
        #[export_name = "_ZN4lean4div2kERNS_3mpzERKS0_j"]
        pub unsafe extern "C" fn div2k(a: *mut MpzT, b: *const MpzT, k: u32) {
            __gmpz_tdiv_q_2exp(a, b, k as u64);
        }

        // Modular reduction helpers (mod8/16/32/64, smod8/16/32/64)
        unsafe fn fdiv_r_2exp(self_: *const MpzT, bits: u64) -> u64 {
            let mut tmp: MpzT = [MpzStruct { _mp_alloc: 0, _mp_size: 0, _mp_d: core::ptr::null_mut() }];
            __gmpz_init(&mut tmp);
            __gmpz_fdiv_r_2exp(&mut tmp, self_, bits);
            let lo = __gmpz_get_ui(&tmp) as u64;
            __gmpz_clear(&mut tmp);
            lo
        }
        unsafe fn fdiv_q_2exp_ui(self_: *const MpzT, bits: u64) -> u64 {
            let mut tmp: MpzT = [MpzStruct { _mp_alloc: 0, _mp_size: 0, _mp_d: core::ptr::null_mut() }];
            __gmpz_init(&mut tmp);
            __gmpz_fdiv_q_2exp(&mut tmp, self_, bits);
            let hi = __gmpz_get_ui(&tmp) as u64;
            __gmpz_clear(&mut tmp);
            hi
        }

        #[export_name = "_ZNK4lean3mpz4mod8Ev"]
        pub unsafe extern "C" fn mpz_mod8(self_: *const MpzT) -> u8 { fdiv_r_2exp(self_, 8) as u8 }
        #[export_name = "_ZNK4lean3mpz5mod16Ev"]
        pub unsafe extern "C" fn mpz_mod16(self_: *const MpzT) -> u16 { fdiv_r_2exp(self_, 16) as u16 }
        #[export_name = "_ZNK4lean3mpz5mod32Ev"]
        pub unsafe extern "C" fn mpz_mod32(self_: *const MpzT) -> u32 { fdiv_r_2exp(self_, 32) as u32 }
        #[export_name = "_ZNK4lean3mpz5mod64Ev"]
        pub unsafe extern "C" fn mpz_mod64(self_: *const MpzT) -> u64 {
            let r = fdiv_r_2exp(self_, 64);
            let lo = fdiv_r_2exp(self_, 32);
            let hi = fdiv_q_2exp_ui(self_, 32);
            // Reconstruct 64-bit value from two 32-bit halves
            lo | (hi << 32)
        }
        #[export_name = "_ZNK4lean3mpz5smod8Ev"]
        pub unsafe extern "C" fn mpz_smod8(self_: *const MpzT) -> i8 { mpz_mod8(self_) as i8 }
        #[export_name = "_ZNK4lean3mpz6smod16Ev"]
        pub unsafe extern "C" fn mpz_smod16(self_: *const MpzT) -> i16 { mpz_mod16(self_) as i16 }
        #[export_name = "_ZNK4lean3mpz6smod32Ev"]
        pub unsafe extern "C" fn mpz_smod32(self_: *const MpzT) -> i32 { mpz_mod32(self_) as i32 }
        #[export_name = "_ZNK4lean3mpz6smod64Ev"]
        pub unsafe extern "C" fn mpz_smod64(self_: *const MpzT) -> i64 { mpz_mod64(self_) as i64 }

        // lean::mpz::ediv / emod (static)
        #[export_name = "_ZN4lean3mpz4edivERKS0_S2_"]
        pub unsafe extern "C" fn mpz_ediv(
            result: *mut MpzT,
            n: *const MpzT,
            d: *const MpzT,
        ) {
            // q = n tdiv d
            __gmpz_init(result);
            let mut r: MpzT = [MpzStruct { _mp_alloc: 0, _mp_size: 0, _mp_d: core::ptr::null_mut() }];
            __gmpz_init(&mut r);
            __gmpz_tdiv_qr(result, &mut r, n, d);
            // if r < 0: adjust q
            if gmp_sys::mpz_sgn(&r) < 0 {
                if gmp_sys::mpz_sgn(d) > 0 {
                    __gmpz_sub_ui(result, result, 1);
                } else {
                    __gmpz_add_ui(result, result, 1);
                }
            }
            __gmpz_clear(&mut r);
        }

        #[export_name = "_ZN4lean3mpz4emodERKS0_S2_"]
        pub unsafe extern "C" fn mpz_emod(
            result: *mut MpzT,
            n: *const MpzT,
            d: *const MpzT,
        ) {
            __gmpz_init(result);
            __gmpz_tdiv_r(result, n, d);
            if gmp_sys::mpz_sgn(result) < 0 {
                if gmp_sys::mpz_sgn(d) > 0 {
                    __gmpz_add(result, result, d);
                } else {
                    __gmpz_sub(result, result, d);
                }
            }
        }

        // lean::power(mpz&, mpz const&, unsigned)
        #[export_name = "_ZN4lean5powerERNS_3mpzERKS0_j"]
        pub unsafe extern "C" fn power_fn(a: *mut MpzT, b: *const MpzT, k: u32) {
            __gmpz_pow_ui(a, b, k as _);
        }

        // lean::gcd(mpz&, mpz const&, mpz const&)
        #[export_name = "_ZN4lean3gcdERNS_3mpzERKS0_S3_"]
        pub unsafe extern "C" fn gcd_fn(g: *mut MpzT, a: *const MpzT, b: *const MpzT) {
            __gmpz_gcd(g, a, b);
        }

        // lean::mpz::to_string() const  — returns std::string via hidden-arg ABI
        // This is complex to replicate correctly; we use a C++ shim instead.
        // See mpz_shims.cpp: lean_mpz_to_string_cstr(mpz*, buf, buflen) -> char*
    }

    // -----------------------------------------------------------------------
    // Non-GMP implementation
    // -----------------------------------------------------------------------
    #[cfg(not(lean_use_gmp))]
    mod non_gmp_impl {
        use super::*;
        use core::ffi::{c_char, c_int};

        // The non-GMP mpz layout (must match lean.h exactly):
        //   bool        m_sign;
        //   size_t      m_size;
        //   mpn_digit * m_digits;
        #[repr(C)]
        pub struct MpzNonGmp {
            pub m_sign: bool,
            pub m_size: usize,
            pub m_digits: *mut MpnDigit,
        }

        impl MpzNonGmp {
            #[inline]
            pub unsafe fn is_zero(&self) -> bool {
                self.m_size == 1 && *self.m_digits == 0
            }

            #[inline]
            pub unsafe fn sgn(&self) -> c_int {
                if self.is_zero() { 0 } else if self.m_sign { -1 } else { 1 }
            }

            /// Replace digits with a new allocation of size `sz`.
            pub unsafe fn set_digits(&mut self, digits: *const MpnDigit, mut sz: usize) {
                // Trim leading zeros
                while sz > 1 && *digits.add(sz - 1) == 0 {
                    sz -= 1;
                }
                if sz != self.m_size {
                    mpz_free_mem(self.m_digits, self.m_size);
                    self.m_digits = mpz_alloc_mem(sz);
                    self.m_size = sz;
                }
                core::ptr::copy_nonoverlapping(digits, self.m_digits, sz);
            }

            pub unsafe fn init_uint(&mut self, v: u32) {
                self.m_digits = mpz_alloc_mem(1);
                self.m_sign = false;
                self.m_size = 1;
                *self.m_digits = v;
            }

            pub unsafe fn init_int(&mut self, v: i32) {
                self.m_digits = mpz_alloc_mem(1);
                self.m_size = 1;
                if v < 0 {
                    self.m_sign = true;
                    *self.m_digits = (-(v as i64)) as MpnDigit;
                } else {
                    self.m_sign = false;
                    *self.m_digits = v as MpnDigit;
                }
            }

            pub unsafe fn init_uint64(&mut self, v: u64) {
                self.m_sign = false;
                if v <= u32::MAX as u64 {
                    self.m_digits = mpz_alloc_mem(1);
                    self.m_size = 1;
                    *self.m_digits = v as MpnDigit;
                } else {
                    self.m_digits = mpz_alloc_mem(2);
                    self.m_size = 2;
                    *self.m_digits = v as MpnDigit;
                    *self.m_digits.add(1) = (v >> 32) as MpnDigit;
                }
            }

            pub unsafe fn init_int64(&mut self, v: i64) {
                if v >= 0 {
                    self.init_uint64(v as u64);
                } else {
                    self.init_uint64((-(v as i128)) as u64);
                    self.m_sign = true;
                }
            }

            pub unsafe fn init_copy(&mut self, other: &MpzNonGmp) {
                self.m_sign = other.m_sign;
                self.m_size = other.m_size;
                self.m_digits = mpz_alloc_mem(other.m_size);
                core::ptr::copy_nonoverlapping(other.m_digits, self.m_digits, other.m_size);
            }

            pub unsafe fn add_inplace(
                &mut self,
                sign: bool,
                sz: usize,
                digits: *const MpnDigit,
            ) {
                const TMP_CAP: usize = 256;
                if self.m_sign == sign {
                    let new_sz = self.m_size.max(sz) + 1;
                    let mut tmp = vec![0u32; new_sz];
                    let mut real_sz: usize = 0;
                    mpn_add(
                        self.m_digits, self.m_size,
                        digits, sz,
                        tmp.as_mut_ptr(), new_sz,
                        &mut real_sz,
                    );
                    self.set_digits(tmp.as_ptr(), real_sz);
                } else {
                    let r = mpn_compare(self.m_digits, self.m_size, digits, sz);
                    if r == 0 {
                        mpz_free_mem(self.m_digits, self.m_size);
                        self.m_digits = mpz_alloc_mem(1);
                        self.m_size = 1;
                        *self.m_digits = 0;
                        self.m_sign = false;
                        return;
                    }
                    let mut borrow: MpnDigit = 0;
                    if r < 0 {
                        let mut tmp = vec![0u32; sz];
                        mpn_sub(digits, sz, self.m_digits, self.m_size, tmp.as_mut_ptr(), &mut borrow);
                        self.m_sign = sign;
                        self.set_digits(tmp.as_ptr(), sz);
                    } else {
                        let mut tmp = vec![0u32; self.m_size];
                        mpn_sub(self.m_digits, self.m_size, digits, sz, tmp.as_mut_ptr(), &mut borrow);
                        self.set_digits(tmp.as_ptr(), self.m_size);
                    }
                }
            }

            pub unsafe fn mul_inplace(
                &mut self,
                sign: bool,
                sz: usize,
                digits: *const MpnDigit,
            ) {
                let new_sz = self.m_size + sz;
                let mut tmp = vec![0u32; new_sz];
                mpn_mul(self.m_digits, self.m_size, digits, sz, tmp.as_mut_ptr());
                self.set_digits(tmp.as_ptr(), new_sz);
                self.m_sign = !self.is_zero() && self.m_sign != sign;
            }

            pub unsafe fn div_inplace(
                &mut self,
                sign: bool,
                sz: usize,
                digits: *const MpnDigit,
            ) {
                if sz > self.m_size {
                    mpz_free_mem(self.m_digits, self.m_size);
                    self.m_digits = mpz_alloc_mem(1);
                    self.m_size = 1;
                    *self.m_digits = 0;
                    self.m_sign = false;
                    return;
                }
                let q_sz = self.m_size - sz + 1;
                let r_sz = sz;
                let mut q = vec![0u32; q_sz];
                let mut r = vec![0u32; r_sz];
                mpn_div(self.m_digits, self.m_size, digits, sz, q.as_mut_ptr(), r.as_mut_ptr());
                self.set_digits(q.as_ptr(), q_sz);
                self.m_sign = !self.is_zero() && self.m_sign != sign;
            }

            pub unsafe fn rem_inplace(&mut self, sz: usize, digits: *const MpnDigit) {
                if sz > self.m_size { return; }
                let q_sz = self.m_size - sz + 1;
                let r_sz = sz;
                let mut q = vec![0u32; q_sz];
                let mut r = vec![0u32; r_sz];
                mpn_div(self.m_digits, self.m_size, digits, sz, q.as_mut_ptr(), r.as_mut_ptr());
                let was_neg = self.m_sign;
                self.set_digits(r.as_ptr(), r_sz);
                self.m_sign = was_neg && !self.is_zero();
            }
        }

        // Constructors
        #[export_name = "_ZN4lean3mpzC1Ev"]
        pub unsafe extern "C" fn mpz_ctor_default(self_: *mut MpzNonGmp) {
            (*self_).m_digits = mpz_alloc_mem(1);
            (*self_).m_sign = false;
            (*self_).m_size = 1;
            *(*self_).m_digits = 0;
        }

        #[export_name = "_ZN4lean3mpzC1EPKc"]
        pub unsafe extern "C" fn mpz_ctor_str(self_: *mut MpzNonGmp, s: *const c_char) {
            mpz_ctor_default(self_);
            // parse decimal string
            let cstr = core::ffi::CStr::from_ptr(s).to_bytes();
            let mut bytes = cstr;
            let mut negative = false;
            while bytes.first() == Some(&b' ') { bytes = &bytes[1..]; }
            if bytes.first() == Some(&b'-') { negative = true; bytes = &bytes[1..]; }
            for &ch in bytes {
                if ch >= b'0' && ch <= b'9' {
                    (*self_).mul_inplace(false, 1, &10u32);
                    let d = (ch - b'0') as u32;
                    (*self_).add_inplace(false, 1, &d);
                }
            }
            if negative { (*self_).m_sign = !(*self_).is_zero(); }
        }

        #[export_name = "_ZN4lean3mpzC1Ej"]
        pub unsafe extern "C" fn mpz_ctor_uint(self_: *mut MpzNonGmp, v: u32) {
            (*self_).init_uint(v);
        }

        #[export_name = "_ZN4lean3mpzC1Ei"]
        pub unsafe extern "C" fn mpz_ctor_int(self_: *mut MpzNonGmp, v: i32) {
            (*self_).init_int(v);
        }

        #[export_name = "_ZN4lean3mpzC1Ey"]
        pub unsafe extern "C" fn mpz_ctor_uint64(self_: *mut MpzNonGmp, v: u64) {
            (*self_).init_uint64(v);
        }

        #[export_name = "_ZN4lean3mpzC1Ex"]
        pub unsafe extern "C" fn mpz_ctor_int64(self_: *mut MpzNonGmp, v: i64) {
            (*self_).init_int64(v);
        }

        #[export_name = "_ZN4lean3mpzC1ERKS0_"]
        pub unsafe extern "C" fn mpz_ctor_copy(self_: *mut MpzNonGmp, other: *const MpzNonGmp) {
            (*self_).init_copy(&*other);
        }

        #[export_name = "_ZN4lean3mpzD1Ev"]
        pub unsafe extern "C" fn mpz_dtor(self_: *mut MpzNonGmp) {
            if !(*self_).m_digits.is_null() {
                mpz_free_mem((*self_).m_digits, (*self_).m_size);
                (*self_).m_digits = core::ptr::null_mut();
            }
        }

        #[export_name = "_ZN4lean4swapERNS_3mpzES1_"]
        pub unsafe extern "C" fn mpz_swap(a: *mut MpzNonGmp, b: *mut MpzNonGmp) {
            core::ptr::swap(a, b);
        }

        #[export_name = "_ZNK4lean3mpz3sgnEv"]
        pub unsafe extern "C" fn mpz_sgn(self_: *const MpzNonGmp) -> c_int {
            (*self_).sgn()
        }

        #[export_name = "_ZNK4lean3mpz6is_intEv"]
        pub unsafe extern "C" fn mpz_is_int(self_: *const MpzNonGmp) -> bool {
            let s = &*self_;
            if s.m_sign {
                s.m_size == 1 && *s.m_digits <= (-(i32::MIN as i64)) as u32
            } else {
                s.m_size == 1 && *s.m_digits <= i32::MAX as u32
            }
        }

        #[export_name = "_ZNK4lean3mpz15is_unsigned_intEv"]
        pub unsafe extern "C" fn mpz_is_unsigned_int(self_: *const MpzNonGmp) -> bool {
            let s = &*self_;
            s.m_size == 1 && !s.m_sign
        }

        #[export_name = "_ZNK4lean3mpz9is_size_tEv"]
        pub unsafe extern "C" fn mpz_is_size_t(self_: *const MpzNonGmp) -> bool {
            let s = &*self_;
            if core::mem::size_of::<usize>() == 8 {
                s.m_size <= 2 && !s.m_sign
            } else {
                s.m_size == 1 && !s.m_sign
            }
        }

        #[export_name = "_ZNK4lean3mpz7get_intEv"]
        pub unsafe extern "C" fn mpz_get_int(self_: *const MpzNonGmp) -> i32 {
            let s = &*self_;
            if s.m_sign { -((*s.m_digits) as i32) } else { *s.m_digits as i32 }
        }

        #[export_name = "_ZNK4lean3mpz16get_unsigned_intEv"]
        pub unsafe extern "C" fn mpz_get_unsigned_int(self_: *const MpzNonGmp) -> u32 {
            *(*self_).m_digits
        }

        #[export_name = "_ZNK4lean3mpz10get_size_tEv"]
        pub unsafe extern "C" fn mpz_get_size_t(self_: *const MpzNonGmp) -> usize {
            let s = &*self_;
            if core::mem::size_of::<usize>() == 8 && s.m_size == 2 {
                (*s.m_digits) as usize | ((*s.m_digits.add(1)) as usize) << 32
            } else {
                (*s.m_digits) as usize
            }
        }

        #[export_name = "_ZN4lean3cmpERKNS_3mpzES2_"]
        pub unsafe extern "C" fn mpz_cmp(a: *const MpzNonGmp, b: *const MpzNonGmp) -> c_int {
            let a = &*a; let b = &*b;
            if a.m_sign {
                if b.m_sign {
                    mpn_compare(b.m_digits, b.m_size, a.m_digits, a.m_size)
                } else { -1 }
            } else {
                if b.m_sign { 1 }
                else { mpn_compare(a.m_digits, a.m_size, b.m_digits, b.m_size) }
            }
        }

        #[export_name = "_ZN4lean3cmpERKNS_3mpzEj"]
        pub unsafe extern "C" fn mpz_cmp_uint(a: *const MpzNonGmp, b: u32) -> c_int {
            if (*a).m_sign { -1 }
            else { mpn_compare((*a).m_digits, (*a).m_size, &b, 1) }
        }

        #[export_name = "_ZN4lean3cmpERKNS_3mpzEi"]
        pub unsafe extern "C" fn mpz_cmp_int(a: *const MpzNonGmp, b: i32) -> c_int {
            if (*a).m_sign {
                if b < 0 {
                    let b1 = (-(b as i64)) as u32;
                    mpn_compare(&b1, 1, (*a).m_digits, (*a).m_size)
                } else { -1 }
            } else {
                if b < 0 { 1 }
                else {
                    let b1 = b as u32;
                    mpn_compare((*a).m_digits, (*a).m_size, &b1, 1)
                }
            }
        }

        // Arithmetic operators — delegate to MpzNonGmp methods
        macro_rules! binop_mpz {
            ($export:literal, $fn_name:ident, $method:ident) => {
                #[export_name = $export]
                pub unsafe extern "C" fn $fn_name(
                    self_: *mut MpzNonGmp, other: *const MpzNonGmp
                ) -> *mut MpzNonGmp {
                    (*self_).$method((*other).m_sign, (*other).m_size, (*other).m_digits);
                    self_
                }
            }
        }
        binop_mpz!("_ZN4lean3mpzpLERKS0_", mpz_add_assign, add_inplace);
        binop_mpz!("_ZN4lean3mpzmIERKS0_", mpz_sub_assign_impl, sub_assign_impl);
        binop_mpz!("_ZN4lean3mpzmLERKS0_", mpz_mul_assign, mul_inplace);
        binop_mpz!("_ZN4lean3mpzdVERKS0_", mpz_div_assign_mpz, div_inplace);

        impl MpzNonGmp {
            // -= mpz: add with flipped sign
            pub unsafe fn sub_assign_impl(&mut self, sign: bool, sz: usize, digits: *const MpnDigit) {
                self.add_inplace(!sign, sz, digits);
            }
        }

        #[export_name = "_ZN4lean3mpzrMERKS0_"]
        pub unsafe extern "C" fn mpz_rem_assign(
            self_: *mut MpzNonGmp, other: *const MpzNonGmp
        ) -> *mut MpzNonGmp {
            (*self_).rem_inplace((*other).m_size, (*other).m_digits);
            self_
        }

        #[export_name = "_ZN4lean3mpzpLEj"]
        pub unsafe extern "C" fn mpz_add_uint(self_: *mut MpzNonGmp, u: u32) -> *mut MpzNonGmp {
            (*self_).add_inplace(false, 1, &u); self_
        }
        #[export_name = "_ZN4lean3mpzmIEj"]
        pub unsafe extern "C" fn mpz_sub_uint(self_: *mut MpzNonGmp, u: u32) -> *mut MpzNonGmp {
            (*self_).add_inplace(true, 1, &u); self_
        }
        #[export_name = "_ZN4lean3mpzmLEj"]
        pub unsafe extern "C" fn mpz_mul_uint(self_: *mut MpzNonGmp, u: u32) -> *mut MpzNonGmp {
            (*self_).mul_inplace(false, 1, &u); self_
        }
        #[export_name = "_ZN4lean3mpzdVEj"]
        pub unsafe extern "C" fn mpz_div_uint(self_: *mut MpzNonGmp, u: u32) -> *mut MpzNonGmp {
            (*self_).div_inplace(false, 1, &u); self_
        }
        #[export_name = "_ZN4lean3mpzpLEi"]
        pub unsafe extern "C" fn mpz_add_int(self_: *mut MpzNonGmp, u: i32) -> *mut MpzNonGmp {
            if u < 0 { let u1 = (-(u as i64)) as u32; (*self_).add_inplace(true, 1, &u1); }
            else { let u1 = u as u32; (*self_).add_inplace(false, 1, &u1); }
            self_
        }
        #[export_name = "_ZN4lean3mpzmIEi"]
        pub unsafe extern "C" fn mpz_sub_int(self_: *mut MpzNonGmp, u: i32) -> *mut MpzNonGmp {
            if u < 0 { let u1 = (-(u as i64)) as u32; (*self_).add_inplace(false, 1, &u1); }
            else { let u1 = u as u32; (*self_).add_inplace(true, 1, &u1); }
            self_
        }
        #[export_name = "_ZN4lean3mpzmLEi"]
        pub unsafe extern "C" fn mpz_mul_int(self_: *mut MpzNonGmp, u: i32) -> *mut MpzNonGmp {
            if u < 0 { let u1 = (-(u as i64)) as u32; (*self_).mul_inplace(true, 1, &u1); }
            else { let u1 = u as u32; (*self_).mul_inplace(false, 1, &u1); }
            self_
        }

        // Bitwise ops via digit-level AND/OR/XOR
        unsafe fn bitwise_op(
            self_: *mut MpzNonGmp,
            other: *const MpzNonGmp,
            op: fn(MpnDigit, MpnDigit) -> MpnDigit,
        ) -> *mut MpzNonGmp {
            let sz = (*self_).m_size.max((*other).m_size);
            let mut r = vec![0u32; sz];
            for i in 0..sz {
                let u = if i < (*self_).m_size { *(*self_).m_digits.add(i) } else { 0 };
                let v = if i < (*other).m_size { *(*other).m_digits.add(i) } else { 0 };
                r[i] = op(u, v);
            }
            (*self_).set_digits(r.as_ptr(), sz);
            self_
        }
        #[export_name = "_ZN4lean3mpzaNERKS0_"]
        pub unsafe extern "C" fn mpz_and_assign(self_: *mut MpzNonGmp, o: *const MpzNonGmp) -> *mut MpzNonGmp {
            bitwise_op(self_, o, |a, b| a & b)
        }
        #[export_name = "_ZN4lean3mpzoRERKS0_"]
        pub unsafe extern "C" fn mpz_or_assign(self_: *mut MpzNonGmp, o: *const MpzNonGmp) -> *mut MpzNonGmp {
            bitwise_op(self_, o, |a, b| a | b)
        }
        #[export_name = "_ZN4lean3mpzeOERKS0_"]
        pub unsafe extern "C" fn mpz_xor_assign(self_: *mut MpzNonGmp, o: *const MpzNonGmp) -> *mut MpzNonGmp {
            bitwise_op(self_, o, |a, b| a ^ b)
        }

        // Modular reductions
        #[export_name = "_ZNK4lean3mpz4mod8Ev"]
        pub unsafe extern "C" fn mpz_mod8(self_: *const MpzNonGmp) -> u8 {
            let r = (*(*self_).m_digits & 0xFF) as u8;
            if (*self_).m_sign { r.wrapping_neg() } else { r }
        }
        #[export_name = "_ZNK4lean3mpz5mod16Ev"]
        pub unsafe extern "C" fn mpz_mod16(self_: *const MpzNonGmp) -> u16 {
            let r = (*(*self_).m_digits & 0xFFFF) as u16;
            if (*self_).m_sign { r.wrapping_neg() } else { r }
        }
        #[export_name = "_ZNK4lean3mpz5mod32Ev"]
        pub unsafe extern "C" fn mpz_mod32(self_: *const MpzNonGmp) -> u32 {
            let r = *(*self_).m_digits;
            if (*self_).m_sign { r.wrapping_neg() } else { r }
        }
        #[export_name = "_ZNK4lean3mpz5mod64Ev"]
        pub unsafe extern "C" fn mpz_mod64(self_: *const MpzNonGmp) -> u64 {
            let s = &*self_;
            let r = if s.m_size == 1 {
                *s.m_digits as u64
            } else {
                (*s.m_digits as u64) | ((*s.m_digits.add(1) as u64) << 32)
            };
            if s.m_sign { r.wrapping_neg() } else { r }
        }
        #[export_name = "_ZNK4lean3mpz5smod8Ev"]
        pub unsafe extern "C" fn mpz_smod8(self_: *const MpzNonGmp) -> i8 { mpz_mod8(self_) as i8 }
        #[export_name = "_ZNK4lean3mpz6smod16Ev"]
        pub unsafe extern "C" fn mpz_smod16(self_: *const MpzNonGmp) -> i16 { mpz_mod16(self_) as i16 }
        #[export_name = "_ZNK4lean3mpz6smod32Ev"]
        pub unsafe extern "C" fn mpz_smod32(self_: *const MpzNonGmp) -> i32 { mpz_mod32(self_) as i32 }
        #[export_name = "_ZNK4lean3mpz6smod64Ev"]
        pub unsafe extern "C" fn mpz_smod64(self_: *const MpzNonGmp) -> i64 { mpz_mod64(self_) as i64 }

        // log2
        #[export_name = "_ZNK4lean3mpz4log2Ev"]
        pub unsafe extern "C" fn mpz_log2(self_: *const MpzNonGmp) -> usize {
            let s = &*self_;
            fn log2_u32(v: u32) -> usize {
                if v == 0 { return 0; }
                (31 - v.leading_zeros()) as usize
            }
            (s.m_size - 1) * 32 + log2_u32(*s.m_digits.add(s.m_size - 1))
        }

        // mul2k / div2k
        #[export_name = "_ZN4lean4mul2kERNS_3mpzERKS0_j"]
        pub unsafe extern "C" fn mul2k(a: *mut MpzNonGmp, b: *const MpzNonGmp, k: u32) {
            // Delegate to C++ shim — shift logic is non-trivial with digit arrays
            extern "C" { fn lean_mpz_mul2k_impl(a: *mut MpzNonGmp, b: *const MpzNonGmp, k: u32); }
            lean_mpz_mul2k_impl(a, b, k);
        }

        #[export_name = "_ZN4lean4div2kERNS_3mpzERKS0_j"]
        pub unsafe extern "C" fn div2k(a: *mut MpzNonGmp, b: *const MpzNonGmp, k: u32) {
            extern "C" { fn lean_mpz_div2k_impl(a: *mut MpzNonGmp, b: *const MpzNonGmp, k: u32); }
            lean_mpz_div2k_impl(a, b, k);
        }

        // ediv / emod
        #[export_name = "_ZN4lean3mpz4edivERKS0_S2_"]
        pub unsafe extern "C" fn mpz_ediv(
            result: *mut MpzNonGmp, n: *const MpzNonGmp, d: *const MpzNonGmp,
        ) {
            extern "C" { fn lean_mpz_ediv_impl(r: *mut MpzNonGmp, n: *const MpzNonGmp, d: *const MpzNonGmp); }
            lean_mpz_ediv_impl(result, n, d);
        }

        #[export_name = "_ZN4lean3mpz4emodERKS0_S2_"]
        pub unsafe extern "C" fn mpz_emod(
            result: *mut MpzNonGmp, n: *const MpzNonGmp, d: *const MpzNonGmp,
        ) {
            extern "C" { fn lean_mpz_emod_impl(r: *mut MpzNonGmp, n: *const MpzNonGmp, d: *const MpzNonGmp); }
            lean_mpz_emod_impl(result, n, d);
        }

        // power / gcd  (delegate to C++ shims — complex iteration)
        #[export_name = "_ZN4lean5powerERNS_3mpzERKS0_j"]
        pub unsafe extern "C" fn power_fn(a: *mut MpzNonGmp, b: *const MpzNonGmp, k: u32) {
            extern "C" { fn lean_mpz_power_impl(a: *mut MpzNonGmp, b: *const MpzNonGmp, k: u32); }
            lean_mpz_power_impl(a, b, k);
        }
        #[export_name = "_ZN4lean3gcdERNS_3mpzERKS0_S3_"]
        pub unsafe extern "C" fn gcd_fn(g: *mut MpzNonGmp, a: *const MpzNonGmp, b: *const MpzNonGmp) {
            extern "C" { fn lean_mpz_gcd_impl(g: *mut MpzNonGmp, a: *const MpzNonGmp, b: *const MpzNonGmp); }
            lean_mpz_gcd_impl(g, a, b);
        }
    }

    // -----------------------------------------------------------------------
    // to_string — shared, uses a C++ shim since std::string ABI is complex
    // -----------------------------------------------------------------------

    // lean::mpz::to_string() const
    // The C++ return-by-value std::string uses hidden-first-arg ABI which is
    // hard to replicate from Rust.  We expose a C helper that writes into a
    // caller-supplied buffer instead, and keep a thin C++ wrapper for the
    // mangled symbol.
    // See mpz_shims.cpp.

    // print(lean::mpz const&) — used only in debug builds, keep in C++.
}
