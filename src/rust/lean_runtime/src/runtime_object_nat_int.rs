/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

// Port of Natural numbers, Integers, UInt, IntX sections from src/runtime/object.cpp.

#[cfg(not(lean_use_gmp))]
compile_error!("runtime_object_nat_int.rs requires lean_use_gmp cfg flag");

#[cfg(lean_use_gmp)]
pub(crate) mod runtime_object_nat_int_impl {
    use super::*;
    use core::ffi::{c_char, c_int, c_long, c_ulong};

    #[repr(C)]
    pub(crate) struct MpzStruct {
        _mp_alloc: c_int,
        _mp_size: c_int,
        _mp_d: *mut u64,
    }
    pub(crate) type MpzT = [MpzStruct; 1];

    #[repr(C)]
    struct LeanMpzObject {
        header: LeanObject,
        value: MpzT,
    }

    extern "C" {
        fn lean_internal_panic(msg: *const c_char) -> !;
        fn __gmpz_init(x: *mut MpzT);
        fn __gmpz_init_set(rop: *mut MpzT, op: *const MpzT);
        fn __gmpz_init_set_str(rop: *mut MpzT, s: *const c_char, base: c_int) -> c_int;
        fn __gmpz_init_set_ui(rop: *mut MpzT, op: c_ulong);
        fn __gmpz_init_set_si(rop: *mut MpzT, op: c_long);
        fn __gmpz_clear(x: *mut MpzT);
        fn __gmpz_set(rop: *mut MpzT, op: *const MpzT);
        fn __gmpz_size(op: *const MpzT) -> usize;
        fn __gmpz_getlimbn(op: *const MpzT, n: usize) -> u64;
        fn __gmpz_get_si(op: *const MpzT) -> c_long;
        fn __gmpz_get_ui(op: *const MpzT) -> c_ulong;
        fn __gmpz_sizeinbase(op: *const MpzT, base: c_int) -> usize;
        fn __gmpz_cmp(op1: *const MpzT, op2: *const MpzT) -> c_int;
        fn __gmpz_cmp_ui(op1: *const MpzT, op2: c_ulong) -> c_int;
        fn __gmpz_cmp_si(op1: *const MpzT, op2: c_long) -> c_int;
        fn __gmpz_add(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
        fn __gmpz_add_ui(rop: *mut MpzT, op1: *const MpzT, op2: c_ulong);
        fn __gmpz_sub(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
        fn __gmpz_sub_ui(rop: *mut MpzT, op1: *const MpzT, op2: c_ulong);
        fn __gmpz_mul(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
        fn __gmpz_mul_ui(rop: *mut MpzT, op1: *const MpzT, op2: c_ulong);
        fn __gmpz_mul_si(rop: *mut MpzT, op1: *const MpzT, op2: c_long);
        fn __gmpz_mul_2exp(rop: *mut MpzT, op1: *const MpzT, op2: u64);
        fn __gmpz_neg(rop: *mut MpzT, op: *const MpzT);
        fn __gmpz_tdiv_q(q: *mut MpzT, n: *const MpzT, d: *const MpzT);
        fn __gmpz_tdiv_q_ui(q: *mut MpzT, n: *const MpzT, d: c_ulong);
        fn __gmpz_tdiv_q_2exp(q: *mut MpzT, n: *const MpzT, b: u64);
        fn __gmpz_tdiv_qr(q: *mut MpzT, r: *mut MpzT, n: *const MpzT, d: *const MpzT);
        fn __gmpz_tdiv_r(r: *mut MpzT, n: *const MpzT, d: *const MpzT);
        fn __gmpz_divexact(q: *mut MpzT, n: *const MpzT, d: *const MpzT);
        fn __gmpz_fdiv_r_2exp(r: *mut MpzT, n: *const MpzT, b: u64);
        fn __gmpz_fdiv_q_2exp(q: *mut MpzT, n: *const MpzT, b: u64);
        fn __gmpz_pow_ui(rop: *mut MpzT, base: *const MpzT, exp: c_ulong);
        fn __gmpz_and(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
        fn __gmpz_ior(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
        fn __gmpz_xor(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
        fn __gmpz_gcd(rop: *mut MpzT, op1: *const MpzT, op2: *const MpzT);
    }

    const LEAN_MPZ_TAG: u8 = 250;
    const LEAN_MAX_SMALL_NAT: usize = usize::MAX >> 1;
    const LEAN_MAX_SMALL_INT: i32 = i32::MAX;
    const LEAN_MIN_SMALL_INT: i32 = i32::MIN;

    #[inline]
    fn uninit_mpzt() -> MpzT {
        [MpzStruct {
            _mp_alloc: 0,
            _mp_size: 0,
            _mp_d: core::ptr::null_mut(),
        }]
    }

    #[inline]
    unsafe fn mpz_sgn(op: *const MpzT) -> c_int {
        let size = (*op)[0]._mp_size;
        if size < 0 {
            -1
        } else if size > 0 {
            1
        } else {
            0
        }
    }

    #[inline]
    unsafe fn lean_mpz_val(o: *mut LeanObject) -> *const MpzT {
        (o as *const u8).add(core::mem::size_of::<LeanObject>()) as *const MpzT
    }

    #[inline]
    unsafe fn lean_mpz_val_mut(o: *mut LeanObject) -> *mut MpzT {
        (o as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut MpzT
    }

    unsafe fn alloc_mpz(mpz: *const MpzT) -> *mut LeanObject {
        let sz = core::mem::size_of::<LeanMpzObject>();
        let obj = runtime_object_rc_impl::lean_alloc_small_object(sz);
        #[cfg(lean_has_mimalloc)]
        let saved_cs_size = (*obj).cs_size;
        let slot = lean_mpz_val_mut(obj);
        __gmpz_init_set(slot, mpz);
        (*obj).rc = 1;
        (*obj).tag = LEAN_MPZ_TAG;
        (*obj).other = 0;
        #[cfg(lean_has_mimalloc)]
        {
            (*obj).cs_size = saved_cs_size;
        }
        #[cfg(not(lean_has_mimalloc))]
        {
            (*obj).cs_size = 0;
        }
        obj
    }

    #[inline]
    unsafe fn mpz_is_size_t(m: *const MpzT) -> bool {
        mpz_sgn(m) >= 0 && __gmpz_size(m) <= 1
    }

    unsafe fn mpz_to_nat(m: *mut MpzT) -> *mut LeanObject {
        if mpz_is_size_t(m) {
            let v = __gmpz_getlimbn(m, 0) as usize;
            if v <= LEAN_MAX_SMALL_NAT {
                __gmpz_clear(m);
                return lean_box(v);
            }
        }
        let r = alloc_mpz(m);
        __gmpz_clear(m);
        r
    }

    unsafe fn mpz_to_nat_core(m: *mut MpzT) -> *mut LeanObject {
        let r = alloc_mpz(m);
        __gmpz_clear(m);
        r
    }

    unsafe fn mpz_to_int(m: *mut MpzT) -> *mut LeanObject {
        let cmp_max = __gmpz_cmp_si(m, LEAN_MAX_SMALL_INT as c_long);
        let cmp_min = __gmpz_cmp_si(m, LEAN_MIN_SMALL_INT as c_long);
        if cmp_min >= 0 && cmp_max <= 0 {
            let v = __gmpz_get_si(m) as i32 as u32 as usize;
            __gmpz_clear(m);
            return lean_box(v);
        }
        let r = alloc_mpz(m);
        __gmpz_clear(m);
        r
    }

    unsafe fn mpz_to_int_core(m: *mut MpzT) -> *mut LeanObject {
        let r = alloc_mpz(m);
        __gmpz_clear(m);
        r
    }

    #[inline]
    unsafe fn scalar_to_int(a: *mut LeanObject) -> i32 {
        lean_unbox(a) as u32 as i32
    }

    unsafe fn mpz_log2(m: *const MpzT) -> usize {
        if mpz_sgn(m) <= 0 {
            return 0;
        }
        let r = __gmpz_sizeinbase(m, 2);
        if r > 0 {
            r - 1
        } else {
            0
        }
    }

    fn mix_hash_u64(a: u64, b: u64) -> u64 {
        const M: u64 = 0xc6a4a7935bd1e995u64;
        const R: u32 = 47;
        let mut h: u64 = a ^ b.wrapping_mul(M);
        let mut k: u64 = b;
        k = k.wrapping_mul(M);
        k ^= k >> R;
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
        h ^= h >> R;
        h = h.wrapping_mul(M);
        h ^= h >> R;
        h
    }

    unsafe fn init_uint64(m: *mut MpzT, v: u64) {
        __gmpz_init_set_ui(m, v as u32 as c_ulong);
        let hi = (v >> 32) as u32;
        if hi != 0 {
            let mut tmp = uninit_mpzt();
            __gmpz_init_set_ui(&mut tmp, hi as c_ulong);
            __gmpz_mul_2exp(&mut tmp, &tmp, 32);
            __gmpz_add(m, m, &tmp);
            __gmpz_clear(&mut tmp);
        }
    }

    // ── Natural numbers ─────────────────────────────────────────────────────

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_alloc_mpz(v: *const MpzT) -> *mut LeanObject {
        alloc_mpz(v)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_extract_mpz_value(o: *mut LeanObject, v: *mut MpzT) {
        __gmpz_set(v, lean_mpz_val(o));
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_mpz_hash(o: *mut LeanObject) -> u32 {
        __gmpz_get_si(lean_mpz_val(o)) as i32 as u32
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_mpz_eq(o1: *mut LeanObject, o2: *mut LeanObject) -> u8 {
        (__gmpz_cmp(lean_mpz_val(o1), lean_mpz_val(o2)) == 0) as u8
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_alloc_mpz_from_mpz(o: *mut LeanObject) -> *mut LeanObject {
        alloc_mpz(lean_mpz_val(o))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_cstr_to_nat(n: *const c_char) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init_set_str(&mut m, n, 10);
        mpz_to_nat(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_big_usize_to_nat(n: usize) -> *mut LeanObject {
        if n <= LEAN_MAX_SMALL_NAT {
            return lean_box(n);
        }
        let mut m = uninit_mpzt();
        __gmpz_init_set_ui(&mut m, n as c_ulong);
        mpz_to_nat_core(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_big_uint64_to_nat(n: u64) -> *mut LeanObject {
        if n <= LEAN_MAX_SMALL_NAT as u64 {
            return lean_box(n as usize);
        }
        let mut m = uninit_mpzt();
        init_uint64(&mut m, n);
        mpz_to_nat_core(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_succ(a: *mut LeanObject) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init_set(&mut m, lean_mpz_val(a));
        __gmpz_add_ui(&mut m, &m, 1);
        mpz_to_nat_core(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_add(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        if lean_is_scalar(a1) {
            __gmpz_add_ui(&mut m, lean_mpz_val(a2), lean_unbox(a1) as c_ulong);
        } else if lean_is_scalar(a2) {
            __gmpz_add_ui(&mut m, lean_mpz_val(a1), lean_unbox(a2) as c_ulong);
        } else {
            __gmpz_add(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        }
        mpz_to_nat_core(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_sub(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) {
            return lean_box(0);
        } else if lean_is_scalar(a2) {
            let mut m = uninit_mpzt();
            __gmpz_init_set(&mut m, lean_mpz_val(a1));
            __gmpz_sub_ui(&mut m, &m, lean_unbox(a2) as c_ulong);
            return mpz_to_nat(&mut m);
        } else {
            if __gmpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) < 0 {
                return lean_box(0);
            }
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_sub(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
            return mpz_to_nat(&mut m);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_mul(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        if lean_is_scalar(a1) {
            __gmpz_mul_ui(&mut m, lean_mpz_val(a2), lean_unbox(a1) as c_ulong);
        } else if lean_is_scalar(a2) {
            __gmpz_mul_ui(&mut m, lean_mpz_val(a1), lean_unbox(a2) as c_ulong);
        } else {
            __gmpz_mul(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        }
        mpz_to_nat(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_overflow_mul(a1: usize, a2: usize) -> *mut LeanObject {
        let mut m1 = uninit_mpzt();
        __gmpz_init_set_ui(&mut m1, a1 as c_ulong);
        let mut m2 = uninit_mpzt();
        __gmpz_init_set_ui(&mut m2, a2 as c_ulong);
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        __gmpz_mul(&mut m, &m1, &m2);
        __gmpz_clear(&mut m1);
        __gmpz_clear(&mut m2);
        mpz_to_nat(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_div(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) {
            return lean_box(0);
        } else if lean_is_scalar(a2) {
            let n2 = lean_unbox(a2);
            if n2 == 0 {
                return a2;
            }
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_tdiv_q_ui(&mut m, lean_mpz_val(a1), n2 as c_ulong);
            return mpz_to_nat(&mut m);
        } else {
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_tdiv_q(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
            return mpz_to_nat(&mut m);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_div_exact(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) {
            return lean_box(0);
        } else if lean_is_scalar(a2) {
            let mut d = uninit_mpzt();
            __gmpz_init_set_ui(&mut d, lean_unbox(a2) as c_ulong);
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_divexact(&mut m, lean_mpz_val(a1), &d);
            __gmpz_clear(&mut d);
            return mpz_to_nat(&mut m);
        } else {
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_divexact(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
            return mpz_to_nat(&mut m);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_mod(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) {
            return a1;
        } else if lean_is_scalar(a2) {
            let n2 = lean_unbox(a2);
            if n2 == 0 {
                lean_inc(a1);
                return a1;
            }
            let mut d = uninit_mpzt();
            __gmpz_init_set_ui(&mut d, n2 as c_ulong);
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_tdiv_r(&mut m, lean_mpz_val(a1), &d);
            __gmpz_clear(&mut d);
            return mpz_to_nat(&mut m);
        } else {
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_tdiv_r(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
            return mpz_to_nat(&mut m);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
        if lean_is_scalar(a1) || lean_is_scalar(a2) {
            return false;
        }
        __gmpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) == 0
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_le(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
        if lean_is_scalar(a1) {
            return true;
        } else if lean_is_scalar(a2) {
            return false;
        }
        __gmpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) <= 0
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_lt(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
        if lean_is_scalar(a1) {
            return true;
        } else if lean_is_scalar(a2) {
            return false;
        }
        __gmpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) < 0
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_land(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        if lean_is_scalar(a1) {
            let mut s = uninit_mpzt();
            __gmpz_init_set_ui(&mut s, lean_unbox(a1) as c_ulong);
            __gmpz_and(&mut m, &s, lean_mpz_val(a2));
            __gmpz_clear(&mut s);
        } else if lean_is_scalar(a2) {
            let mut s = uninit_mpzt();
            __gmpz_init_set_ui(&mut s, lean_unbox(a2) as c_ulong);
            __gmpz_and(&mut m, lean_mpz_val(a1), &s);
            __gmpz_clear(&mut s);
        } else {
            __gmpz_and(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        }
        mpz_to_nat(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_lor(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        if lean_is_scalar(a1) {
            let mut s = uninit_mpzt();
            __gmpz_init_set_ui(&mut s, lean_unbox(a1) as c_ulong);
            __gmpz_ior(&mut m, &s, lean_mpz_val(a2));
            __gmpz_clear(&mut s);
        } else if lean_is_scalar(a2) {
            let mut s = uninit_mpzt();
            __gmpz_init_set_ui(&mut s, lean_unbox(a2) as c_ulong);
            __gmpz_ior(&mut m, lean_mpz_val(a1), &s);
            __gmpz_clear(&mut s);
        } else {
            __gmpz_ior(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        }
        mpz_to_nat(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_xor(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        if lean_is_scalar(a1) {
            let mut s = uninit_mpzt();
            __gmpz_init_set_ui(&mut s, lean_unbox(a1) as c_ulong);
            __gmpz_xor(&mut m, &s, lean_mpz_val(a2));
            __gmpz_clear(&mut s);
        } else if lean_is_scalar(a2) {
            let mut s = uninit_mpzt();
            __gmpz_init_set_ui(&mut s, lean_unbox(a2) as c_ulong);
            __gmpz_xor(&mut m, lean_mpz_val(a1), &s);
            __gmpz_clear(&mut s);
        } else {
            __gmpz_xor(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        }
        mpz_to_nat(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_shiftl(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) && lean_unbox(a1) == 0 {
            return lean_box(0);
        }
        if !lean_is_scalar(a2) || lean_unbox(a2) > u32::MAX as usize {
            lean_internal_panic(b"Nat.shiftl exponent is too big\0".as_ptr() as *const c_char);
        }
        let k = lean_unbox(a2) as u64;
        let mut m = uninit_mpzt();
        if lean_is_scalar(a1) {
            __gmpz_init_set_ui(&mut m, lean_unbox(a1) as c_ulong);
        } else {
            __gmpz_init_set(&mut m, lean_mpz_val(a1));
        }
        __gmpz_mul_2exp(&mut m, &m, k);
        mpz_to_nat(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_big_shiftr(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(a2) {
            return lean_box(0);
        }
        let s = lean_unbox(a2);
        let mut m = uninit_mpzt();
        if lean_is_scalar(a1) {
            __gmpz_init_set_ui(&mut m, lean_unbox(a1) as c_ulong);
        } else {
            __gmpz_init_set(&mut m, lean_mpz_val(a1));
        }
        if s > u32::MAX as usize {
            if mpz_log2(&m) >= s {
                __gmpz_clear(&mut m);
                lean_internal_panic(b"Nat.shiftr exponent is too big\0".as_ptr() as *const c_char);
            }
            __gmpz_clear(&mut m);
            return lean_box(0);
        }
        __gmpz_tdiv_q_2exp(&mut m, &m, s as u64);
        mpz_to_nat(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_pow(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(a2) || lean_unbox(a2) > u32::MAX as usize {
            lean_internal_panic(b"Nat.pow exponent is too big\0".as_ptr() as *const c_char);
        }
        let exp = lean_unbox(a2) as c_ulong;
        let mut base = uninit_mpzt();
        if lean_is_scalar(a1) {
            __gmpz_init_set_ui(&mut base, lean_unbox(a1) as c_ulong);
        } else {
            __gmpz_init_set(&mut base, lean_mpz_val(a1));
        }
        let mut result = uninit_mpzt();
        __gmpz_init(&mut result);
        __gmpz_pow_ui(&mut result, &base, exp);
        __gmpz_clear(&mut base);
        mpz_to_nat(&mut result)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_gcd(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut m1 = uninit_mpzt();
        let mut m2 = uninit_mpzt();
        if lean_is_scalar(a1) {
            __gmpz_init_set_ui(&mut m1, lean_unbox(a1) as c_ulong);
        } else {
            __gmpz_init_set(&mut m1, lean_mpz_val(a1));
        }
        if lean_is_scalar(a2) {
            __gmpz_init_set_ui(&mut m2, lean_unbox(a2) as c_ulong);
        } else {
            __gmpz_init_set(&mut m2, lean_mpz_val(a2));
        }
        let mut g = uninit_mpzt();
        __gmpz_init(&mut g);
        __gmpz_gcd(&mut g, &m1, &m2);
        __gmpz_clear(&mut m1);
        __gmpz_clear(&mut m2);
        mpz_to_nat(&mut g)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_nat_log2(a: *mut LeanObject) -> *mut LeanObject {
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

    // ── Integers ────────────────────────────────────────────────────────────

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_big_int_to_nat(a: *mut LeanObject) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init_set(&mut m, lean_mpz_val(a));
        lean_dec(a);
        mpz_to_nat(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_cstr_to_int(n: *const c_char) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init_set_str(&mut m, n, 10);
        mpz_to_int(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_big_int_to_int(n: c_int) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init_set_si(&mut m, n as c_long);
        mpz_to_int_core(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_big_size_t_to_int(n: usize) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init_set_ui(&mut m, n as c_ulong);
        mpz_to_int_core(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_big_int64_to_int(n: i64) -> *mut LeanObject {
        if n >= LEAN_MIN_SMALL_INT as i64 && n <= LEAN_MAX_SMALL_INT as i64 {
            return lean_box(n as i32 as u32 as usize);
        }
        let mut m = uninit_mpzt();
        let w: u64 = if n < 0 {
            (-(n as i128)) as u64
        } else {
            n as u64
        };
        init_uint64(&mut m, w);
        if n < 0 {
            __gmpz_neg(&mut m, &m);
        }
        mpz_to_int_core(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_neg(a: *mut LeanObject) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        __gmpz_neg(&mut m, lean_mpz_val(a));
        mpz_to_int(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_add(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        if lean_is_scalar(a1) {
            let i1 = scalar_to_int(a1);
            if i1 >= 0 {
                __gmpz_add_ui(&mut m, lean_mpz_val(a2), i1 as c_ulong);
            } else {
                __gmpz_sub_ui(&mut m, lean_mpz_val(a2), (-(i1 as i64)) as c_ulong);
            }
        } else if lean_is_scalar(a2) {
            let i2 = scalar_to_int(a2);
            if i2 >= 0 {
                __gmpz_add_ui(&mut m, lean_mpz_val(a1), i2 as c_ulong);
            } else {
                __gmpz_sub_ui(&mut m, lean_mpz_val(a1), (-(i2 as i64)) as c_ulong);
            }
        } else {
            __gmpz_add(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        }
        mpz_to_int(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_sub(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        if lean_is_scalar(a1) {
            let mut n = uninit_mpzt();
            __gmpz_init_set_si(&mut n, scalar_to_int(a1) as c_long);
            __gmpz_sub(&mut m, &n, lean_mpz_val(a2));
            __gmpz_clear(&mut n);
        } else if lean_is_scalar(a2) {
            let i2 = scalar_to_int(a2);
            if i2 >= 0 {
                __gmpz_sub_ui(&mut m, lean_mpz_val(a1), i2 as c_ulong);
            } else {
                __gmpz_add_ui(&mut m, lean_mpz_val(a1), (-(i2 as i64)) as c_ulong);
            }
        } else {
            __gmpz_sub(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        }
        mpz_to_int(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_mul(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut m = uninit_mpzt();
        __gmpz_init(&mut m);
        if lean_is_scalar(a1) {
            __gmpz_mul_si(&mut m, lean_mpz_val(a2), scalar_to_int(a1) as c_long);
        } else if lean_is_scalar(a2) {
            __gmpz_mul_si(&mut m, lean_mpz_val(a1), scalar_to_int(a2) as c_long);
        } else {
            __gmpz_mul(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
        }
        mpz_to_int(&mut m)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_div(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) {
            let mut n = uninit_mpzt();
            __gmpz_init_set_si(&mut n, scalar_to_int(a1) as c_long);
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_tdiv_q(&mut m, &n, lean_mpz_val(a2));
            __gmpz_clear(&mut n);
            return mpz_to_int(&mut m);
        } else if lean_is_scalar(a2) {
            let d = scalar_to_int(a2);
            if d == 0 {
                return a2;
            }
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            if d > 0 {
                __gmpz_tdiv_q_ui(&mut m, lean_mpz_val(a1), d as c_ulong);
            } else {
                let mut dn = uninit_mpzt();
                __gmpz_init_set_si(&mut dn, d as c_long);
                __gmpz_tdiv_q(&mut m, lean_mpz_val(a1), &dn);
                __gmpz_clear(&mut dn);
            }
            return mpz_to_int(&mut m);
        } else {
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_tdiv_q(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
            return mpz_to_int(&mut m);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_div_exact(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) {
            let n = scalar_to_int(a1);
            if n == 0 {
                return a1;
            }
            return lean_box((-1i32) as u32 as usize);
        } else if lean_is_scalar(a2) {
            let mut dn = uninit_mpzt();
            __gmpz_init_set_si(&mut dn, scalar_to_int(a2) as c_long);
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_divexact(&mut m, lean_mpz_val(a1), &dn);
            __gmpz_clear(&mut dn);
            return mpz_to_int(&mut m);
        } else {
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_divexact(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
            return mpz_to_int(&mut m);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_mod(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) {
            let mut n = uninit_mpzt();
            __gmpz_init_set_si(&mut n, scalar_to_int(a1) as c_long);
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_tdiv_r(&mut m, &n, lean_mpz_val(a2));
            __gmpz_clear(&mut n);
            return mpz_to_int(&mut m);
        } else if lean_is_scalar(a2) {
            let i2 = scalar_to_int(a2);
            if i2 == 0 {
                lean_inc(a1);
                return a1;
            }
            let mut d = uninit_mpzt();
            __gmpz_init_set_si(&mut d, i2 as c_long);
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_tdiv_r(&mut m, lean_mpz_val(a1), &d);
            __gmpz_clear(&mut d);
            return mpz_to_int(&mut m);
        } else {
            let mut m = uninit_mpzt();
            __gmpz_init(&mut m);
            __gmpz_tdiv_r(&mut m, lean_mpz_val(a1), lean_mpz_val(a2));
            return mpz_to_int(&mut m);
        }
    }

    unsafe fn ediv_impl(n: *const MpzT, d: *const MpzT) -> MpzT {
        let mut result = uninit_mpzt();
        __gmpz_init(&mut result);
        let mut r = uninit_mpzt();
        __gmpz_init(&mut r);
        __gmpz_tdiv_qr(&mut result, &mut r, n, d);
        if mpz_sgn(&r) < 0 {
            if mpz_sgn(d) > 0 {
                __gmpz_sub_ui(&mut result, &result, 1);
            } else {
                __gmpz_add_ui(&mut result, &result, 1);
            }
        }
        __gmpz_clear(&mut r);
        result
    }

    unsafe fn emod_impl(n: *const MpzT, d: *const MpzT) -> MpzT {
        let mut result = uninit_mpzt();
        __gmpz_init(&mut result);
        __gmpz_tdiv_r(&mut result, n, d);
        if mpz_sgn(&result) < 0 {
            if mpz_sgn(d) > 0 {
                __gmpz_add(&mut result, &result, d);
            } else {
                __gmpz_sub(&mut result, &result, d);
            }
        }
        result
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_ediv(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) {
            let mut n = uninit_mpzt();
            __gmpz_init_set_si(&mut n, scalar_to_int(a1) as c_long);
            let mut m = ediv_impl(&n, lean_mpz_val(a2));
            __gmpz_clear(&mut n);
            return mpz_to_int(&mut m);
        } else if lean_is_scalar(a2) {
            let d = scalar_to_int(a2);
            if d == 0 {
                return a2;
            }
            let mut dn = uninit_mpzt();
            __gmpz_init_set_si(&mut dn, d as c_long);
            let mut m = ediv_impl(lean_mpz_val(a1), &dn);
            __gmpz_clear(&mut dn);
            return mpz_to_int(&mut m);
        } else {
            let mut m = ediv_impl(lean_mpz_val(a1), lean_mpz_val(a2));
            return mpz_to_int(&mut m);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_emod(
        a1: *mut LeanObject,
        a2: *mut LeanObject,
    ) -> *mut LeanObject {
        if lean_is_scalar(a1) {
            let mut n = uninit_mpzt();
            __gmpz_init_set_si(&mut n, scalar_to_int(a1) as c_long);
            let mut m = emod_impl(&n, lean_mpz_val(a2));
            __gmpz_clear(&mut n);
            return mpz_to_int(&mut m);
        } else if lean_is_scalar(a2) {
            let i2 = scalar_to_int(a2);
            if i2 == 0 {
                lean_inc(a1);
                return a1;
            }
            let mut dn = uninit_mpzt();
            __gmpz_init_set_si(&mut dn, i2 as c_long);
            let mut m = emod_impl(lean_mpz_val(a1), &dn);
            __gmpz_clear(&mut dn);
            return mpz_to_int(&mut m);
        } else {
            let mut m = emod_impl(lean_mpz_val(a1), lean_mpz_val(a2));
            return mpz_to_int(&mut m);
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
        if lean_is_scalar(a1) || lean_is_scalar(a2) {
            return false;
        }
        __gmpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) == 0
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_le(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
        if lean_is_scalar(a1) {
            __gmpz_cmp_si(lean_mpz_val(a2), scalar_to_int(a1) as c_long) >= 0
        } else if lean_is_scalar(a2) {
            __gmpz_cmp_si(lean_mpz_val(a1), scalar_to_int(a2) as c_long) <= 0
        } else {
            __gmpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) <= 0
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_lt(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
        if lean_is_scalar(a1) {
            __gmpz_cmp_si(lean_mpz_val(a2), scalar_to_int(a1) as c_long) > 0
        } else if lean_is_scalar(a2) {
            __gmpz_cmp_si(lean_mpz_val(a1), scalar_to_int(a2) as c_long) < 0
        } else {
            __gmpz_cmp(lean_mpz_val(a1), lean_mpz_val(a2)) < 0
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int_big_nonneg(a: *mut LeanObject) -> bool {
        mpz_sgn(lean_mpz_val(a)) >= 0
    }

    // ── UInt ────────────────────────────────────────────────────────────────

    unsafe fn fdiv_r_2exp_ui(m: *const MpzT, bits: u64) -> u64 {
        let mut tmp = uninit_mpzt();
        __gmpz_init(&mut tmp);
        __gmpz_fdiv_r_2exp(&mut tmp, m, bits);
        let v = __gmpz_get_ui(&tmp) as u64;
        __gmpz_clear(&mut tmp);
        v
    }

    unsafe fn fdiv_q_2exp_ui(m: *const MpzT, bits: u64) -> u64 {
        let mut tmp = uninit_mpzt();
        __gmpz_init(&mut tmp);
        __gmpz_fdiv_q_2exp(&mut tmp, m, bits);
        let v = __gmpz_get_ui(&tmp) as u64;
        __gmpz_clear(&mut tmp);
        v
    }

    unsafe fn mod64(m: *const MpzT) -> u64 {
        let mut r = uninit_mpzt();
        __gmpz_init(&mut r);
        __gmpz_fdiv_r_2exp(&mut r, m, 64);
        let lo = fdiv_r_2exp_ui(&r, 32);
        let hi = fdiv_q_2exp_ui(&r, 32);
        __gmpz_clear(&mut r);
        lo | (hi << 32)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uint8_of_big_nat(a: *mut LeanObject) -> u8 {
        fdiv_r_2exp_ui(lean_mpz_val(a), 8) as u8
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uint16_of_big_nat(a: *mut LeanObject) -> u16 {
        fdiv_r_2exp_ui(lean_mpz_val(a), 16) as u16
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uint32_of_big_nat(a: *mut LeanObject) -> u32 {
        fdiv_r_2exp_ui(lean_mpz_val(a), 32) as u32
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uint64_of_big_nat(a: *mut LeanObject) -> u64 {
        mod64(lean_mpz_val(a))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uint64_mix_hash(a1: u64, a2: u64) -> u64 {
        mix_hash_u64(a1, a2)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_usize_of_big_nat(a: *mut LeanObject) -> usize {
        __gmpz_getlimbn(lean_mpz_val(a), 0) as usize
    }

    // ── IntX ────────────────────────────────────────────────────────────────

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int8_of_big_int(a: *mut LeanObject) -> i8 {
        fdiv_r_2exp_ui(lean_mpz_val(a), 8) as u8 as i8
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int16_of_big_int(a: *mut LeanObject) -> i16 {
        fdiv_r_2exp_ui(lean_mpz_val(a), 16) as u16 as i16
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int32_of_big_int(a: *mut LeanObject) -> i32 {
        fdiv_r_2exp_ui(lean_mpz_val(a), 32) as u32 as i32
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_int64_of_big_int(a: *mut LeanObject) -> i64 {
        mod64(lean_mpz_val(a)) as i64
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_isize_of_big_int(a: *mut LeanObject) -> isize {
        if core::mem::size_of::<isize>() == 8 {
            mod64(lean_mpz_val(a)) as i64 as isize
        } else {
            fdiv_r_2exp_ui(lean_mpz_val(a), 32) as u32 as i32 as isize
        }
    }
}
