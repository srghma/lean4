
// Port of src/runtime/mpz.cpp (GMP path only)
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
//
// The lean::mpz class is embedded by value in lean_mpz_object (lean.h).
// Its memory layout must match exactly.
//
// In GMP mode: layout is [mpz_t m_val] = [__mpz_struct; 1]
//
// All functions are exported with C++ mangled names so existing C++ callers
// link without modification.  The C++ shim mpz_helpers.cpp provides
// to_string() and operator<< which need std::string/ostream ABI.

#[cfg(not(lean_use_gmp))]
compile_error!("runtime_mpz.rs requires lean_use_gmp cfg flag (build with USE_GMP=ON)");

#[cfg(lean_use_gmp)]
mod gmp_impl {
    use core::ffi::{c_int, c_long, c_ulong};

    // GMP's __mpz_struct — must match gmp.h exactly on the target platform.
    // On LP64 (Linux/macOS 64-bit): mp_limb_t is u64.
    #[repr(C)]
    pub struct MpzStruct {
        pub _mp_alloc: c_int,
        pub _mp_size: c_int,
        pub _mp_d: *mut u64,
    }

    // mpz_t = [__mpz_struct; 1]
    pub type MpzT = [MpzStruct; 1];

    extern "C" {
        fn __gmpz_init(x: *mut MpzT);
        fn __gmpz_init_set(rop: *mut MpzT, op: *const MpzT);
        fn __gmpz_init_set_str(rop: *mut MpzT, s: *const core::ffi::c_char, base: c_int) -> c_int;
        fn __gmpz_init_set_ui(rop: *mut MpzT, op: c_ulong);
        fn __gmpz_init_set_si(rop: *mut MpzT, op: c_long);
        fn __gmpz_clear(x: *mut MpzT);
        fn __gmpz_set(rop: *mut MpzT, op: *const MpzT);
        fn __gmpz_swap(rop1: *mut MpzT, rop2: *mut MpzT);
        fn __gmpz_fits_sint_p(op: *const MpzT) -> c_int;
        fn __gmpz_fits_uint_p(op: *const MpzT) -> c_int;
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

    // mpz_sgn is a GMP macro; implement it directly from the struct fields.
    #[inline]
    unsafe fn mpz_sgn_impl(op: *const MpzT) -> c_int {
        let size = (*op)[0]._mp_size;
        if size < 0 {
            -1
        } else if size > 0 {
            1
        } else {
            0
        }
    }

    // Zero-initialised MpzT suitable for stack allocation before __gmpz_init.
    #[inline]
    fn uninit_mpzt() -> MpzT {
        [MpzStruct {
            _mp_alloc: 0,
            _mp_size: 0,
            _mp_d: core::ptr::null_mut(),
        }]
    }

    // lean::mpz::mpz()
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzC1Ev")]
    pub unsafe extern "C" fn mpz_ctor_default(self_: *mut MpzT) {
        __gmpz_init(self_);
    }

    // lean::mpz::mpz(char const*)
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzC1EPKc")]
    pub unsafe extern "C" fn mpz_ctor_str(self_: *mut MpzT, s: *const core::ffi::c_char) {
        __gmpz_init_set_str(self_, s, 10);
    }

    // lean::mpz::mpz(unsigned int)
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzC1Ej")]
    pub unsafe extern "C" fn mpz_ctor_uint(self_: *mut MpzT, v: u32) {
        __gmpz_init_set_ui(self_, v as c_ulong);
    }

    // lean::mpz::mpz(int)
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzC1Ei")]
    pub unsafe extern "C" fn mpz_ctor_int(self_: *mut MpzT, v: i32) {
        __gmpz_init_set_si(self_, v as c_long);
    }

    // lean::mpz::mpz(uint64)  — uint64 = unsigned long on Linux x64 → mangled 'm'
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzC1Em")]
    pub unsafe extern "C" fn mpz_ctor_uint64(self_: *mut MpzT, v: u64) {
        // Lower 32 bits, then add upper 32 shifted left (portable across 32/64-bit GMP).
        __gmpz_init_set_ui(self_, (v as u32) as c_ulong);
        let hi = (v >> 32) as u32;
        if hi != 0 {
            let mut tmp = uninit_mpzt();
            __gmpz_init_set_ui(&mut tmp, hi as c_ulong);
            __gmpz_mul_2exp(&mut tmp, &tmp, 32);
            __gmpz_add(self_, self_, &tmp);
            __gmpz_clear(&mut tmp);
        }
    }

    // lean::mpz::mpz(int64) — int64 = long on Linux x64 → mangled 'l'
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzC1El")]
    pub unsafe extern "C" fn mpz_ctor_int64(self_: *mut MpzT, v: i64) {
        let w: u64 = if v < 0 {
            (-(v as i128)) as u64
        } else {
            v as u64
        };
        mpz_ctor_uint64(self_, w);
        if v < 0 {
            __gmpz_neg(self_, self_);
        }
    }

    // lean::mpz::mpz(mpz const&)
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzC1ERKS0_")]
    pub unsafe extern "C" fn mpz_ctor_copy(self_: *mut MpzT, other: *const MpzT) {
        __gmpz_init_set(self_, other);
    }

    // lean::mpz::mpz(mpz&&)  — move constructor: init to 0, swap
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzC1EOS0_")]
    pub unsafe extern "C" fn mpz_ctor_move(self_: *mut MpzT, other: *mut MpzT) {
        __gmpz_init(self_);
        __gmpz_swap(self_, other);
    }

    // lean::mpz::mpz(__mpz_struct const*)  — construct from raw mpz_t pointer
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean3mpzC1EP12__mpz_struct"
    )]
    pub unsafe extern "C" fn mpz_ctor_mpzt(self_: *mut MpzT, v: *const MpzT) {
        __gmpz_init_set(self_, v);
    }

    // lean::mpz::~mpz()
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzD1Ev")]
    pub unsafe extern "C" fn mpz_dtor(self_: *mut MpzT) {
        __gmpz_clear(self_);
    }

    // lean::mpz::set(mpz_t r) const  — copies self's value into raw mpz_t r
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZNK4lean3mpz3setEP12__mpz_struct"
    )]
    pub unsafe extern "C" fn mpz_set_raw(self_: *const MpzT, r: *mut MpzT) {
        __gmpz_set(r, self_);
    }

    // lean::swap(mpz&, mpz&)
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean4swapERNS_3mpzES1_"
    )]
    pub unsafe extern "C" fn mpz_swap(a: *mut MpzT, b: *mut MpzT) {
        __gmpz_swap(a, b);
    }

    // lean::mpz::sgn() const
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz3sgnEv")]
    pub unsafe extern "C" fn mpz_sgn_export(self_: *const MpzT) -> c_int {
        mpz_sgn_impl(self_)
    }

    // lean::mpz::is_int() const
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz6is_intEv")]
    pub unsafe extern "C" fn mpz_is_int(self_: *const MpzT) -> bool {
        __gmpz_fits_sint_p(self_) != 0
    }

    // lean::mpz::is_unsigned_int() const
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZNK4lean3mpz15is_unsigned_intEv"
    )]
    pub unsafe extern "C" fn mpz_is_unsigned_int(self_: *const MpzT) -> bool {
        __gmpz_fits_uint_p(self_) != 0
    }

    // lean::mpz::is_size_t() const
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZNK4lean3mpz9is_size_tEv"
    )]
    pub unsafe extern "C" fn mpz_is_size_t(self_: *const MpzT) -> bool {
        // sizeof(size_t) == sizeof(mp_limb_t) on LP64; nonneg AND at most one limb
        mpz_sgn_impl(self_) >= 0 && __gmpz_size(self_) <= 1
    }

    // lean::mpz::get_int() const
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZNK4lean3mpz7get_intEv"
    )]
    pub unsafe extern "C" fn mpz_get_int(self_: *const MpzT) -> i32 {
        __gmpz_get_si(self_) as i32
    }

    // lean::mpz::get_unsigned_int() const
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZNK4lean3mpz16get_unsigned_intEv"
    )]
    pub unsafe extern "C" fn mpz_get_unsigned_int(self_: *const MpzT) -> u32 {
        __gmpz_get_ui(self_) as u32
    }

    // lean::mpz::get_size_t() const
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZNK4lean3mpz10get_size_tEv"
    )]
    pub unsafe extern "C" fn mpz_get_size_t(self_: *const MpzT) -> usize {
        __gmpz_getlimbn(self_, 0) as usize
    }

    // lean::cmp(mpz const&, mpz const&)
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean3cmpERKNS_3mpzES2_"
    )]
    pub unsafe extern "C" fn mpz_cmp(a: *const MpzT, b: *const MpzT) -> c_int {
        __gmpz_cmp(a, b)
    }

    // lean::cmp(mpz const&, unsigned)
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean3cmpERKNS_3mpzEj"
    )]
    pub unsafe extern "C" fn mpz_cmp_uint(a: *const MpzT, b: u32) -> c_int {
        __gmpz_cmp_ui(a, b as c_ulong)
    }

    // lean::cmp(mpz const&, int)
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean3cmpERKNS_3mpzEi"
    )]
    pub unsafe extern "C" fn mpz_cmp_int(a: *const MpzT, b: i32) -> c_int {
        __gmpz_cmp_si(a, b as c_long)
    }

    // In-place binary operators: self op= other; return self
    macro_rules! binop {
        ($export:literal, $fn_name:ident, $gmp_fn:ident) => {
            #[cfg_attr(feature = "export-runtime-ffi", export_name = $export)]
            pub unsafe extern "C" fn $fn_name(self_: *mut MpzT, other: *const MpzT) -> *mut MpzT {
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
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzpLEj")]
    pub unsafe extern "C" fn mpz_add_uint(self_: *mut MpzT, u: u32) -> *mut MpzT {
        __gmpz_add_ui(self_, self_, u as c_ulong);
        self_
    }
    // -= unsigned
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzmIEj")]
    pub unsafe extern "C" fn mpz_sub_uint(self_: *mut MpzT, u: u32) -> *mut MpzT {
        __gmpz_sub_ui(self_, self_, u as c_ulong);
        self_
    }
    // *= unsigned
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzmLEj")]
    pub unsafe extern "C" fn mpz_mul_uint(self_: *mut MpzT, u: u32) -> *mut MpzT {
        __gmpz_mul_ui(self_, self_, u as c_ulong);
        self_
    }
    // /= unsigned
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzdVEj")]
    pub unsafe extern "C" fn mpz_div_uint(self_: *mut MpzT, u: u32) -> *mut MpzT {
        __gmpz_tdiv_q_ui(self_, self_, u as c_ulong);
        self_
    }
    // += int
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzpLEi")]
    pub unsafe extern "C" fn mpz_add_int(self_: *mut MpzT, u: i32) -> *mut MpzT {
        if u >= 0 {
            __gmpz_add_ui(self_, self_, u as c_ulong);
        } else {
            __gmpz_sub_ui(self_, self_, (-(u as i64)) as c_ulong);
        }
        self_
    }
    // -= int
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzmIEi")]
    pub unsafe extern "C" fn mpz_sub_int(self_: *mut MpzT, u: i32) -> *mut MpzT {
        if u >= 0 {
            __gmpz_sub_ui(self_, self_, u as c_ulong);
        } else {
            __gmpz_add_ui(self_, self_, (-(u as i64)) as c_ulong);
        }
        self_
    }
    // *= int
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean3mpzmLEi")]
    pub unsafe extern "C" fn mpz_mul_int(self_: *mut MpzT, u: i32) -> *mut MpzT {
        __gmpz_mul_si(self_, self_, u as c_long);
        self_
    }

    // lean::mpz::pow(unsigned) const — returns mpz via hidden first-arg (SRET)
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz3powEj")]
    pub unsafe extern "C" fn mpz_pow(result: *mut MpzT, self_: *const MpzT, exp: u32) {
        __gmpz_init(result);
        __gmpz_pow_ui(result, self_, exp as c_ulong);
    }

    // lean::mpz::log2() const
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz4log2Ev")]
    pub unsafe extern "C" fn mpz_log2(self_: *const MpzT) -> usize {
        if mpz_sgn_impl(self_) <= 0 {
            return 0;
        }
        let r = __gmpz_sizeinbase(self_, 2);
        if r > 0 {
            r - 1
        } else {
            0
        }
    }

    // lean::mul2k(mpz&, mpz const&, unsigned)
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean5mul2kERNS_3mpzERKS0_j"
    )]
    pub unsafe extern "C" fn mul2k(a: *mut MpzT, b: *const MpzT, k: u32) {
        __gmpz_mul_2exp(a, b, k as u64);
    }

    // lean::div2k(mpz&, mpz const&, unsigned)
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean5div2kERNS_3mpzERKS0_j"
    )]
    pub unsafe extern "C" fn div2k(a: *mut MpzT, b: *const MpzT, k: u32) {
        __gmpz_tdiv_q_2exp(a, b, k as u64);
    }

    // Helpers for mod/smod: floor division remainder for 2^bits (returns low 32 bits)
    unsafe fn fdiv_r_2exp_ui(self_: *const MpzT, bits: u64) -> u64 {
        let mut tmp = uninit_mpzt();
        __gmpz_init(&mut tmp);
        __gmpz_fdiv_r_2exp(&mut tmp, self_, bits);
        let v = __gmpz_get_ui(&tmp) as u64;
        __gmpz_clear(&mut tmp);
        v
    }
    unsafe fn fdiv_q_2exp_ui(self_: *const MpzT, bits: u64) -> u64 {
        let mut tmp = uninit_mpzt();
        __gmpz_init(&mut tmp);
        __gmpz_fdiv_q_2exp(&mut tmp, self_, bits);
        let v = __gmpz_get_ui(&tmp) as u64;
        __gmpz_clear(&mut tmp);
        v
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz4mod8Ev")]
    pub unsafe extern "C" fn mpz_mod8(self_: *const MpzT) -> u8 {
        fdiv_r_2exp_ui(self_, 8) as u8
    }
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz5mod16Ev")]
    pub unsafe extern "C" fn mpz_mod16(self_: *const MpzT) -> u16 {
        fdiv_r_2exp_ui(self_, 16) as u16
    }
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz5mod32Ev")]
    pub unsafe extern "C" fn mpz_mod32(self_: *const MpzT) -> u32 {
        fdiv_r_2exp_ui(self_, 32) as u32
    }
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz5mod64Ev")]
    pub unsafe extern "C" fn mpz_mod64(self_: *const MpzT) -> u64 {
        let mut r = uninit_mpzt();
        __gmpz_init(&mut r);
        __gmpz_fdiv_r_2exp(&mut r, self_, 64);
        let lo = fdiv_r_2exp_ui(&r, 32);
        let hi = fdiv_q_2exp_ui(&r, 32);
        __gmpz_clear(&mut r);
        lo | (hi << 32)
    }
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz5smod8Ev")]
    pub unsafe extern "C" fn mpz_smod8(self_: *const MpzT) -> i8 {
        mpz_mod8(self_) as i8
    }
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz6smod16Ev")]
    pub unsafe extern "C" fn mpz_smod16(self_: *const MpzT) -> i16 {
        mpz_mod16(self_) as i16
    }
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz6smod32Ev")]
    pub unsafe extern "C" fn mpz_smod32(self_: *const MpzT) -> i32 {
        mpz_mod32(self_) as i32
    }
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean3mpz6smod64Ev")]
    pub unsafe extern "C" fn mpz_smod64(self_: *const MpzT) -> i64 {
        mpz_mod64(self_) as i64
    }

    // lean::mpz::ediv(mpz const&, mpz const&) static — SRET result
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean3mpz4edivERKS0_S2_"
    )]
    pub unsafe extern "C" fn mpz_ediv(result: *mut MpzT, n: *const MpzT, d: *const MpzT) {
        __gmpz_init(result);
        let mut r = uninit_mpzt();
        __gmpz_init(&mut r);
        __gmpz_tdiv_qr(result, &mut r, n, d);
        if mpz_sgn_impl(&r) < 0 {
            if mpz_sgn_impl(d) > 0 {
                __gmpz_sub_ui(result, result, 1);
            } else {
                __gmpz_add_ui(result, result, 1);
            }
        }
        __gmpz_clear(&mut r);
    }

    // lean::mpz::emod(mpz const&, mpz const&) static — SRET result
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean3mpz4emodERKS0_S2_"
    )]
    pub unsafe extern "C" fn mpz_emod(result: *mut MpzT, n: *const MpzT, d: *const MpzT) {
        __gmpz_init(result);
        __gmpz_tdiv_r(result, n, d);
        if mpz_sgn_impl(result) < 0 {
            if mpz_sgn_impl(d) > 0 {
                __gmpz_add(result, result, d);
            } else {
                __gmpz_sub(result, result, d);
            }
        }
    }

    // lean::mpz::divexact(mpz const&, mpz const&) static — SRET result
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean3mpz8divexactERKS0_S2_"
    )]
    pub unsafe extern "C" fn mpz_divexact(result: *mut MpzT, n: *const MpzT, d: *const MpzT) {
        __gmpz_init(result);
        __gmpz_divexact(result, n, d);
    }

    // lean::power(mpz&, mpz const&, unsigned)
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean5powerERNS_3mpzERKS0_j"
    )]
    pub unsafe extern "C" fn power_fn(a: *mut MpzT, b: *const MpzT, k: u32) {
        __gmpz_pow_ui(a, b, k as c_ulong);
    }

    // lean::gcd(mpz&, mpz const&, mpz const&)
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean3gcdERNS_3mpzERKS0_S3_"
    )]
    pub unsafe extern "C" fn gcd_fn(g: *mut MpzT, a: *const MpzT, b: *const MpzT) {
        __gmpz_gcd(g, a, b);
    }
}
