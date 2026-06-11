// src/rust/lean_runtime/src/runtime_object_nat_int.rs
// Ported from src/runtime/object.cpp — Natural numbers and Integers section.
// Include from lib.rs: include!("runtime_object_nat_int.rs");
//
// Strategy: all operations delegate to the C++ mpz wrappers (alloc_mpz,
// mpz_value, etc.) via extern "C" shims.  Once runtime_mpz.rs exists and
// exposes a safe Rust mpz API, these can be replaced with pure-Rust code.

mod runtime_object_nat_int_impl {
    use super::*;
    use core::ffi::{c_char, c_int};

    // ── C++ shims that manipulate mpz_object ────────────────────────────────
    extern "C" {
        // Allocate a new mpz_object wrapping an existing mpz value (C++ side).
        // These are thin C++ functions added in src/runtime/object_shims.cpp:
        //   extern "C" lean_object * lean_shim_alloc_mpz_from_str(const char *);
        //   extern "C" lean_object * lean_shim_mpz_add(lean_object *, lean_object *);
        //   ... etc.
        //
        // For now we use the existing C++ nat/int big* operations directly
        // by forwarding from Rust to them.  The symbols below are the C++ ones
        // that are NOT being removed yet — we just re-export them under the same
        // name by calling through.  When mpz.cpp is ported to Rust we will
        // replace these bodies.
        fn lean_nat_big_succ_cxx(a: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_add_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_sub_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_mul_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_overflow_mul_cxx(a1: usize, a2: usize) -> *mut LeanObject;
        fn lean_nat_big_div_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_div_exact_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_mod_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_eq_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_nat_big_le_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_nat_big_lt_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_nat_big_land_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_lor_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_xor_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_shiftl_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_big_shiftr_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_pow_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_gcd_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_nat_log2_cxx(a: *mut LeanObject) -> *mut LeanObject;
        fn lean_cstr_to_nat_cxx(n: *const c_char) -> *mut LeanObject;
        fn lean_big_usize_to_nat_cxx(n: usize) -> *mut LeanObject;
        fn lean_big_uint64_to_nat_cxx(n: u64) -> *mut LeanObject;
        fn lean_mpz_hash_cxx(o: *mut LeanObject) -> u32;
        fn lean_mpz_eq_cxx(o1: *mut LeanObject, o2: *mut LeanObject) -> u8;
        fn lean_alloc_mpz_from_mpz_cxx(o: *mut LeanObject) -> *mut LeanObject;
        fn lean_uint8_of_big_nat_cxx(a: *mut LeanObject) -> u8;
        fn lean_uint16_of_big_nat_cxx(a: *mut LeanObject) -> u16;
        fn lean_uint32_of_big_nat_cxx(a: *mut LeanObject) -> u32;
        fn lean_uint64_of_big_nat_cxx(a: *mut LeanObject) -> u64;
        fn lean_usize_of_big_nat_cxx(a: *mut LeanObject) -> usize;
        fn lean_int8_of_big_int_cxx(a: *mut LeanObject) -> i8;
        fn lean_int16_of_big_int_cxx(a: *mut LeanObject) -> i16;
        fn lean_int32_of_big_int_cxx(a: *mut LeanObject) -> i32;
        fn lean_int64_of_big_int_cxx(a: *mut LeanObject) -> i64;
        fn lean_isize_of_big_int_cxx(a: *mut LeanObject) -> isize;
        fn lean_int_big_neg_cxx(a: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_add_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_sub_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_mul_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_div_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_div_exact_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_mod_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_ediv_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_emod_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject;
        fn lean_int_big_eq_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_int_big_le_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_int_big_lt_cxx(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_int_big_nonneg_cxx(a: *mut LeanObject) -> bool;
        fn lean_big_int_to_nat_cxx(a: *mut LeanObject) -> *mut LeanObject;
        fn lean_cstr_to_int_cxx(n: *const c_char) -> *mut LeanObject;
        fn lean_big_int_to_int_cxx(n: c_int) -> *mut LeanObject;
        fn lean_big_size_t_to_int_cxx(n: usize) -> *mut LeanObject;
        fn lean_big_int64_to_int_cxx(n: i64) -> *mut LeanObject;
        fn lean_uint64_mix_hash_cxx(a1: u64, a2: u64) -> u64;
        #[cfg(feature = "use_gmp")]
        fn lean_alloc_mpz_gmp(v: *mut core::ffi::c_void) -> *mut LeanObject;
        #[cfg(feature = "use_gmp")]
        fn lean_extract_mpz_value_gmp(o: *mut LeanObject, v: *mut core::ffi::c_void);
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Natural numbers
    // ════════════════════════════════════════════════════════════════════════════

    #[no_mangle]
    pub unsafe extern "C" fn lean_cstr_to_nat(n: *const c_char) -> *mut LeanObject {
        lean_cstr_to_nat_cxx(n)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_usize_to_nat(n: usize) -> *mut LeanObject {
        lean_big_usize_to_nat_cxx(n)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_uint64_to_nat(n: u64) -> *mut LeanObject {
        lean_big_uint64_to_nat_cxx(n)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_succ(a: *mut LeanObject) -> *mut LeanObject {
        lean_nat_big_succ_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_add(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_add_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_sub(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_sub_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_mul(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_mul_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_overflow_mul(a1: usize, a2: usize) -> *mut LeanObject {
        lean_nat_overflow_mul_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_div(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_div_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_div_exact(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_div_exact_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_mod(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_mod_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_eq(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        lean_nat_big_eq_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_le(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        lean_nat_big_le_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_lt(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        lean_nat_big_lt_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_land(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_land_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_lor(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_lor_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_xor(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_xor_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_shiftl(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_shiftl_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_shiftr(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_big_shiftr_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_pow(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_pow_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_gcd(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_nat_gcd_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_log2(a: *mut LeanObject) -> *mut LeanObject {
        lean_nat_log2_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_mpz_hash(o: *mut LeanObject) -> u32 {
        lean_mpz_hash_cxx(o)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_mpz_eq(
        o1: *mut LeanObject, o2: *mut LeanObject,
    ) -> u8 {
        lean_mpz_eq_cxx(o1, o2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_alloc_mpz_from_mpz(o: *mut LeanObject) -> *mut LeanObject {
        lean_alloc_mpz_from_mpz_cxx(o)
    }

    // ── UInt truncations ────────────────────────────────────────────────────
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint8_of_big_nat(a: *mut LeanObject) -> u8 {
        lean_uint8_of_big_nat_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint16_of_big_nat(a: *mut LeanObject) -> u16 {
        lean_uint16_of_big_nat_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint32_of_big_nat(a: *mut LeanObject) -> u32 {
        lean_uint32_of_big_nat_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint64_of_big_nat(a: *mut LeanObject) -> u64 {
        lean_uint64_of_big_nat_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_usize_of_big_nat(a: *mut LeanObject) -> usize {
        lean_usize_of_big_nat_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_uint64_mix_hash(a1: u64, a2: u64) -> u64 {
        lean_uint64_mix_hash_cxx(a1, a2)
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Integers
    // ════════════════════════════════════════════════════════════════════════════

    #[no_mangle]
    pub unsafe extern "C" fn lean_big_int_to_nat(a: *mut LeanObject) -> *mut LeanObject {
        lean_big_int_to_nat_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_cstr_to_int(n: *const c_char) -> *mut LeanObject {
        lean_cstr_to_int_cxx(n)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_int_to_int(n: c_int) -> *mut LeanObject {
        lean_big_int_to_int_cxx(n)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_size_t_to_int(n: usize) -> *mut LeanObject {
        lean_big_size_t_to_int_cxx(n)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_int64_to_int(n: i64) -> *mut LeanObject {
        lean_big_int64_to_int_cxx(n)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_neg(a: *mut LeanObject) -> *mut LeanObject {
        lean_int_big_neg_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_add(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_int_big_add_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_sub(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_int_big_sub_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_mul(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_int_big_mul_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_div(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_int_big_div_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_div_exact(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_int_big_div_exact_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_mod(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_int_big_mod_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_ediv(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_int_big_ediv_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_emod(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_int_big_emod_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_eq(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        lean_int_big_eq_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_le(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        lean_int_big_le_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_lt(
        a1: *mut LeanObject, a2: *mut LeanObject,
    ) -> bool {
        lean_int_big_lt_cxx(a1, a2)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_nonneg(a: *mut LeanObject) -> bool {
        lean_int_big_nonneg_cxx(a)
    }

    // ── IntX truncations ─────────────────────────────────────────────────────
    #[no_mangle]
    pub unsafe extern "C" fn lean_int8_of_big_int(a: *mut LeanObject) -> i8 {
        lean_int8_of_big_int_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int16_of_big_int(a: *mut LeanObject) -> i16 {
        lean_int16_of_big_int_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int32_of_big_int(a: *mut LeanObject) -> i32 {
        lean_int32_of_big_int_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_int64_of_big_int(a: *mut LeanObject) -> i64 {
        lean_int64_of_big_int_cxx(a)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_isize_of_big_int(a: *mut LeanObject) -> isize {
        lean_isize_of_big_int_cxx(a)
    }

    // ── GMP raw interface (when USE_GMP is on) ───────────────────────────────
    #[cfg(feature = "use_gmp")]
    #[no_mangle]
    pub unsafe extern "C" fn lean_alloc_mpz(v: *mut core::ffi::c_void) -> *mut LeanObject {
        lean_alloc_mpz_gmp(v)
    }
    #[cfg(feature = "use_gmp")]
    #[no_mangle]
    pub unsafe extern "C" fn lean_extract_mpz_value(
        o: *mut LeanObject, v: *mut core::ffi::c_void,
    ) {
        lean_extract_mpz_value_gmp(o, v);
    }
}
