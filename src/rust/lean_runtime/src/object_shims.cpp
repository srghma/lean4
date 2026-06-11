/*
 * src/runtime/object_shims.cpp
 *
 * Thin C++ shims that let Rust call internal functions via stable _cxx-suffixed
 * extern "C" symbols.  These are NOT part of the public lean.h ABI; they are
 * link-time bridges for the Rust->C++ migration.
 *
 * Once an operation is fully ported to Rust (e.g. after runtime_mpz.rs lands)
 * the corresponding shim here can be deleted and the _cxx call in the .rs file
 * replaced with pure Rust.
 */
#include <lean/lean.h>
#include "runtime/object.h"   // alloc_mpz, mpz_value, mpz_to_nat_core, etc.
#include "runtime/mpz.h"
#include "runtime/hash.h"
#include "runtime/thread.h"

// Pull the lean namespace helpers into scope
using namespace lean;

// ─────────────────────────────────────────────────────────────────────────────
// Dealloc export
// Called by runtime_object_rc.rs and runtime_object_string/array.rs
// ─────────────────────────────────────────────────────────────────────────────

extern "C" void lean_dealloc_export(lean_object * o, size_t sz) {
#ifdef LEAN_SMALL_ALLOCATOR
    dealloc(o, sz);
#elif defined(LEAN_MIMALLOC)
    mi_free_size(o, sz);
#else
    free_sized(o, sz);
#endif
}

// ─────────────────────────────────────────────────────────────────────────────
// Thunk get — still in C++ until LeanThunkObject layout is stable in Rust
// ─────────────────────────────────────────────────────────────────────────────

extern "C" b_obj_res lean_thunk_get_core_impl_cxx(b_obj_arg t) {
    return lean_thunk_get_core(t);
}

// ─────────────────────────────────────────────────────────────────────────────
// Natural number big operations
// ─────────────────────────────────────────────────────────────────────────────

extern "C" obj_res lean_nat_big_succ_cxx(obj_arg a)
    { return lean_nat_big_succ(a); }
extern "C" obj_res lean_nat_big_add_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_add(a1, a2); }
extern "C" obj_res lean_nat_big_sub_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_sub(a1, a2); }
extern "C" obj_res lean_nat_big_mul_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_mul(a1, a2); }
extern "C" obj_res lean_nat_overflow_mul_cxx(size_t a1, size_t a2)
    { return lean_nat_overflow_mul(a1, a2); }
extern "C" obj_res lean_nat_big_div_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_div(a1, a2); }
extern "C" obj_res lean_nat_big_div_exact_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_div_exact(a1, a2); }
extern "C" obj_res lean_nat_big_mod_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_mod(a1, a2); }
extern "C" bool lean_nat_big_eq_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_eq(a1, a2); }
extern "C" bool lean_nat_big_le_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_le(a1, a2); }
extern "C" bool lean_nat_big_lt_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_lt(a1, a2); }
extern "C" obj_res lean_nat_big_land_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_land(a1, a2); }
extern "C" obj_res lean_nat_big_lor_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_lor(a1, a2); }
extern "C" obj_res lean_nat_big_xor_cxx(obj_arg a1, obj_arg a2)
    { return lean_nat_big_xor(a1, a2); }
extern "C" obj_res lean_nat_shiftl_cxx(b_obj_arg a1, b_obj_arg a2)
    { return lean_nat_shiftl(a1, a2); }
extern "C" obj_res lean_nat_big_shiftr_cxx(b_obj_arg a1, b_obj_arg a2)
    { return lean_nat_big_shiftr(a1, a2); }
extern "C" obj_res lean_nat_pow_cxx(b_obj_arg a1, b_obj_arg a2)
    { return lean_nat_pow(a1, a2); }
extern "C" obj_res lean_nat_gcd_cxx(b_obj_arg a1, b_obj_arg a2)
    { return lean_nat_gcd(a1, a2); }
extern "C" obj_res lean_nat_log2_cxx(b_obj_arg a)
    { return lean_nat_log2(a); }
extern "C" obj_res lean_cstr_to_nat_cxx(char const * n)
    { return lean_cstr_to_nat(n); }
extern "C" obj_res lean_big_usize_to_nat_cxx(size_t n)
    { return lean_big_usize_to_nat(n); }
extern "C" obj_res lean_big_uint64_to_nat_cxx(uint64_t n)
    { return lean_big_uint64_to_nat(n); }
extern "C" unsigned lean_mpz_hash_cxx(lean_object * o)
    { return lean_mpz_hash(o); }
extern "C" uint8_t lean_mpz_eq_cxx(lean_object * o1, lean_object * o2)
    { return lean_mpz_eq(o1, o2); }
extern "C" lean_object * lean_alloc_mpz_from_mpz_cxx(lean_object * o)
    { return lean_alloc_mpz_from_mpz(o); }

// ─────────────────────────────────────────────────────────────────────────────
// UInt / IntX truncations
// ─────────────────────────────────────────────────────────────────────────────

extern "C" uint8_t  lean_uint8_of_big_nat_cxx(b_obj_arg a)  { return lean_uint8_of_big_nat(a); }
extern "C" uint16_t lean_uint16_of_big_nat_cxx(b_obj_arg a) { return lean_uint16_of_big_nat(a); }
extern "C" uint32_t lean_uint32_of_big_nat_cxx(b_obj_arg a) { return lean_uint32_of_big_nat(a); }
extern "C" uint64_t lean_uint64_of_big_nat_cxx(b_obj_arg a) { return lean_uint64_of_big_nat(a); }
extern "C" size_t   lean_usize_of_big_nat_cxx(b_obj_arg a)  { return lean_usize_of_big_nat(a); }
extern "C" uint64_t lean_uint64_mix_hash_cxx(uint64_t a1, uint64_t a2)
    { return lean_uint64_mix_hash(a1, a2); }

extern "C" int8_t   lean_int8_of_big_int_cxx(b_obj_arg a)  { return lean_int8_of_big_int(a); }
extern "C" int16_t  lean_int16_of_big_int_cxx(b_obj_arg a) { return lean_int16_of_big_int(a); }
extern "C" int32_t  lean_int32_of_big_int_cxx(b_obj_arg a) { return lean_int32_of_big_int(a); }
extern "C" int64_t  lean_int64_of_big_int_cxx(b_obj_arg a) { return lean_int64_of_big_int(a); }
extern "C" ptrdiff_t lean_isize_of_big_int_cxx(b_obj_arg a) { return lean_isize_of_big_int(a); }

// ─────────────────────────────────────────────────────────────────────────────
// Integer big operations
// ─────────────────────────────────────────────────────────────────────────────

extern "C" obj_res lean_big_int_to_nat_cxx(obj_arg a)
    { return lean_big_int_to_nat(a); }
extern "C" obj_res lean_cstr_to_int_cxx(char const * n)
    { return lean_cstr_to_int(n); }
extern "C" obj_res lean_big_int_to_int_cxx(int n)
    { return lean_big_int_to_int(n); }
extern "C" obj_res lean_big_size_t_to_int_cxx(size_t n)
    { return lean_big_size_t_to_int(n); }
extern "C" obj_res lean_big_int64_to_int_cxx(int64_t n)
    { return lean_big_int64_to_int(n); }
extern "C" obj_res lean_int_big_neg_cxx(obj_arg a)
    { return lean_int_big_neg(a); }
extern "C" obj_res lean_int_big_add_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_add(a1, a2); }
extern "C" obj_res lean_int_big_sub_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_sub(a1, a2); }
extern "C" obj_res lean_int_big_mul_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_mul(a1, a2); }
extern "C" obj_res lean_int_big_div_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_div(a1, a2); }
extern "C" obj_res lean_int_big_div_exact_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_div_exact(a1, a2); }
extern "C" obj_res lean_int_big_mod_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_mod(a1, a2); }
extern "C" obj_res lean_int_big_ediv_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_ediv(a1, a2); }
extern "C" obj_res lean_int_big_emod_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_emod(a1, a2); }
extern "C" bool lean_int_big_eq_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_eq(a1, a2); }
extern "C" bool lean_int_big_le_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_le(a1, a2); }
extern "C" bool lean_int_big_lt_cxx(obj_arg a1, obj_arg a2)
    { return lean_int_big_lt(a1, a2); }
extern "C" bool lean_int_big_nonneg_cxx(obj_arg a)
    { return lean_int_big_nonneg(a); }

// ─────────────────────────────────────────────────────────────────────────────
// GMP raw (only compiled when USE_GMP is set)
// ─────────────────────────────────────────────────────────────────────────────
#ifdef LEAN_USE_GMP
extern "C" lean_object * lean_alloc_mpz_gmp(mpz_t v)  { return lean_alloc_mpz(v); }
extern "C" void lean_extract_mpz_value_gmp(lean_object * o, mpz_t v)
    { lean_extract_mpz_value(o, v); }
#endif

// ─────────────────────────────────────────────────────────────────────────────
// External class / ctor helpers used by runtime_object_rc.rs
// ─────────────────────────────────────────────────────────────────────────────

extern "C" void lean_runtime_mpz_destroy(lean_object * o) {
    // called from Rust lean_free_object path for LeanMPZ
    to_mpz(o)->m_value.~mpz();
    lean_free_small_object(o);
}

// ─────────────────────────────────────────────────────────────────────────────
// C++ exception throw shims (needed by runtime_exception.rs)
// These are defined here rather than in a separate file to keep the shim
// surface in one place.
// ─────────────────────────────────────────────────────────────────────────────
#include "runtime/exception.h"

extern "C" [[noreturn]] void lean_cxx_throw_heartbeat_exception() {
    throw lean::heartbeat_exception();
}
extern "C" [[noreturn]] void lean_cxx_throw_interrupt_exception() {
    throw lean::interrupt_exception();
}
extern "C" [[noreturn]] void lean_cxx_throw_stack_overflow_exception() {
    throw lean::stack_overflow_exception();
}
extern "C" [[noreturn]] void lean_cxx_throw_lean_exception(lean_object * e) {
    throw lean::lean_exception(e);
}
extern "C" int lean_cxx_uncaught_exceptions() {
    return std::uncaught_exceptions();
}

// ─────────────────────────────────────────────────────────────────────────────
// C++ throw shim for get_stack_size_failed (used by runtime_exception.rs)
// ─────────────────────────────────────────────────────────────────────────────
extern "C" [[noreturn]] void lean_cxx_throw_get_stack_size_failed() {
    throw lean::exception("failed to retrieve thread stack size");
}
