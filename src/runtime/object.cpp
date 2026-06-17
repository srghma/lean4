/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <lean/lean.h>
#include "runtime/object.h"

#if !defined(__STDC_VERSION_STDLIB_H__) || __STDC_VERSION_STDLIB_H__ < 202311L
extern "C" LEAN_EXPORT
#if defined(__GLIBC__) && (defined(__GNUC__) || defined(__clang__))
// glibc tacks on `__attribute__((nothrow))` to its declarations. In C++ this requires either
// `__attribute__((nothrow))` to be present or `noexcept`.
__attribute__((nothrow))
#endif
__attribute__((weak)) void free_sized(void *ptr, size_t) {
    free(ptr);
}
#endif

namespace lean {

// lean_alloc_mpz is implemented in Rust (runtime_object_nat_int.rs)
#ifdef LEAN_USE_GMP
extern "C" lean_object * lean_alloc_mpz(mpz_t v);
#endif

object * alloc_mpz(mpz const & m) {
#ifdef LEAN_USE_GMP
    mpz_t tmp;
    mpz_init(tmp);
    m.set(tmp);
    lean_object * result = lean_alloc_mpz(tmp);
    mpz_clear(tmp);
    return result;
#else
    lean_internal_panic("alloc_mpz: non-GMP build not supported with Rust nat/int");
    lean_unreachable();
#endif
}

object * mpz_to_nat_core(mpz const & m) {
    lean_assert(!m.is_size_t() || m.get_size_t() > LEAN_MAX_SMALL_NAT);
    return alloc_mpz(m);
}

// C++ wrappers — always compiled (used by io.cpp, object_ref.h, kernel/expr.cpp, etc.)
object * mk_string(std::string const & s) {
    return lean_mk_string_from_bytes(s.data(), s.size());
}

object * mk_ascii_string_unchecked(std::string const & s) {
    return lean_mk_string_unchecked(s.data(), s.size(), s.size());
}

std::string string_to_std(b_obj_arg o) {
    lean_assert(string_size(o) > 0);
    return std::string(lean_to_string(o)->m_data, lean_string_size(o) - 1);
}

extern "C" void lean_finalize_external_classes();

LEAN_EXPORT void initialize_object() {
}

LEAN_EXPORT void finalize_object() {
    lean_finalize_external_classes();
}

}
