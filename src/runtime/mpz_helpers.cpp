/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Thin C++ shim providing mpz output functions that need std::string/ostream ABI.
All other lean::mpz methods are implemented in src/rust/lean_runtime/src/runtime_mpz.rs.
*/
#include <string>
#include <sstream>
#include <memory>
#include "runtime/mpz.h"

namespace lean {

std::ostream & operator<<(std::ostream & out, mpz const & v) {
#ifdef LEAN_USE_GMP
    size_t sz = mpz_sizeinbase(v.m_val, 10) + 2;
    if (sz < 1024) {
        char buffer[1024];
        mpz_get_str(buffer, 10, v.m_val);
        out << buffer;
    } else {
        std::unique_ptr<char[]> buffer(new char[sz]);
        mpz_get_str(buffer.get(), 10, v.m_val);
        out << buffer.get();
    }
#else
    if (v.m_sign) out << "-";
    std::unique_ptr<char[]> buf(new char[11 * v.m_size + 1]);
    out << mpn_to_string(v.m_digits, v.m_size, buf.get(), 11 * v.m_size + 1);
#endif
    return out;
}

std::string mpz::to_string() const {
    std::ostringstream out;
    out << *this;
    return out.str();
}

} // namespace lean
