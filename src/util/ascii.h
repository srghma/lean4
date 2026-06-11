/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstring>
namespace lean {
extern "C" bool lean_util_is_safe_ascii_char(char c);
extern "C" bool lean_util_is_safe_ascii(char const * str);
extern "C" bool lean_util_is_safe_ascii_n(char const * str, size_t sz);

/** \brief Return true iff \c c is a "safe" ASCII characters.
    It is a "keyboard" character. */
inline bool is_safe_ascii(char c) { return lean_util_is_safe_ascii_char(c); }
/** \brief Return true iff the given string contains only "safe"
    ASCII character. */
inline bool is_safe_ascii(char const * str) { return lean_util_is_safe_ascii(str); }
/** \brief Return true iff the given string of size sz contains only "safe"
    ASCII character. */
inline bool is_safe_ascii(char const * str, size_t sz) { return lean_util_is_safe_ascii_n(str, sz); }

inline void initialize_ascii() {}
inline void finalize_ascii() {}
}
