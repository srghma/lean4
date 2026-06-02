/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include "runtime/optional.h"
#include "lean/lean.h"

namespace lean {
using uchar = unsigned char;

extern "C" bool lean_runtime_is_utf8_next(unsigned char c);
extern "C" unsigned lean_runtime_get_utf8_size(unsigned char c);
extern "C" size_t lean_utf8_strlen(char const * str);
extern "C" size_t lean_utf8_n_strlen(char const * str, size_t sz);
extern "C" bool lean_runtime_utf8_char_pos(char const * str, size_t char_idx, size_t * out_pos);
extern "C" char const * lean_runtime_get_utf8_last_char(char const * str);
extern "C" unsigned lean_runtime_utf8_to_unicode(uchar const * begin, uchar const * end);
extern "C" bool lean_runtime_get_utf8_first_byte_size(unsigned char c, unsigned * out_size);
extern "C" unsigned lean_runtime_next_utf8(char const * str, size_t size, size_t * pos);
extern "C" bool lean_runtime_validate_utf8_one(uint8_t const * str, size_t size, size_t * pos);
extern "C" bool lean_runtime_validate_utf8(uint8_t const * str, size_t size, size_t * pos, size_t * i);
extern "C" unsigned lean_runtime_push_unicode_scalar(char * d, unsigned code);

inline bool is_utf8_next(unsigned char c) { return lean_runtime_is_utf8_next(c); }
inline unsigned get_utf8_size(unsigned char c) { return lean_runtime_get_utf8_size(c); }
/* Return the length of the null terminated string encoded using UTF8 */
inline size_t utf8_strlen(char const * str) { return lean_utf8_strlen(str); }
/* Return the length of the string `str` encoded using UTF8.
   `str` may contain null characters. */
inline size_t utf8_strlen(std::string const & str) { return lean_utf8_n_strlen(str.data(), str.size()); }
/* Return the length of the string `str` encoded using UTF8.
   `str` may contain null characters. */
inline size_t utf8_strlen(char const * str, size_t sz) { return lean_utf8_n_strlen(str, sz); }
inline optional<size_t> utf8_char_pos(char const * str, size_t char_idx) {
    size_t pos;
    if (lean_runtime_utf8_char_pos(str, char_idx, &pos))
        return some<size_t>(pos);
    else
        return optional<size_t>();
}
inline char const * get_utf8_last_char(char const * str) { return lean_runtime_get_utf8_last_char(str); }
inline std::string utf8_trim(std::string const & s) {
    int start = -1, stop = -1;
    for (unsigned i = 0; i < s.size(); i += get_utf8_size(s[i])) {
        if (s[i] == ' ') {
            if (stop == -1)
                stop = i;
        } else {
            if (start == -1)
                start = i;
            stop = -1;
        }
    }
    if (stop == -1)
        stop = static_cast<int>(s.size());
    if (start < 0)
        return std::string();
    return s.substr(static_cast<size_t>(start), static_cast<size_t>(stop - start));
}
inline unsigned utf8_to_unicode(uchar const * begin, uchar const * end) {
    return lean_runtime_utf8_to_unicode(begin, end);
}
inline unsigned utf8_to_unicode(char const * begin, char const * end) {
    return utf8_to_unicode(reinterpret_cast<uchar const *>(begin),
                           reinterpret_cast<uchar const *>(end));
}

/* If `c` is the first byte of an utf-8 encoded unicode scalar value,
   then return `some(n)` where `n` is the number of bytes needed to encode
   the unicode scalar value. Otherwise, return `none` */
inline optional<unsigned> get_utf8_first_byte_opt(unsigned char c) {
    unsigned size;
    if (lean_runtime_get_utf8_first_byte_size(c, &size))
        return optional<unsigned>(size);
    else
        return optional<unsigned>();
}

/* "Read" next unicode character starting at position i in a string using UTF-8 encoding.
   Return the unicode character and update i. */
inline unsigned next_utf8(std::string const & str, size_t & i) {
    return lean_runtime_next_utf8(str.data(), str.size(), &i);
}
inline unsigned next_utf8(char const * str, size_t size, size_t & i) {
    return lean_runtime_next_utf8(str, size, &i);
}

/* Decode a UTF-8 encoded string `str` into unicode scalar values */
inline void utf8_decode(std::string const & str, std::vector<unsigned> & out) {
    size_t i = 0;
    while (i < str.size())
        out.push_back(next_utf8(str, i));
}

/* Returns true if the given character is valid UTF-8 */
inline bool validate_utf8_one(uint8_t const * str, size_t size, size_t & pos) {
    return lean_runtime_validate_utf8_one(str, size, &pos);
}

/* Returns true if the provided string is valid UTF-8 */
inline bool validate_utf8(uint8_t const * str, size_t size, size_t & pos, size_t & i) {
    return lean_runtime_validate_utf8(str, size, &pos, &i);
}

/* Push a unicode scalar value into a utf-8 encoded string */
inline void push_unicode_scalar(std::string & s, unsigned code) {
    char buf[4];
    unsigned len = lean_runtime_push_unicode_scalar(buf, code);
    s.append(buf, len);
}

/* Store unicode scalar value at `d`, `d` must point to memory with enough space to store `c`.
   Return the number of bytes consumed. */
inline unsigned push_unicode_scalar(char * d, unsigned code) {
    return lean_runtime_push_unicode_scalar(d, code);
}
}
