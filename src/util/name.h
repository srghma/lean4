/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <iostream>
#include <functional>
#include <algorithm>
#include <utility>
#include "runtime/optional.h"
#include "runtime/string_ref.h"
#include "runtime/list_ref.h"
#include "runtime/buffer.h"
#include "runtime/utf8.h"
#include "util/ascii.h"
#include "util/pair.h"
#include "util/nat.h"


namespace lean {
constexpr char const * lean_name_separator = ".";
#ifdef _MSC_VER
constexpr char16_t id_begin_escape = L'\xab';
constexpr char16_t id_end_escape = L'\xbb';
#else
constexpr char16_t id_begin_escape = u'«';
constexpr char16_t id_end_escape = u'»';
#endif

extern "C" uint64_t lean_name_hash_exported(lean_obj_arg n);
extern "C" obj_res lean_name_mk_string(obj_arg p, obj_arg s);
extern "C" obj_res lean_name_mk_numeral(obj_arg p, obj_arg n);
extern "C" obj_res lean_name_append_after(obj_arg n, obj_arg s);
extern "C" obj_res lean_name_append_before(obj_arg n, obj_arg s);
extern "C" obj_res lean_name_append_index_after(obj_arg n, obj_arg i);
extern "C" unsigned lean_name_next_internal_unique_id();

inline uint64_t lean_name_hash_exported_b(b_lean_obj_arg n) {
    lean_inc(n);
    return lean_name_hash_exported(n);
}

enum class name_kind { ANONYMOUS, STRING, NUMERAL };
/** \brief Hierarchical names. */
class LEAN_EXPORT name : public object_ref {
public:
    /* Low level primitives */
    static bool eq(b_obj_arg n1, b_obj_arg n2) { return lean_name_eq(n1, n2); }
    static name_kind kind(object * o) { return static_cast<name_kind>(obj_tag(o)); }
    static bool is_anonymous(object * o) { return is_scalar(o); }
    static object * get_prefix(object * o) { return cnstr_get(o, 0); }
    static string_ref const & get_string(object * o) { return static_cast<string_ref const &>(cnstr_get_ref(o, 1)); }
    static nat const & get_numeral(object * o) { return static_cast<nat const &>(cnstr_get_ref(o, 1)); }
    static int cmp_core(object * o1, object * o2);
    size_t size_core(bool unicode) const;
private:
    explicit name(object_ref && r) noexcept:object_ref(r) {}
public:
    name():object_ref(box(static_cast<unsigned>(name_kind::ANONYMOUS))) {}
    explicit name(obj_arg o):object_ref(o) {}
    name(b_obj_arg r, bool b):object_ref(r, b) {}
    name(name const & prefix, char const * name);
    name(name const & prefix, unsigned k);
    name(name const & prefix, nat const & n);
    name(name const & prefix, string_ref const & s);
    name(char const * n):name(name(), n) {}
    name(std::string const & s):name(name(), string_ref(s)) {}
    name(string_ref const & s):name(name(), s) {}
    name(name const & other):object_ref(other) {}
    name(name && other) noexcept:object_ref(std::move(other)) {}
    /**
       \brief Create a hierarchical name using the given strings.
       Example: <code>name{"foo", "bla", "tst"}</code> creates the hierarchical
       name <tt>foo::bla::tst</tt>.
    */
    name(std::initializer_list<char const *> const & l);
    static name const & anonymous();
    /**
        \brief Create a unique internal name that is not meant to exposed
        to the user. Different modules require a unique name.
        The unique name is created using a numeric prefix.
        A module that needs to create several unique names should
        the following idiom:
        <code>
            name unique_prefix = name::mk_internal_unique_name();
            name unique_name_1(unique_prefix, 1);
            ...
            name unique_name_k(unique_prefix, k);
        </code>
    */
    static name mk_internal_unique_name();
    name & operator=(name const & other) { object_ref::operator=(other); return *this; }
    name & operator=(name && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    static uint64_t hash(b_obj_arg n) {
       lean_assert(lean_name_hash(n) == lean_name_hash_exported_b(n));
       return lean_name_hash(n);
    }
    uint64_t hash() const { return hash(raw()); }
    /** \brief Return true iff \c n1 is a prefix of \c n2. */
    friend bool is_prefix_of(name const & n1, name const & n2);
    friend bool operator==(name const & a, name const & b) { return name::eq(a.raw(), b.raw()); }
    friend bool operator!=(name const & a, name const & b) { return !(a == b); }
    friend bool operator==(name const & a, char const * b);
    friend bool operator!=(name const & a, char const * b) { return !(a == b); }
    /** \brief Total order on hierarchical names. */
    friend int cmp(name const & a, name const & b) { return cmp_core(a.raw(), b.raw()); }
    friend bool operator<(name const & a, name const & b) { return cmp(a, b) < 0; }
    friend bool operator>(name const & a, name const & b) { return cmp(a, b) > 0; }
    friend bool operator<=(name const & a, name const & b) { return cmp(a, b) <= 0; }
    friend bool operator>=(name const & a, name const & b) { return cmp(a, b) >= 0; }
    name_kind kind() const { return kind(raw()); }
    bool is_anonymous() const { return kind() == name_kind::ANONYMOUS; }
    bool is_string() const    { return kind() == name_kind::STRING; }
    bool is_numeral() const   { return kind() == name_kind::NUMERAL; }
    explicit operator bool() const { return kind() != name_kind::ANONYMOUS; }
    nat const & get_numeral() const { lean_assert(is_numeral()); return get_numeral(raw()); }
    string_ref const & get_string() const { lean_assert(is_string()); return get_string(raw()); }
    name const & get_prefix() const {
        if (is_anonymous()) return *this;
        else return static_cast<name const &>(cnstr_get_ref(*this, 0));
    }
    bool is_atomic() const { return is_anonymous() || kind(get_prefix(raw())) == name_kind::ANONYMOUS; }
    /** \brief Given a name of the form a_1.a_2. ... .a_k, return a_1 if k >= 1, or the empty name otherwise. */
    name get_root() const;
    /** \brief Convert this hierarchical name into a string. */
    std::string to_string(char const * sep = lean_name_separator) const;
    std::string escape(char const * sep = lean_name_separator) const;
    /** \brief Size of the this name (in characters). */
    size_t size() const;
    /** \brief Size of the this name in unicode. */
    size_t utf8_size() const;
    /** \brief Return true iff the name contains only safe ASCII chars */
    bool is_safe_ascii() const;
    friend LEAN_EXPORT std::ostream & operator<<(std::ostream & out, name const & n);
    /** \brief Concatenate the two given names. */
    friend name operator+(name const & n1, name const & n2);

    /**
        \brief Given a name of the form a_1.a_2. ... .a_k,
           If a_k is a string,  return a_1.a_2. ... .a_k', where a_k' is the string p concatenated with a_k.
           If a_k is a numeral, return a_1.a_2. ... .p.a_k
    */
    name append_before(char const * p) const;
    /**
        \brief Given a name of the form a_1.a_2. ... .a_k,
           If a_k is a string,  return a_1.a_2. ... .a_k', where a_k' is the string a_k concatenated with s.
           If a_k is a numeral, return a_1.a_2. ... .a_k.s
    */
    name append_after(char const * s) const;

    /**
        \brief Given a name of the form a_1.a_2. ... .a_k,
           If a_k is a string,  return a_1.a_2. ... .a_k', where a_k' is the string a_k concatenated with _i.
           Otherwise add _i as the last component.
    */
    name append_after(unsigned i) const;

    /**
        \brief Given a name of the form a_1.a_2. ... .a_k,
           If a_k is a string, return the name itself.
           Otherwise add the empty string as the last component.
    */
    name get_subscript_base() const;

    /**
        \brief Given a name of the form a_1.a_2. ... .a_k, determine whether it was produced by append_after(unsigned).
    */
    optional<pair<name, unsigned>> is_subscripted() const;

    /**
        \brief If prefix is a prefix of this name, then return a new name where the prefix is replaced with new_prefix.
        Otherwise, return this name.
    */
    name replace_prefix(name const & prefix, name const & new_prefix) const;

    friend void swap(name & a, name & b) { object_ref::swap(a, b); }
    /**
       \brief Quicker version of \c cmp that uses the hashcode.
       Remark: we should not use it when we want to order names using
       lexicographical order.
    */
    friend int quick_cmp(name const & a, name const & b) {
        if (a.raw() == b.raw())
            return 0;
        unsigned h1 = a.hash();
        unsigned h2 = b.hash();
        if (h1 != h2) {
            return h1 < h2 ? -1 : 1;
        } else if (a == b) {
            return 0;
        } else {
            return cmp(a, b);
        }
    }
};

struct name_hash_fn { unsigned operator()(name const & n) const { return n.hash(); } };
struct name_eq_fn { bool operator()(name const & n1, name const & n2) const { return n1 == n2; } };
struct name_quick_cmp {
    typedef name type;
    int operator()(name const & n1, name const & n2) const { return quick_cmp(n1, n2); }
};

typedef list_ref<name> names;

void initialize_name();
void finalize_name();

inline std::ostream & operator<<(std::ostream & out, name const & n) {
    return out << n.to_string();
}

inline name::name(name const & prefix, char const * n):
    object_ref(lean_name_mk_string(prefix.raw(), lean_mk_string(n))) {
    inc(prefix.raw());
}

inline name::name(name const & prefix, unsigned k):
    object_ref(lean_name_mk_numeral(prefix.raw(), lean_unsigned_to_nat(k))) {
    inc(prefix.raw());
}

inline name::name(name const & prefix, string_ref const & s):
    object_ref(lean_name_mk_string(prefix.raw(), s.raw())) {
    inc(prefix.raw());
    inc(s.raw());
}

inline name::name(name const & prefix, nat const & k):
    object_ref(lean_name_mk_numeral(prefix.raw(), k.raw())) {
    inc(prefix.raw());
    inc(k.raw());
}

inline name::name(std::initializer_list<char const *> const & l):name() {
    if (l.size() == 0) {
        return;
    } else {
        auto it = l.begin();
        *this = name(*it);
        ++it;
        for (; it != l.end(); ++it)
            *this = name(*this, *it);
    }
}

inline bool is_greek_unicode(unsigned u) { return 0x391 <= u && u <= 0x3DD; }
inline bool is_letter_like_unicode(unsigned u) {
    return
            (0x3b1  <= u && u <= 0x3c9 && u != 0x3bb) ||
            (0x391  <= u && u <= 0x3A9 && u != 0x3A0 && u != 0x3A3) ||
            (0x3ca  <= u && u <= 0x3fb) ||
            (0x1f00 <= u && u <= 0x1ffe) ||
            (0x2100 <= u && u <= 0x214f) ||
            (0x1d49c <= u && u <= 0x1d59f);
}
inline bool is_sub_script_alnum_unicode(unsigned u) {
    return
            (0x207f <= u && u <= 0x2089) ||
            (0x2090 <= u && u <= 0x209c) ||
            (0x1d62 <= u && u <= 0x1d6a);
}

inline bool is_id_first(unsigned char const * begin, unsigned char const * end) {
    if (std::isalpha(*begin) || *begin == '_')
        return true;
    unsigned u = utf8_to_unicode(begin, end);
    return u == id_begin_escape || is_letter_like_unicode(u);
}
inline bool is_id_first(char const * begin, char const * end) {
    return is_id_first(reinterpret_cast<unsigned char const *>(begin),
                      reinterpret_cast<unsigned char const *>(end));
}

inline bool is_id_rest(unsigned char const * begin, unsigned char const * end) {
    if (std::isalnum(*begin) || *begin == '_' || *begin == '\'' || *begin == '?' || *begin == '!')
        return true;
    unsigned u = utf8_to_unicode(begin, end);
    return is_letter_like_unicode(u) || is_sub_script_alnum_unicode(u);
}
inline bool is_id_rest(char const * begin, char const * end) {
    return is_id_rest(reinterpret_cast<unsigned char const *>(begin),
                      reinterpret_cast<unsigned char const *>(end));
}

inline void copy_limbs(object * p, buffer<object *> & limbs) {
    limbs.clear();
    while (!is_scalar(p)) {
        limbs.push_back(p);
        p = name::get_prefix(p);
    }
    std::reverse(limbs.begin(), limbs.end());
}

inline void display_name_core(std::ostream & out, name const & n, bool escape, char const * sep) {
    lean_assert(!n.is_anonymous());
    name pre = n.get_prefix();
    if (pre) {
        display_name_core(out, pre, escape, sep);
        out << sep;
    }
    if (n.is_string()) {
        std::string str = n.get_string().to_std_string();
        size_t sz = str.size();
        bool must_escape = false;
        if (escape) {
            if (sz == 0)
                must_escape = true;
            if (!is_id_first(str.data(), str.data() + sz))
                must_escape = true;
            if (must_escape && str[0] == '?')
                must_escape = false;
            for (size_t i = get_utf8_size(str[0]); !must_escape && i < sz; i += get_utf8_size(str[i])) {
                if (!is_id_rest(str.data() + i, str.data() + sz))
                    must_escape = true;
            }
        }
        if (must_escape || sz == 0)
            out << "«" << str << "»";
        else
            out << str;
    } else {
        out << n.get_numeral().to_std_string();
    }
}

inline std::string name::to_string(char const * sep) const {
    std::ostringstream s;
    display_name_core(s, *this, false, sep);
    return s.str();
}

inline std::string name::escape(char const * sep) const {
    std::ostringstream s;
    display_name_core(s, *this, true, sep);
    return s.str();
}

inline bool operator==(name const & a, char const * b) {
    return
        a.kind() == name_kind::STRING &&
        is_scalar(name::get_prefix(a.raw())) &&
        name::get_string(a.raw()) == b;
}

inline name operator+(name const & n1, name const & n2) {
    if (n2.is_anonymous()) {
        return n1;
    } else if (n1.is_anonymous()) {
        return n2;
    } else {
        name prefix;
        if (!n2.is_atomic())
            prefix = n1 + n2.get_prefix();
        else
            prefix = n1;
        if (n2.is_string())
            return name(prefix, n2.get_string());
        else
            return name(prefix, n2.get_numeral());
    }
}

inline bool is_prefix_of(name const & n1, name const & n2) {
    if (n2.is_atomic())
        return n1 == n2;
    buffer<object*> limbs1, limbs2;
    object* i1 = n1.raw();
    object* i2 = n2.raw();
    copy_limbs(i1, limbs1);
    copy_limbs(i2, limbs2);
    unsigned sz1 = limbs1.size();
    unsigned sz2 = limbs2.size();
    if (sz1 > sz2)
        return false;
    else if (sz1 == sz2 && n1.hash() != n2.hash())
        return false;
    auto it1 = limbs1.begin();
    auto it2 = limbs2.begin();
    for (; it1 != limbs1.end(); ++it1, ++it2) {
        i1 = *it1;
        i2 = *it2;
        if (cnstr_tag(i1) != cnstr_tag(i2))
            return false;
        if (static_cast<name_kind>(cnstr_tag(i1)) == name_kind::STRING) {
            if (name::get_string(i1) != name::get_string(i2))
                return false;
        } else if (name::get_numeral(i1) != name::get_numeral(i2)) {
            return false;
        }
    }
    return true;
}

inline int name::cmp_core(object * i1, object * i2) {
    buffer<object*> limbs1, limbs2;
    copy_limbs(i1, limbs1);
    copy_limbs(i2, limbs2);
    auto it1 = limbs1.begin();
    auto it2 = limbs2.begin();
    for (; it1 != limbs1.end() && it2 != limbs2.end(); ++it1, ++it2) {
        i1 = *it1;
        i2 = *it2;
        name_kind k1 = static_cast<name_kind>(cnstr_tag(i1));
        name_kind k2 = static_cast<name_kind>(cnstr_tag(i2));
        if (k1 != k2)
            return k1 == name_kind::STRING ? 1 : -1;
        if (k1 == name_kind::STRING) {
            if (get_string(i1) < get_string(i2))
                return -1;
            if (get_string(i2) < get_string(i1))
                return 1;
        } else {
            if (get_numeral(i1) < get_numeral(i2))
                return -1;
            if (get_numeral(i2) < get_numeral(i1))
                return 1;
        }
    }
    if (it1 == limbs1.end() && it2 == limbs2.end())
        return 0;
    return it1 == limbs1.end() ? -1 : 1;
}

inline size_t num_digits(nat k) {
    if (k == 0u)
        return 1;
    int r = 0;
    while (k != 0u) {
        k = k / nat(10);
        r++;
    }
    return r;
}

inline size_t name::size_core(bool unicode) const {
    if (is_scalar(raw())) {
        return strlen("[anonymous]");
    } else {
        object * i = raw();
        size_t sep_sz = strlen(lean_name_separator);
        size_t r = 0;
        while (true) {
            lean_assert(!is_scalar(i));
            if (kind(i) == name_kind::STRING) {
                r += unicode ? get_string(i).length() : get_string(i).num_bytes();
            } else {
                r += num_digits(get_numeral(i));
            }
            i = get_prefix(i);
            if (is_scalar(i))
                break;
            r += sep_sz;
        }
        return r;
    }
}

inline size_t name::size() const { return size_core(false); }
inline size_t name::utf8_size() const { return size_core(true); }
inline bool name::is_safe_ascii() const {
    object * i = raw();
    while (!is_scalar(i)) {
        if (kind(i) == name_kind::STRING) {
            if (!::lean::is_safe_ascii(get_string(i).data(), get_string(i).num_bytes()))
                return false;
        }
        i = get_prefix(i);
    }
    return true;
}

inline name name::get_root() const {
    name n = *this;
    while (n.get_prefix()) {
        n = n.get_prefix();
    }
    return n;
}

inline name name::append_before(char const * p) const {
    return name(lean_name_append_before(to_obj_arg(), lean_mk_string(p)));
}

inline name name::append_after(char const * s) const {
    return name(lean_name_append_after(to_obj_arg(), lean_mk_string(s)));
}

inline name name::get_subscript_base() const {
    if (is_string()) {
        return *this;
    } else {
        return name(*this, "");
    }
}

inline name name::append_after(unsigned i) const {
    return name(lean_name_append_index_after(to_obj_arg(), lean_unsigned_to_nat(i)));
}

inline optional<pair<name, unsigned>> name::is_subscripted() const {
    optional<pair<name, unsigned>> none;
    if (!is_string()) return none;
    std::string s = get_string().to_std_string();
    auto underscore_pos = s.find_last_of('_');
    if (underscore_pos == std::string::npos) return none;
    std::string::iterator it = s.begin() + underscore_pos + 1;
    if (it == s.end() || *it == '0') return none;
    unsigned idx = 0;
    for (; it != s.end() && '0' <= *it && *it <= '9'; it++)
        idx = 10 * idx + (*it - '0');
    if (it != s.end()) return none;
    name prefix(get_prefix(), string_ref(s.substr(0, underscore_pos)));
    return optional<pair<name, unsigned>>(prefix, idx);
}

inline name name::replace_prefix(name const & prefix, name const & new_prefix) const {
    if (*this == prefix)
        return new_prefix;
    if (is_anonymous())
        return *this;
    name p = get_prefix().replace_prefix(prefix, new_prefix);
    if (p.raw() == raw())
        return *this;
    if (is_string())
        return name(p, get_string());
    else
        return name(p, get_numeral());
}


inline name name::mk_internal_unique_name() {
    unsigned id = lean_name_next_internal_unique_id();
    return name(name(), id);
}

inline name const & name::anonymous() {
    static name anon;
    return anon;
}
}
