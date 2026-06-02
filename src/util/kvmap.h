/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "runtime/pair_ref.h"
#include "util/name.h"

namespace lean {
extern "C" object * lean_mk_bool_data_value(bool b);
extern "C" uint8 lean_data_value_bool(object * v);
extern "C" uint8 lean_data_value_beq(object * a, object * b);

enum class data_value_kind { String, Bool, Name, Nat, /* Int, Syntax */ };
/*
inductive DataValue
| ofString (v : String)
| ofBool   (v : Bool)
| ofName   (v : Name)
| ofNat    (v : Nat)
| ofInt    (v : Int)
| ofSyntax (v : Syntax)
*/
class data_value : public object_ref {
    data_value(b_obj_arg o, bool b):object_ref(o, b) {}
public:
    explicit data_value(char const * v):object_ref(mk_cnstr(static_cast<unsigned>(data_value_kind::String), mk_string(v))) {}
    explicit data_value(string_ref const & v):object_ref(mk_cnstr(static_cast<unsigned>(data_value_kind::String), v.raw())) { inc(v.raw()); }
    explicit data_value(nat const & v):object_ref(mk_cnstr(static_cast<unsigned>(data_value_kind::Nat), v.raw())) { inc(v.raw()); }
    explicit data_value(bool v):object_ref(lean_mk_bool_data_value(v)) {}
    explicit data_value(name const & v):object_ref(mk_cnstr(static_cast<unsigned>(data_value_kind::Name), v.raw())) { inc(v.raw()); }
    data_value():data_value(false) {}
    data_value(data_value const & other):object_ref(other) {}
    data_value(data_value && other) noexcept:object_ref(std::move(other)) {}
    data_value & operator=(data_value const & other) { object_ref::operator=(other); return *this; }
    data_value & operator=(data_value && other) noexcept { object_ref::operator=(std::move(other)); return *this; }

    data_value_kind kind() const { return static_cast<data_value_kind>(cnstr_tag(raw())); }
    string_ref const & get_string() const { lean_assert(kind() == data_value_kind::String); return static_cast<string_ref const &>(cnstr_get_ref(*this, 0)); }
    nat const & get_nat() const { lean_assert(kind() == data_value_kind::Nat); return static_cast<nat const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { lean_assert(kind() == data_value_kind::Name); return static_cast<name const &>(cnstr_get_ref(*this, 0)); }
    bool get_bool() const {
        lean_assert(kind() == data_value_kind::Bool);
        return lean_data_value_bool(to_obj_arg());
    }

    friend bool operator==(data_value const & a, data_value const & b);
    friend bool operator<(data_value const & a, data_value const & b);
};

inline bool operator==(data_value const & a, data_value const & b) {
    if (a.raw() == b.raw()) return true;
    return lean_data_value_beq(a.to_obj_arg(), b.to_obj_arg());
}
inline bool operator!=(data_value const & a, data_value const & b) { return !(a == b); }
inline bool operator<(data_value const & a, data_value const & b) {
    if (a.kind() != b.kind()) return static_cast<unsigned>(a.kind()) < static_cast<unsigned>(b.kind());
    switch (a.kind()) {
    case data_value_kind::String:   return a.get_string() < b.get_string();
    case data_value_kind::Nat:      return a.get_nat() < b.get_nat();
    case data_value_kind::Bool:     return !a.get_bool() && b.get_bool();
    case data_value_kind::Name:     return a.get_name() < b.get_name();
    }
    return false;
}

typedef pair_ref<name, data_value> kvmap_entry;
typedef list_ref<kvmap_entry> kvmap;

inline optional<data_value> find(kvmap m, name const & k) {
    while (!is_nil(m)) {
        if (head(m).fst() == k)
            return optional<data_value>(head(m).snd());
        m = tail(m);
    }
    return optional<data_value>();
}

inline optional<string_ref> get_string(kvmap const & m, name const & k) {
    optional<data_value> r = find(m, k);
    if (r && r->kind() == data_value_kind::String)
        return optional<string_ref>(r->get_string());
    else
        return optional<string_ref>();
}
inline optional<nat> get_nat(kvmap const & m, name const & k) {
    optional<data_value> r = find(m, k);
    if (r && r->kind() == data_value_kind::Nat)
        return optional<nat>(r->get_nat());
    else
        return optional<nat>();
}
inline optional<bool> get_bool(kvmap const & m, name const & k) {
    optional<data_value> r = find(m, k);
    if (r && r->kind() == data_value_kind::Bool)
        return optional<bool>(r->get_bool());
    else
        return optional<bool>();
}
inline optional<name> get_name(kvmap const & m, name const & k) {
    optional<data_value> r = find(m, k);
    if (r && r->kind() == data_value_kind::Name)
        return optional<name>(r->get_name());
    else
        return optional<name>();
}

inline kvmap set_string(kvmap const & m, name const & k, string_ref const & v) {
    if (is_nil(m))
        return kvmap(kvmap_entry(k, data_value(v)));
    else if (head(m).fst() == k)
        return kvmap(kvmap_entry(k, data_value(v)), tail(m));
    else
        return kvmap(head(m), set_string(tail(m), k, v));
}
inline kvmap set_string(kvmap const & m, name const & k, char const * v) { return set_string(m, k, string_ref(v)); }
inline kvmap set_string(kvmap const & m, name const & k, std::string const & v) { return set_string(m, k, string_ref(v)); }
inline kvmap set_bool(kvmap const & m, name const & k, bool v) {
    if (is_nil(m))
        return kvmap(kvmap_entry(k, data_value(v)));
    else if (head(m).fst() == k)
        return kvmap(kvmap_entry(k, data_value(v)), tail(m));
    else
        return kvmap(head(m), set_bool(tail(m), k, v));
}
inline kvmap set_name(kvmap const & m, name const & k, name const & v) {
    if (is_nil(m))
        return kvmap(kvmap_entry(k, data_value(v)));
    else if (head(m).fst() == k)
        return kvmap(kvmap_entry(k, data_value(v)), tail(m));
    else
        return kvmap(head(m), set_name(tail(m), k, v));
}
inline kvmap set_nat(kvmap const & m, name const & k, nat const & v) {
    if (is_nil(m))
        return kvmap(kvmap_entry(k, data_value(v)));
    else if (head(m).fst() == k)
        return kvmap(kvmap_entry(k, data_value(v)), tail(m));
    else
        return kvmap(head(m), set_nat(tail(m), k, v));
}
inline kvmap set_nat(kvmap const & m, name const & k, unsigned v) { return set_nat(m, k, nat(v)); }
}
