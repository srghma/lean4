/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
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

}
