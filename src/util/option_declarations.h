/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <map>
#include <string>
#include <cstring>
#include <cstdlib>
#include "util/macros.h"
#include "util/name_map.h"
#include "util/options.h"
#include "util/io.h"
#include "runtime/array_ref.h"
#include "runtime/pair_ref.h"

namespace lean {
/**
   \brief Datastructure for storing information about available
   configuration options.
*/
class option_declaration {
    name            m_name;
    data_value_kind m_kind;
    std::string     m_default;
    std::string     m_description;
public:
    option_declaration() {}
    option_declaration(name const & n, data_value_kind k, char const * default_val, char const * descr):
        m_name(n), m_kind(k), m_default(default_val), m_description(descr) {}
    data_value_kind kind() const { return m_kind; }
    name const & get_name() const { return m_name; }
    std::string const & get_default_value() const { return m_default; }
    std::string const & get_description() const { return m_description; }
    /** \brief Display value of this option declaration in \c o.
        \remark if \c o does not set this option, then the default value is displayed. */
    void display_value(std::ostream & out, options const & o) const;
};

typedef name_map<option_declaration> option_declarations;
using option_decl = object_ref;

extern "C" object * lean_data_value_to_string(obj_arg d);
extern "C" object * lean_get_option_decls_array();
extern "C" object * lean_register_option(obj_arg name, obj_arg decl);

inline option_declarations get_option_declarations() {
    auto decl_array = get_io_result<array_ref<pair_ref<name, option_decl>>>(lean_get_option_decls_array());
    option_declarations r;
    for (pair_ref<name, option_decl> const & p : decl_array) {
        option_decl decl = p.snd();
        data_value def_val = cnstr_get_ref_t<data_value>(decl, 2);
        string_ref def_str(lean_data_value_to_string(def_val.to_obj_arg()));
        string_ref descr = cnstr_get_ref_t<string_ref>(decl, 3);
        data_value_kind kind = static_cast<data_value_kind>(lean_obj_tag(def_val.raw()));
        option_declaration d(p.fst(), kind, def_str.data(), descr.data());
        r.insert(p.fst(), d);
    }
    return r;
}

inline data_value mk_data_value(data_value_kind k, char const * val) {
    switch (k) {
    case data_value_kind::String:
        return data_value(val);
    case data_value_kind::Bool:
        return strcmp(val, "true") == 0 ? data_value(true) : data_value(false);
    case data_value_kind::Nat:
        return data_value(nat(atoi(val)));
    case data_value_kind::Name:
        return data_value(name(val));
    default:
        lean_unreachable();
    }
}

inline void register_option(name const & n, name const & decl_name, data_value_kind k, char const * default_value, char const * description) {
    object_ref decl = mk_cnstr(0, n, decl_name, mk_data_value(k, default_value), string_ref(description), object_ref(lean_box(0)));
    consume_io_result(lean_register_option(n.to_obj_arg(), decl.to_obj_arg()));
}

#define register_bool_option(n, v, d) register_option(n, {}, data_value_kind::Bool, LEAN_STR(v), d)
#define register_unsigned_option(n, v, d) register_option(n, {}, data_value_kind::Nat, LEAN_STR(v), d)
#define register_string_option(n, v, d) register_option(n, {}, data_value_kind::String, LEAN_STR(v), d)
}
