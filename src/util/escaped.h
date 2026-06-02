/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

#include <iostream>

namespace lean {
/**
   \brief Helper class for printing quoted strings.
   For example, the string <tt>foo\"bla</tt> is displayed as <tt>"foo\"bla"</tt>.
*/
class escaped {
    char const * m_str;
    bool         m_trim_nl; // if true -> eliminate '\n' in the end of m_str.
    unsigned     m_indent;
    char const * end() const {
        if (m_str == 0) return 0;
        char const * it = m_str;
        char const * e  = m_str;
        while (*it) {
            if (!m_trim_nl || *it != '\n') {
                ++it;
                e = it;
            } else {
                ++it;
            }
        }
        return e;
    }
public:
    escaped(char const * str, bool trim_nl = false, unsigned indent = 0):m_str(str), m_trim_nl(trim_nl), m_indent(indent) {}
    friend inline std::ostream & operator<<(std::ostream & out, escaped const & s) {
        char const * it = s.m_str;
        char const * e  = s.end();
        for (; it != e; ++it) {
            char c = *it;
            if (c == '"') {
                out << '\\';
            }
            out << c;
            if (c == '\n') {
                for (unsigned i = 0; i < s.m_indent; i++)
                    out << " ";
            }
        }
        return out;
    }
};
}
