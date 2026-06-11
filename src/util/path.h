/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Gabriel Ebner
*/
#pragma once
#include <string>
#include <vector>
#include <ios>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <cstring>
#include <chrono>
#include <system_error>
#include "runtime/exception.h"
#include "runtime/optional.h"

namespace lean {
class file_not_found_exception : public exception {
    std::string m_fname;
public:
    file_not_found_exception(std::string const & fname):
        exception(sstream() << "file '" << fname << "' not found"),
        m_fname(fname) {}
};

#if !defined(LEAN_EMSCRIPTEN)
inline std::string get_exe_location() {
#if defined(LEAN_WINDOWS)
    HMODULE hModule = GetModuleHandle(NULL);
    char path[MAX_PATH];
    GetModuleFileName(hModule, path, MAX_PATH);
    return std::string(path);
#elif defined(__APPLE__)
    char buf1[PATH_MAX];
    char buf2[PATH_MAX];
    uint32_t bufsize = PATH_MAX;
    if (_NSGetExecutablePath(buf1, &bufsize) != 0)
        throw exception("failed to locate Lean executable location");
    if (!realpath(buf1, buf2))
        throw exception("failed to resolve symbolic links in " + std::string(buf1));
    return std::string(buf2);
#else
    std::error_code ec;
    auto p = std::filesystem::read_symlink("/proc/self/exe", ec);
    if (ec)
        throw exception("failed to locate Lean executable location");
    return p.string();
#endif
}
#endif

inline char const * get_dir_sep();
inline char get_dir_sep_ch();
inline bool is_path_sep(char c);

inline std::string normalize_path(std::string f) {
    for (auto & c : f) {
        if (c == '\\')
            c = get_dir_sep_ch();
    }
    return f;
}

/** \brief Find all files with the given extension recursively. */
inline void find_files(std::string const & base, char const * ext, std::vector<std::string> & files) {
    for (auto const & entry : std::filesystem::recursive_directory_iterator(base)) {
        if (entry.is_regular_file()) {
            auto fn = entry.path().string();
            if (fn.size() > std::strlen(ext) && fn.substr(fn.size() - std::strlen(ext)) == ext)
                files.push_back(fn);
        }
    }
}
inline bool has_file_ext(std::string const & fname, char const * ext) {
    unsigned ext_len = strlen(ext);
    return fname.size() > ext_len && fname.substr(fname.size() - ext_len, ext_len) == ext;
}

inline std::string resolve(std::string const & rel_or_abs, std::string const & base) {
    if (!rel_or_abs.empty() && rel_or_abs[0] == get_dir_sep_ch()) {
        return rel_or_abs;
    } else {
        return base + get_dir_sep_ch() + rel_or_abs;
    }
}
inline std::string dirname(std::string const & fn) {
    auto nfname = normalize_path(fn);
    auto i = nfname.rfind(get_dir_sep_ch());
    if (i == std::string::npos) {
        return ".";
    } else {
        return nfname.substr(0, i);
    }
}
/** \brief Get the file name without the extension. */
inline std::string stem(std::string const & fn) {
    auto nfname = normalize_path(fn);
    auto i = nfname.rfind(get_dir_sep_ch());
    if (i == std::string::npos) {
        i = 0;
    } else {
        i++;
    }
    auto j = nfname.rfind(".");
    if (j == std::string::npos) {
        j = nfname.size();
    }
    return nfname.substr(i, j - i);
}

inline std::string read_file(std::string const & fname, std::ios_base::openmode mode = std::ios_base::in) {
    std::ifstream in(fname, mode);
    if (!in.good()) throw file_not_found_exception(fname);
    std::stringstream buf;
    buf << in.rdbuf();
    return buf.str();
}

inline optional<bool> is_dir(std::string const & fn) {
    std::error_code ec;
    auto s = std::filesystem::status(fn, ec);
    if (ec) return optional<bool>();
    return optional<bool>(std::filesystem::is_directory(s));
}
inline bool is_directory(std::string const & fn) {
    if (auto res = is_dir(fn)) {
        return *res;
    } else {
        return false;
    }
}
inline std::vector<std::string> read_dir(std::string const & dirname) {
    std::vector<std::string> files;
    for (auto const & entry : std::filesystem::directory_iterator(dirname)) {
        auto fn = entry.path().filename().string();
        if (fn == "." || fn == "..") continue;
        files.push_back(entry.path().string());
    }
    return files;
}

inline time_t get_mtime(std::string const & fname) {
    std::error_code ec;
    auto ft = std::filesystem::last_write_time(fname, ec);
    if (ec) return -1;
    auto now_sys = std::chrono::system_clock::now();
    auto now_fs = decltype(ft)::clock::now();
    auto sys_time = std::chrono::time_point_cast<std::chrono::system_clock::duration>(ft - now_fs + now_sys);
    return std::chrono::system_clock::to_time_t(sys_time);
}

inline char const * get_dir_sep() {
#if defined(LEAN_WINDOWS)
    static char g_sep_str[2] = { '\\', 0 };
#else
    static char g_sep_str[2] = { '/', 0 };
#endif
    return g_sep_str;
}
inline char get_dir_sep_ch() { return get_dir_sep()[0]; }
inline bool is_path_sep(char c) { return c == ':'; }
}
