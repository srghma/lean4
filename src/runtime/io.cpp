/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#if defined(LEAN_WINDOWS)
#include <icu.h>
#include <windows.h>
#include <io.h>
#define NOMINMAX // prevent ntdef.h from defining min/max macros
#include <ntdef.h>
#include <bcrypt.h>
#elif defined(__APPLE__)
#include <mach-o/dyld.h>
#include <unistd.h>
#else
#if defined(LEAN_EMSCRIPTEN)
#include <emscripten.h>
#endif
// Linux include files
#include <unistd.h> // NOLINT
#include <sys/mman.h>
#include <sys/file.h>
#ifndef LEAN_EMSCRIPTEN
#include <sys/random.h>
#endif
#endif
#ifndef LEAN_WINDOWS
#include <csignal>
#endif
#include <dirent.h>
#include <fcntl.h>
#include <iostream>
#include <chrono>
#include <sstream>
#include <fstream>
#include <iomanip>
#include <string>
#include <cstdlib>
#include <cctype>
#include <sys/stat.h>
#include "util/io.h"
#include "runtime/alloc.h"
#include "runtime/io.h"
#include "runtime/utf8.h"
#include "runtime/object.h"
#include "runtime/thread.h"

#ifdef _MSC_VER
#define S_ISDIR(mode) ((mode & _S_IFDIR) != 0)
#else
#include <dirent.h>
#endif

namespace lean {

obj_res io_result_mk_error(char const * msg) {
    return io_result_mk_error(lean_mk_io_user_error(mk_string(msg)));
}

obj_res io_result_mk_error(std::string const & msg) {
    return io_result_mk_error(lean_mk_io_user_error(mk_string(msg)));
}

static lean_external_class * g_io_handle_external_class = nullptr;

static void io_handle_finalizer(void * h) {
    // There is no sensible way to handle errors here; in particular, we should
    // not panic as finalizing a handle that already is in an invalid state
    // (broken pipe etc.) should work and not terminate the process. The same
    // decision was made for `std::fs::File` in the Rust stdlib.
    fclose(static_cast<FILE *>(h));
}

static void io_handle_foreach(void * /* mod */, b_obj_arg /* fn */) {
}

lean_object * io_wrap_handle(FILE *hfile) {
    return lean_alloc_external(g_io_handle_external_class, hfile);
}

extern "C" obj_res lean_stream_of_handle(obj_arg h);

static object * g_stream_stdin  = nullptr;
static object * g_stream_stdout = nullptr;
static object * g_stream_stderr = nullptr;
MK_THREAD_LOCAL_GET(object_ref, get_stream_current_stdin,  g_stream_stdin);
MK_THREAD_LOCAL_GET(object_ref, get_stream_current_stdout, g_stream_stdout);
MK_THREAD_LOCAL_GET(object_ref, get_stream_current_stderr, g_stream_stderr);

/* getStdin : BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_stdin() {
    return get_stream_current_stdin().to_obj_arg();
}

/* getStdout : BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_stdout() {
    return get_stream_current_stdout().to_obj_arg();
}

/* getStderr : BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_stderr() {
    return get_stream_current_stderr().to_obj_arg();
}

/* setStdin  : FS.Stream -> BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_set_stdin(obj_arg h) {
    object_ref & x = get_stream_current_stdin();
    object * r = x.steal();
    x = object_ref(h);
    return r;
}

/* setStdout  : FS.Stream -> BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_set_stdout(obj_arg h) {
    object_ref & x = get_stream_current_stdout();
    object * r = x.steal();
    x = object_ref(h);
    return r;
}

/* setStderr  : FS.Stream -> BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_set_stderr(obj_arg h) {
    object_ref & x = get_stream_current_stderr();
    object * r = x.steal();
    x = object_ref(h);
    return r;
}

/* Handle.mk (filename : @& String) (mode : FS.Mode) : IO Handle */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_mk(b_obj_arg filename, uint8 mode) {
    int flags = 0;
#ifdef LEAN_WINDOWS
    // do not translate line endings
    flags |= O_BINARY;
    // do not inherit across process creation
    flags |= O_NOINHERIT;
#else
    // do not inherit across process creation
    flags |= O_CLOEXEC;
#endif
    switch (mode) {
    case 0: flags |= O_RDONLY; break;  // read
    case 1: flags |= O_WRONLY | O_CREAT | O_TRUNC; break;  // write
    case 2: flags |= O_WRONLY | O_CREAT | O_TRUNC | O_EXCL; break;  // writeNew
    case 3: flags |= O_RDWR; break;  // readWrite
    case 4: flags |= O_WRONLY | O_CREAT | O_APPEND; break;  // append
    }
    const char* fname = string_cstr(filename);
    if (strlen(fname) != lean_string_size(filename) - 1) {
        return mk_embedded_nul_error(filename);
    }
    int fd = open(fname, flags, 0666);
    if (fd == -1) {
        return io_result_mk_error(decode_io_error(errno, filename));
    }
    char const * fp_mode;
    switch (mode) {
    case 0: fp_mode = "r"; break;  // read
    case 1: fp_mode = "w"; break;  // write
    case 2: fp_mode = "w"; break;  // writeNew
    case 3: fp_mode = "r+"; break;  // readWrite
    case 4: fp_mode = "a"; break;  // append
    }
    FILE * fp = fdopen(fd, fp_mode);
    if (!fp) {
        return io_result_mk_error(decode_io_error(errno, filename));
    } else {
        return io_result_mk_ok(io_wrap_handle(fp));
    }
}

/* Std.Time.Database.Windows.getNextTransition : @&String -> Int64 -> Bool -> IO (Option (Int64 × TimeZone)) */
extern "C" LEAN_EXPORT obj_res lean_windows_get_next_transition(b_obj_arg timezone_str, uint64_t tm_obj, uint8 default_time) {
#if defined(LEAN_WINDOWS)
    UErrorCode status = U_ZERO_ERROR;
    const char* dst_name_id = lean_string_cstr(timezone_str);

    UChar tzID[256];
    u_strFromUTF8(tzID, sizeof(tzID) / sizeof(tzID[0]), NULL, dst_name_id, lean_string_size(timezone_str) - 1, &status);

    if (U_FAILURE(status)) {
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to read identifier")));
    }

    UCalendar *cal = ucal_open(tzID, -1, NULL, UCAL_GREGORIAN, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to open calendar")));
    }

    int64_t tm = 0;

    if (!default_time) {
        int64_t timestamp_secs = (int64_t)tm_obj;

        ucal_setMillis(cal, timestamp_secs * 1000, &status);
        if (U_FAILURE(status)) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to set calendar time")));
        }

        UDate nextTransition;
        if (!ucal_getTimeZoneTransitionDate(cal, UCAL_TZ_TRANSITION_NEXT, &nextTransition, &status)) {
            ucal_close(cal);
            return io_result_mk_ok(mk_option_none());
        }

        if (U_FAILURE(status)) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to get next transition")));
        }

        tm = (int64_t)(nextTransition / 1000.0);
    }

    int32_t dst_offset = ucal_get(cal, UCAL_DST_OFFSET, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to get dst_offset")));
    }

    int is_dst = dst_offset != 0;

    int32_t tzIDLength = ucal_getTimeZoneDisplayName(cal, is_dst ? UCAL_DST : UCAL_STANDARD, "en_US", tzID, 32, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to timezone identifier")));
    }

    char dst_name[256];
    int32_t dst_name_len;
    u_strToUTF8(dst_name, sizeof(dst_name), &dst_name_len, tzID, tzIDLength, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to convert DST name to UTF-8")));
    }

    UChar display_name[32];
    int32_t display_name_len = ucal_getTimeZoneDisplayName(cal, is_dst ? UCAL_SHORT_DST : UCAL_SHORT_STANDARD, "en_US", display_name, 32, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to read abbreaviation")));
    }

    char display_name_str[256];
    int32_t display_name_str_len;
    u_strToUTF8(display_name_str, sizeof(display_name_str), &display_name_str_len, display_name, display_name_len, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to get abbreviation to cstr")));
    }

    int32_t zone_offset = ucal_get(cal, UCAL_ZONE_OFFSET, &status);
    zone_offset += dst_offset;

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to get zone_offset")));
    }

    ucal_close(cal);

    int offset_seconds = zone_offset / 1000;

    lean_object *lean_tz = lean_alloc_ctor(0, 3, 1);
    lean_ctor_set(lean_tz, 0, lean_int_to_int(offset_seconds));
    lean_ctor_set(lean_tz, 1, lean_mk_string_from_bytes_unchecked(dst_name, dst_name_len));
    lean_ctor_set(lean_tz, 2, lean_mk_string_from_bytes_unchecked(display_name_str, display_name_str_len));
    lean_ctor_set_uint8(lean_tz, sizeof(void*)*3, is_dst);

    lean_object *lean_pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(lean_pair, 0, lean_box_uint64((uint64_t)tm));
    lean_ctor_set(lean_pair, 1, lean_tz);

    return lean_io_result_mk_ok(mk_option_some(lean_pair));
#else
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to get timezone, its windows only.")));
#endif
}

/* Std.Time.Database.Windows.getLocalTimeZoneIdentifierAt : Int64 → IO String */
extern "C" LEAN_EXPORT obj_res lean_get_windows_local_timezone_id_at(uint64_t tm_obj) {
#if defined(LEAN_WINDOWS)
    UErrorCode status = U_ZERO_ERROR;
    UCalendar* cal = ucal_open(NULL, -1, NULL, UCAL_GREGORIAN, &status);

    if (U_FAILURE(status)) {
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to open calendar")));
    }

    int64_t timestamp_secs = (int64_t)tm_obj;
    ucal_setMillis(cal, timestamp_secs * 1000, &status);

    if (U_FAILURE(status)) {
        ucal_close(cal);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to set calendar time")));
    }

    UChar tzId[256];
    int32_t tzIdLength = ucal_getTimeZoneID(cal, tzId, sizeof(tzId) / sizeof(tzId[0]), &status);
    ucal_close(cal);

    if (U_FAILURE(status)) {
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to get timezone ID")));
    }

    char tzIdStr[256];
    u_strToUTF8(tzIdStr, sizeof(tzIdStr), NULL, tzId, tzIdLength, &status);

    if (U_FAILURE(status)) {
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("failed to convert timezone ID to UTF-8")));
    }

    return lean_io_result_mk_ok(lean_mk_ascii_string_unchecked(tzIdStr));
#else
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("timezone retrieval is Windows-only")));
#endif
}

// =======================================
// ST ref primitives


LEAN_EXPORT void initialize_io() {
    g_io_handle_external_class = lean_register_external_class(io_handle_finalizer, io_handle_foreach);
#if defined(LEAN_WINDOWS)
    _setmode(_fileno(stdout), _O_BINARY);
    _setmode(_fileno(stderr), _O_BINARY);
    _setmode(_fileno(stdin), _O_BINARY);
#endif
    g_stream_stdout = lean_stream_of_handle(io_wrap_handle(stdout));
    mark_persistent(g_stream_stdout);
    g_stream_stderr = lean_stream_of_handle(io_wrap_handle(stderr));
    mark_persistent(g_stream_stderr);
    g_stream_stdin  = lean_stream_of_handle(io_wrap_handle(stdin));
    mark_persistent(g_stream_stdin);
#if !defined(LEAN_WINDOWS) && !defined(LEAN_EMSCRIPTEN)
    // We want to handle SIGPIPE ourselves
    lean_always_assert(signal(SIGPIPE, SIG_IGN) != SIG_ERR);
#endif
}

LEAN_EXPORT void finalize_io() {
}
}
