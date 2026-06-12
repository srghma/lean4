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
#include <uv.h>
#include "util/io.h"
#include "runtime/alloc.h"
#include "runtime/io.h"
#include "runtime/utf8.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/option_ref.h"

#ifdef _MSC_VER
#define S_ISDIR(mode) ((mode & _S_IFDIR) != 0)
#else
#include <dirent.h>
#endif

namespace lean {

#ifndef LEAN_RUST_IO_RESULT_SHOW_ERROR
extern "C" LEAN_EXPORT void lean_io_result_show_error(b_obj_arg r) {
    object * err = io_result_get_error(r);
    inc_ref(err);
    object * str = lean_io_error_to_string(err);
    std::cerr << "uncaught exception: " << string_cstr(str) << std::endl;
    dec_ref(str);
}
#endif

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

static FILE * io_get_handle(lean_object * hfile) {
    return static_cast<FILE *>(lean_get_external_data(hfile));
}

extern "C" LEAN_EXPORT obj_res lean_decode_io_error(int errnum, b_lean_obj_arg fname) {
    object * details = mk_string(strerror(errnum));
    // Keep in sync with lean_decode_uv_error below
    switch (errnum) {
    case EINTR:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_interrupted(fname, errnum, details);
    case ELOOP: case ENAMETOOLONG: case EDESTADDRREQ:
    case EBADF: case EDOM: case EINVAL: case EILSEQ:
    case ENOEXEC: case ENOSTR: case ENOTCONN:
    case ENOTSOCK:
        if (fname == nullptr) {
            return lean_mk_io_error_invalid_argument(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_invalid_argument_file(fname, errnum, details);
        }
    case ENOENT:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_no_file_or_directory(fname, errnum, details);
    case EACCES: case EROFS: case ECONNABORTED: case EFBIG:
    case EPERM:
        if (fname == nullptr) {
            return lean_mk_io_error_permission_denied(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_permission_denied_file(fname, errnum, details);
        }
    case EMFILE: case ENFILE: case ENOSPC:
    case E2BIG:  case EAGAIN: case EMLINK:
    case EMSGSIZE: case ENOBUFS: case ENOLCK:
    case ENOMEM: case ENOSR:
        if (fname == nullptr) {
            return lean_mk_io_error_resource_exhausted(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_resource_exhausted_file(fname, errnum, details);
        }
    case EISDIR: case EBADMSG: case ENOTDIR:
        if (fname == nullptr) {
            return lean_mk_io_error_inappropriate_type(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_inappropriate_type_file(fname, errnum, details);
        }
    case ENXIO: case EHOSTUNREACH: case ENETUNREACH:
    case ECHILD: case ECONNREFUSED: case ENODATA:
    case ENOMSG: case ESRCH:
        if (fname == nullptr) {
            return lean_mk_io_error_no_such_thing(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_no_such_thing_file(fname, errnum, details);
        }
    case EEXIST: case EINPROGRESS: case EISCONN:
        if (fname == nullptr) {
            return lean_mk_io_error_already_exists(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_already_exists_file(fname, errnum, details);
        }
    case EIO:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_hardware_fault(errnum, details);
    case ENOTEMPTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsatisfied_constraints(errnum, details);
    case ENOTTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_illegal_operation(errnum, details);
    case ECONNRESET: case EIDRM: case ENETDOWN: case ENETRESET:
    case ENOLINK: case EPIPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_vanished(errnum, details);
    case EPROTO: case EPROTONOSUPPORT: case EPROTOTYPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_protocol_error(errnum, details);
    case ETIME: case ETIMEDOUT:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_time_expired(errnum, details);
    case EADDRINUSE: case EBUSY: case EDEADLK: case ETXTBSY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_busy(errnum, details);
    case EADDRNOTAVAIL: case EAFNOSUPPORT: case ENODEV:
    case ENOPROTOOPT: case ENOSYS: case EOPNOTSUPP:
    case ERANGE: case ESPIPE: case EXDEV:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsupported_operation(errnum, details);
    case EFAULT:
    default:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_other_error(errnum, details);
    }
}

extern "C" LEAN_EXPORT obj_res lean_decode_uv_error(int errnum, b_lean_obj_arg fname) {
    object * details = mk_string(uv_strerror(errnum));
    // Keep in sync with lean_decode_io_error above
    switch (errnum) {
    case UV_EINTR:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_interrupted(fname, errnum, details);
    /* LibUV does not map EDOM, ENOEXEC and ENOSTR as of version 1.48.0 */
    case UV_ELOOP: case UV_ENAMETOOLONG: case UV_EDESTADDRREQ:
    case UV_EBADF: case UV_EINVAL: case UV_EILSEQ:
    case UV_ENOTCONN: case UV_ENOTSOCK:
        if (fname == nullptr) {
            return lean_mk_io_error_invalid_argument(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_invalid_argument_file(fname, errnum, details);
        }
    case UV_ENOENT:
        lean_assert(fname != nullptr);
        inc_ref(fname);
        return lean_mk_io_error_no_file_or_directory(fname, errnum, details);
    case UV_EACCES: case UV_EROFS: case UV_ECONNABORTED: case UV_EFBIG:
    case UV_EPERM:
        if (fname == nullptr) {
            return lean_mk_io_error_permission_denied(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_permission_denied_file(fname, errnum, details);
        }
    /* LibUV does not map ENOLCK and ENOSR as of version 1.48.0 */
    case UV_EMFILE: case UV_ENFILE: case UV_ENOSPC:
    case UV_E2BIG:  case UV_EAGAIN: case UV_EMLINK:
    case UV_EMSGSIZE: case UV_ENOBUFS:
    case UV_ENOMEM:
        if (fname == nullptr) {
            return lean_mk_io_error_resource_exhausted(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_resource_exhausted_file(fname, errnum, details);
        }
    /* LibUV does not map EBADMSG as of version 1.48.0 */
    case UV_EISDIR: case UV_ENOTDIR:
        if (fname == nullptr) {
            return lean_mk_io_error_inappropriate_type(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_inappropriate_type_file(fname, errnum, details);
        }
    /* LibUV does not map ECHILD as of version 1.48.0 */
    case UV_ENXIO: case UV_EHOSTUNREACH: case UV_ENETUNREACH:
    case UV_ECONNREFUSED:
#if UV_VERSION_HEX >= 0x012D00
    case UV_ENODATA:
#endif
    case UV_ESRCH:
        if (fname == nullptr) {
            return lean_mk_io_error_no_such_thing(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_no_such_thing_file(fname, errnum, details);
        }
    /* LibUV does not map EINPROGRESS as of version 1.48.0 */
    case UV_EEXIST: case UV_EISCONN:
        if (fname == nullptr) {
            return lean_mk_io_error_already_exists(errnum, details);
        } else {
            inc_ref(fname);
            return lean_mk_io_error_already_exists_file(fname, errnum, details);
        }
    case UV_EIO:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_hardware_fault(errnum, details);
    case UV_ENOTEMPTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsatisfied_constraints(errnum, details);
    case UV_ENOTTY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_illegal_operation(errnum, details);
    /* LibUV does not map EIDRM, ENETRESET and ENOLINK as of version 1.48.0 */
    case UV_ECONNRESET: case UV_ENETDOWN:
    case UV_EPIPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_vanished(errnum, details);
    case UV_EPROTO: case UV_EPROTONOSUPPORT: case UV_EPROTOTYPE:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_protocol_error(errnum, details);
    /* LibUV does not map ETIME as of version 1.48.0 */
    case UV_ETIMEDOUT:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_time_expired(errnum, details);
    /* LibUV does not map EDEADLK as of version 1.48.0 */
    case UV_EADDRINUSE: case UV_EBUSY: case UV_ETXTBSY:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_resource_busy(errnum, details);
    case UV_EADDRNOTAVAIL: case UV_EAFNOSUPPORT: case UV_ENODEV:
    case UV_ENOPROTOOPT: case UV_ENOSYS: case UV_ENOTSUP:
    case UV_ERANGE: case UV_ESPIPE: case UV_EXDEV:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_unsupported_operation(errnum, details);
    case UV_EFAULT:
    default:
        lean_assert(fname == nullptr);
        return lean_mk_io_error_other_error(errnum, details);
    }
}

#ifndef LEAN_RUST_IO_EMBEDDED_NUL_ERROR
// Used for when you try to convert a string with NUL bytes into a C string
obj_res mk_embedded_nul_error(b_obj_arg str) {
    lean_inc(str);
    return io_result_mk_error(lean_mk_io_error_invalid_argument_file(str, EINVAL, mk_string("string contains NUL bytes")));
}
#endif

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


#ifndef LEAN_RUST_IO_ST_REF
extern "C" LEAN_EXPORT obj_res lean_st_mk_ref(obj_arg a) {
    lean_ref_object * o = (lean_ref_object*)lean_alloc_small_object(sizeof(lean_ref_object));
    lean_set_st_header((lean_object*)o, LeanRef, 0);
    o->m_value = a;
    return (lean_object*)o;
}

static inline atomic<object*> * mt_ref_val_addr(object * o) {
    return reinterpret_cast<atomic<object*> *>(&(lean_to_ref(o)->m_value));
}

/*
  Important: we have added support for initializing global constants
  at program startup. This feature is particularly useful for
  initializing `ST.Ref` values. Any `ST.Ref` value created during
  initialization will be marked as persistent. Thus, to make `ST.Ref`
  API thread-safe, we must treat persistent `ST.Ref` objects created
  during initialization as a multi-threaded object. Then, whenever we store
  a value `val` into a global `ST.Ref`, we have to mark `va`l as a multi-threaded
  object as we do for multi-threaded `ST.Ref`s. It makes sense since
  the global `ST.Ref` may be used to communicate data between threads.
*/
static inline bool ref_maybe_mt(b_obj_arg ref) { return lean_is_mt(ref) || lean_is_persistent(ref); }

extern "C" LEAN_EXPORT obj_res lean_st_ref_get(b_obj_arg ref) {
    if (ref_maybe_mt(ref)) {
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        while (true) {
            /*
              We cannot simply read `val` from the ref and `inc` it like in the `else` branch since someone else could
              write to the ref in between and remove the last owning reference to the object. Instead, we must take
              ownership of the RC token in the ref via `exchange`, duplicate it, then put one RC token back. */
            object * val = val_addr->exchange(nullptr);
            if (val != nullptr) {
                inc(val);
                object * tmp = val_addr->exchange(val);
                if (tmp != nullptr) {
                    /* this may happen if another thread wrote `ref` */
                    dec(tmp);
                }
                return val;
            }
        }
    } else {
        object * val = lean_to_ref(ref)->m_value;
        lean_assert(val != nullptr);
        inc(val);
        return val;
    }
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_take(b_obj_arg ref) {
    if (ref_maybe_mt(ref)) {
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        while (true) {
            object * val = val_addr->exchange(nullptr);
            if (val != nullptr)
                return val;
        }
    } else {
        object * val = lean_to_ref(ref)->m_value;
        lean_assert(val != nullptr);
        lean_to_ref(ref)->m_value = nullptr;
        return val;
    }
}

static_assert(sizeof(atomic<unsigned short>) == sizeof(unsigned short), "`atomic<unsigned short>` and `unsigned short` must have the same size"); // NOLINT

extern "C" LEAN_EXPORT obj_res lean_st_ref_set(b_obj_arg ref, obj_arg a) {
    if (ref_maybe_mt(ref)) {
        /* We must mark `a` as multi-threaded if `ref` is marked as multi-threaded.
           Reason: our runtime relies on the fact that a single-threaded object
           cannot be reached from a multi-thread object. */
        mark_mt(a);
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * old_a = val_addr->exchange(a);
        if (old_a != nullptr)
            dec(old_a);
        return box(0);
    } else {
        if (lean_to_ref(ref)->m_value != nullptr)
            dec(lean_to_ref(ref)->m_value);
        lean_to_ref(ref)->m_value = a;
        return box(0);
    }
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_swap(b_obj_arg ref, obj_arg a) {
    if (ref_maybe_mt(ref)) {
        /* See io_ref_write */
        mark_mt(a);
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        while (true) {
            object * old_a = val_addr->exchange(a);
            if (old_a != nullptr)
                return old_a;
        }
    } else {
        object * old_a = lean_to_ref(ref)->m_value;
        if (old_a == nullptr)
            lean_internal_panic("null reference read");
        lean_to_ref(ref)->m_value = a;
        return old_a;
    }
}

extern "C" LEAN_EXPORT uint8_t lean_st_ref_ptr_eq(b_obj_arg ref1, b_obj_arg ref2) {
    return lean_to_ref(ref1) == lean_to_ref(ref2);
}
#endif // LEAN_RUST_IO_ST_REF

/* {α : Type} (act : BaseIO α) (_ : IO.RealWorld) : α */
static obj_res lean_io_as_task_fn(obj_arg act, obj_arg) {
    object_ref r(apply_1(act, io_mk_world()));
    return object_ref(r.raw(), true).steal();
}

/* asTask {α : Type} (act : BaseIO α) (prio : Nat) : BaseIO (Task α) */
extern "C" LEAN_EXPORT obj_res lean_io_as_task(obj_arg act, obj_arg prio) {
    object * c = lean_alloc_closure((void*)lean_io_as_task_fn, 2, 1);
    lean_closure_set(c, 0, act);
    object * t = lean_task_spawn_core(c, lean_unbox(prio), /* keep_alive */ true);
    return t;
}

/* {α β : Type} (f : α → BaseIO β) (a : α) : β */
static obj_res lean_io_bind_task_fn(obj_arg f, obj_arg a) {
    object_ref r(apply_2(f, a, io_mk_world()));
    return object_ref(r.raw(), true).steal();
}

/*  mapTask (f : α → BaseIO β) (t : Task α) (prio : Nat) (sync : Bool) : BaseIO (Task β) */
extern "C" LEAN_EXPORT obj_res lean_io_map_task(obj_arg f, obj_arg t, obj_arg prio, uint8 sync) {
    object * c = lean_alloc_closure((void*)lean_io_bind_task_fn, 2, 1);
    lean_closure_set(c, 0, f);
    object * t2 = lean_task_map_core(c, t, lean_unbox(prio), sync, /* keep_alive */ true);
    return t2;
}

/*  bindTask (t : Task α) (f : α → BaseIO (Task β)) (prio : Nat) (sync : Bool) : BaseIO (Task β) */
extern "C" LEAN_EXPORT obj_res lean_io_bind_task(obj_arg t, obj_arg f, obj_arg prio, uint8 sync) {
    object * c = lean_alloc_closure((void*)lean_io_bind_task_fn, 2, 1);
    lean_closure_set(c, 0, f);
    object * t2 = lean_task_bind_core(t, c, lean_unbox(prio), sync, /* keep_alive */ true);
    return t2;
}

extern "C" LEAN_EXPORT uint8_t lean_io_check_canceled() {
    return lean_io_check_canceled_core();
}

extern "C" LEAN_EXPORT obj_res lean_io_cancel(b_obj_arg t) {
    lean_io_cancel_core(t);
    return box(0);
}

extern "C" LEAN_EXPORT uint8_t lean_io_get_task_state(b_obj_arg t) {
    return lean_io_get_task_state_core(t);
}

extern "C" LEAN_EXPORT obj_res lean_io_wait(obj_arg t) {
    return lean_task_get_own(t);
}

extern "C" LEAN_EXPORT obj_res lean_io_wait_any(b_obj_arg task_list) {
    object * t = lean_io_wait_any_core(task_list);
    object * v = lean_task_get(t);
    lean_inc(v);
    return v;
}

#ifndef LEAN_RUST_IO_UTIL
extern "C" LEAN_EXPORT obj_res lean_io_exit(uint8_t code) {
    exit(code);
}

extern "C" LEAN_EXPORT obj_res lean_io_force_exit(uint8_t code) {
    std::_Exit((int)code);
}

extern "C" LEAN_EXPORT obj_res lean_runtime_mark_multi_threaded(obj_arg a) {
    lean_mark_mt(a);
    return a;
}

extern "C" LEAN_EXPORT obj_res lean_runtime_mark_persistent(obj_arg a) {
    lean_mark_persistent(a);
    return a;
}

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#include <sanitizer/lsan_interface.h>
#endif
#endif

extern "C" LEAN_EXPORT obj_res lean_runtime_forget(obj_arg o) {
#if defined(__has_feature)
#if __has_feature(address_sanitizer)
    __lsan_ignore_object(o);
#endif
#endif
    return box(0);
}
#endif // LEAN_RUST_IO_UTIL

extern "C" LEAN_EXPORT obj_res lean_option_get_or_block(obj_arg o_opt) {
    option_ref<object_ref> opt = option_ref<object_ref>(o_opt);
    if (opt) {
        return opt.get_val().steal();
    } else {
        lean_panic("PANIC: Promise.result!: promise has been dropped without ever being resolved",
          /* force_stderr */ true);
        // this is only reachable when using non-fatal panics
        while (true) {
            this_thread::sleep_for(std::chrono::seconds::max());
        }
    }
}

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
