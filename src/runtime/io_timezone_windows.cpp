/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#if defined(LEAN_WINDOWS)
#include <icu.h>
#include <windows.h>
#include <io.h>
#define NOMINMAX
#include <ntdef.h>
#include "runtime/io.h"
#include "runtime/object.h"

namespace lean {

/* Std.Time.Database.Windows.getNextTransition : @&String -> Int64 -> Bool -> IO (Option (Int64 × TimeZone)) */
extern "C" LEAN_EXPORT obj_res lean_windows_get_next_transition_cxx(b_obj_arg timezone_str, uint64_t tm_obj, uint8 default_time) {
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
}

/* Std.Time.Database.Windows.getLocalTimeZoneIdentifierAt : Int64 → IO String */
extern "C" LEAN_EXPORT obj_res lean_get_windows_local_timezone_id_at_cxx(uint64_t tm_obj) {
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
}

}
#endif
