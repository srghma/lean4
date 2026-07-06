use runtime::leanh_extra::*;
// Generated stub file for Lean FFI imports
// Source: src/Std/Time/Zoned/Database/Windows.lean

pub unsafe fn lean_windows_get_next_transition(
    timezone_str: *mut LeanObject,
    tm_obj: u64,
    default_time: u8,
) -> *mut LeanObject {
    #[cfg(target_os = "windows")]
    {
        type UErrorCode = c_int;
        type UDate = f64;
        type UChar = u16;
        type UBool = i8;

        const UCAL_GREGORIAN: c_int = 2;
        const UCAL_TZ_TRANSITION_NEXT: c_int = 1;
        const UCAL_DST_OFFSET: c_int = 16;
        const UCAL_ZONE_OFFSET: c_int = 15;
        const UCAL_STANDARD: c_int = 0;
        const UCAL_DST: c_int = 2;
        const UCAL_SHORT_STANDARD: c_int = 1;
        const UCAL_SHORT_DST: c_int = 3;

        extern "C" {
            fn u_strFromUTF8(
                dest: *mut UChar,
                dest_capacity: c_int,
                p_dest_length: *mut c_int,
                src: *const c_char,
                src_length: c_int,
                p_error_code: *mut UErrorCode,
            ) -> *mut UChar;
            fn u_strToUTF8(
                dest: *mut c_char,
                dest_capacity: c_int,
                p_dest_length: *mut c_int,
                src: *const UChar,
                src_length: c_int,
                p_error_code: *mut UErrorCode,
            ) -> *mut c_char;
            fn ucal_open(
                zone_id: *const UChar,
                len: c_int,
                locale: *const c_char,
                typ: c_int,
                ec: *mut UErrorCode,
            ) -> *mut c_void;
            fn ucal_close(cal: *mut c_void);
            fn ucal_setMillis(cal: *mut c_void, date: UDate, ec: *mut UErrorCode);
            fn ucal_getTimeZoneTransitionDate(
                cal: *const c_void,
                direction: c_int,
                transition_time: *mut UDate,
                ec: *mut UErrorCode,
            ) -> UBool;
            fn ucal_get(cal: *const c_void, field: c_int, ec: *mut UErrorCode) -> c_int;
            fn ucal_getTimeZoneDisplayName(
                cal: *const c_void,
                typ: c_int,
                locale: *const c_char,
                result: *mut UChar,
                result_length: c_int,
                ec: *mut UErrorCode,
            ) -> c_int;
        }

        #[inline]
        unsafe fn icu_failed(status: UErrorCode) -> bool {
            status < 0
        }

        let mut status: UErrorCode = 0;
        let dst_name_id = lean_string_cstr(timezone_str);
        let mut tz_id = [0u16; 256];
        u_strFromUTF8(
            tz_id.as_mut_ptr(),
            tz_id.len() as c_int,
            ptr::null_mut(),
            dst_name_id,
            (lean_string_size(timezone_str) - 1) as c_int,
            &mut status,
        );
        if icu_failed(status) {
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to read identifier".as_ptr()),
            ));
        }

        let cal = ucal_open(tz_id.as_ptr(), -1, ptr::null(), UCAL_GREGORIAN, &mut status);
        if cal.is_null() || icu_failed(status) {
            if !cal.is_null() {
                ucal_close(cal);
            }
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to open calendar".as_ptr()),
            ));
        }

        let mut tm: i64 = 0;
        if default_time == 0 {
            let timestamp_secs = tm_obj as i64;
            ucal_setMillis(cal, (timestamp_secs * 1000) as UDate, &mut status);
            if icu_failed(status) {
                ucal_close(cal);
                return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                    libc::EINVAL as u32,
                    lean_mk_string(c"failed to set calendar time".as_ptr()),
                ));
            }

            let mut next_transition: UDate = 0.0;
            if ucal_getTimeZoneTransitionDate(
                cal,
                UCAL_TZ_TRANSITION_NEXT,
                &mut next_transition,
                &mut status,
            ) == 0
            {
                ucal_close(cal);
                return lean_io_result_mk_ok(lean_box(0));
            }
            if icu_failed(status) {
                ucal_close(cal);
                return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                    libc::EINVAL as u32,
                    lean_mk_string(c"failed to get next transition".as_ptr()),
                ));
            }
            tm = (next_transition / 1000.0) as i64;
        }

        let dst_offset = ucal_get(cal, UCAL_DST_OFFSET, &mut status);
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to get dst_offset".as_ptr()),
            ));
        }
        let is_dst = dst_offset != 0;

        let mut tz_id_name = [0u16; 32];
        let tz_id_len = ucal_getTimeZoneDisplayName(
            cal,
            if is_dst { UCAL_DST } else { UCAL_STANDARD },
            c"en_US".as_ptr(),
            tz_id_name.as_mut_ptr(),
            tz_id_name.len() as c_int,
            &mut status,
        );
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to timezone identifier".as_ptr()),
            ));
        }
        let mut dst_name = [0u8; 256];
        let mut dst_name_len: c_int = 0;
        u_strToUTF8(
            dst_name.as_mut_ptr().cast(),
            dst_name.len() as c_int,
            &mut dst_name_len,
            tz_id_name.as_ptr(),
            tz_id_len,
            &mut status,
        );
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to convert DST name to UTF-8".as_ptr()),
            ));
        }

        let mut display_name = [0u16; 32];
        let display_name_len = ucal_getTimeZoneDisplayName(
            cal,
            if is_dst {
                UCAL_SHORT_DST
            } else {
                UCAL_SHORT_STANDARD
            },
            c"en_US".as_ptr(),
            display_name.as_mut_ptr(),
            display_name.len() as c_int,
            &mut status,
        );
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to read abbreaviation".as_ptr()),
            ));
        }
        let mut display_name_str = [0u8; 256];
        let mut display_name_str_len: c_int = 0;
        u_strToUTF8(
            display_name_str.as_mut_ptr().cast(),
            display_name_str.len() as c_int,
            &mut display_name_str_len,
            display_name.as_ptr(),
            display_name_len,
            &mut status,
        );
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to get abbreviation to cstr".as_ptr()),
            ));
        }

        let zone_offset = ucal_get(cal, UCAL_ZONE_OFFSET, &mut status) + dst_offset;
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to get zone_offset".as_ptr()),
            ));
        }
        ucal_close(cal);

        let offset_seconds = zone_offset / 1000;
        let lean_tz = lean_alloc_ctor(0, 3, 1);
        lean_ctor_set(lean_tz, 0, lean_int64_to_int_rust(offset_seconds as i64));
        lean_ctor_set(
            lean_tz,
            1,
            lean_mk_string_from_bytes_unchecked(dst_name.as_ptr().cast(), dst_name_len as usize),
        );
        lean_ctor_set(
            lean_tz,
            2,
            lean_mk_string_from_bytes_unchecked(
                display_name_str.as_ptr().cast(),
                display_name_str_len as usize,
            ),
        );
        lean_ctor_set_uint8(
            lean_tz,
            core::mem::size_of::<*mut c_void>() * 3,
            is_dst as u8,
        );

        let lean_pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(lean_pair, 0, lean_box_uint64(tm as u64));
        lean_ctor_set(lean_pair, 1, lean_tz);
        lean_io_result_mk_ok(mk_option_some(lean_pair))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = (timezone_str, tm_obj, default_time);
        lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
            libc::EINVAL as u32,
            lean_mk_string(c"failed to get timezone, its windows only.".as_ptr()),
        ))
    }
}

pub unsafe fn lean_get_windows_local_timezone_id_at(tm_obj: u64) -> *mut LeanObject {
    #[cfg(target_os = "windows")]
    {
        type UErrorCode = c_int;
        type UChar = u16;
        type UDate = f64;

        const UCAL_GREGORIAN: c_int = 2;

        extern "C" {
            fn ucal_open(
                zone_id: *const UChar,
                len: c_int,
                locale: *const c_char,
                typ: c_int,
                ec: *mut UErrorCode,
            ) -> *mut c_void;
            fn ucal_close(cal: *mut c_void);
            fn ucal_setMillis(cal: *mut c_void, date: UDate, ec: *mut UErrorCode);
            fn ucal_getTimeZoneID(
                cal: *const c_void,
                result: *mut UChar,
                result_length: c_int,
                ec: *mut UErrorCode,
            ) -> c_int;
            fn u_strToUTF8(
                dest: *mut c_char,
                dest_capacity: c_int,
                p_dest_length: *mut c_int,
                src: *const UChar,
                src_length: c_int,
                p_error_code: *mut UErrorCode,
            ) -> *mut c_char;
        }

        #[inline]
        unsafe fn icu_failed(status: UErrorCode) -> bool {
            status < 0
        }

        let mut status: UErrorCode = 0;
        let cal = ucal_open(ptr::null(), -1, ptr::null(), UCAL_GREGORIAN, &mut status);
        if cal.is_null() || icu_failed(status) {
            if !cal.is_null() {
                ucal_close(cal);
            }
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to open calendar".as_ptr()),
            ));
        }

        ucal_setMillis(cal, (tm_obj as i64 * 1000) as UDate, &mut status);
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to set calendar time".as_ptr()),
            ));
        }

        let mut tz_id = [0u16; 256];
        let tz_id_len =
            ucal_getTimeZoneID(cal, tz_id.as_mut_ptr(), tz_id.len() as c_int, &mut status);
        ucal_close(cal);
        if icu_failed(status) {
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to get timezone ID".as_ptr()),
            ));
        }

        let mut tz_id_str = [0u8; 256];
        let mut tz_id_str_len: c_int = 0;
        u_strToUTF8(
            tz_id_str.as_mut_ptr().cast(),
            tz_id_str.len() as c_int,
            &mut tz_id_str_len,
            tz_id.as_ptr(),
            tz_id_len,
            &mut status,
        );
        if icu_failed(status) {
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to convert timezone ID to UTF-8".as_ptr()),
            ));
        }

        lean_io_result_mk_ok(lean_mk_ascii_string_unchecked(
            core::str::from_utf8_unchecked(core::slice::from_raw_parts(
                tz_id_str.as_ptr(),
                tz_id_str_len as usize,
            )),
        ))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = tm_obj;
        lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
            libc::EINVAL as u32,
            lean_mk_string(c"timezone retrieval is Windows-only".as_ptr()),
        ))
    }
}
