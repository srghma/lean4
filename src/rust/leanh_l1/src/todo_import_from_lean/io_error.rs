use std::ffi::{CStr, CString};

use crate::{
    datatypes::LeanObject,
    emitted::{
        lean_ctor_get::lean_ctor_get, lean_ctor_get_uint32::lean_ctor_get_uint32,
        lean_dec::lean_dec, lean_mk_string::lean_mk_string, lean_obj_tag::lean_obj_tag,
    },
    r#priv::{lean_string_cstr::lean_string_cstr, lean_usize_to_nat::lean_usize_to_nat},
};

pub const LEAN_IO_ERROR_TAG_ALREADY_EXISTS: u8 = 0;
pub const LEAN_IO_ERROR_TAG_OTHER_ERROR: u8 = 1;
pub const LEAN_IO_ERROR_TAG_RESOURCE_BUSY: u8 = 2;
pub const LEAN_IO_ERROR_TAG_RESOURCE_VANISHED: u8 = 3;
pub const LEAN_IO_ERROR_TAG_UNSUPPORTED_OPERATION: u8 = 4;
pub const LEAN_IO_ERROR_TAG_HARDWARE_FAULT: u8 = 5;
pub const LEAN_IO_ERROR_TAG_UNSATISFIED_CONSTRAINTS: u8 = 6;
pub const LEAN_IO_ERROR_TAG_ILLEGAL_OPERATION: u8 = 7;
pub const LEAN_IO_ERROR_TAG_PROTOCOL_ERROR: u8 = 8;
pub const LEAN_IO_ERROR_TAG_TIME_EXPIRED: u8 = 9;
pub const LEAN_IO_ERROR_TAG_INTERRUPTED: u8 = 10;
pub const LEAN_IO_ERROR_TAG_NO_FILE_OR_DIRECTORY: u8 = 11;
pub const LEAN_IO_ERROR_TAG_INVALID_ARGUMENT: u8 = 12;
pub const LEAN_IO_ERROR_TAG_PERMISSION_DENIED: u8 = 13;
pub const LEAN_IO_ERROR_TAG_RESOURCE_EXHAUSTED: u8 = 14;
pub const LEAN_IO_ERROR_TAG_INAPPROPRIATE_TYPE: u8 = 15;
pub const LEAN_IO_ERROR_TAG_NO_SUCH_THING: u8 = 16;
pub const LEAN_IO_ERROR_TAG_UNEXPECTED_EOF: u8 = 17;
pub const LEAN_IO_ERROR_TAG_USER_ERROR: u8 = 18;

pub const LEAN_IO_ERROR_TEXT_ALREADY_EXISTS: &str = "already exists";
pub const LEAN_IO_ERROR_TEXT_RESOURCE_BUSY: &str = "resource busy";
pub const LEAN_IO_ERROR_TEXT_RESOURCE_VANISHED: &str = "resource vanished";
pub const LEAN_IO_ERROR_TEXT_UNSUPPORTED_OPERATION: &str = "unsupported operation";
pub const LEAN_IO_ERROR_TEXT_HARDWARE_FAULT: &str = "hardware fault";
pub const LEAN_IO_ERROR_TEXT_DIRECTORY_NOT_EMPTY: &str = "directory not empty";
pub const LEAN_IO_ERROR_TEXT_ILLEGAL_OPERATION: &str = "illegal operation";
pub const LEAN_IO_ERROR_TEXT_PROTOCOL_ERROR: &str = "protocol error";
pub const LEAN_IO_ERROR_TEXT_TIME_EXPIRED: &str = "time expired";
pub const LEAN_IO_ERROR_TEXT_INTERRUPTED_SYSTEM_CALL: &str = "interrupted system call";
pub const LEAN_IO_ERROR_TEXT_NO_FILE_OR_DIRECTORY: &str = "no such file or directory";
pub const LEAN_IO_ERROR_TEXT_INVALID_ARGUMENT: &str = "invalid argument";
pub const LEAN_IO_ERROR_TEXT_RESOURCE_EXHAUSTED: &str = "resource exhausted";
pub const LEAN_IO_ERROR_TEXT_INAPPROPRIATE_TYPE: &str = "inappropriate type";
pub const LEAN_IO_ERROR_TEXT_NO_SUCH_THING: &str = "no such thing";
pub const LEAN_IO_ERROR_TEXT_END_OF_FILE: &str = "end of file";

fn downcase_first(text: &str) -> String {
    let mut chars = text.chars();
    match chars.next() {
        None => String::new(),
        Some(ch) => ch.to_lowercase().chain(chars).collect(),
    }
}

fn format_fopen(gist: &str, file: &str, code: u32, details: Option<&str>) -> String {
    match details {
        Some(details) => format!(
            "{} (error code: {}, {})\n  file: {}",
            downcase_first(gist),
            code,
            downcase_first(details),
            file
        ),
        None => format!(
            "{} (error code: {})\n  file: {}",
            downcase_first(gist),
            code,
            file
        ),
    }
}

fn format_other(gist: &str, code: u32, details: Option<&str>) -> String {
    match details {
        Some(details) => format!(
            "{} (error code: {}, {})",
            downcase_first(gist),
            code,
            downcase_first(details)
        ),
        None => format!("{} (error code: {})", downcase_first(gist), code),
    }
}

unsafe fn lean_string_to_rust(obj: *mut LeanObject) -> String {
    CStr::from_ptr(lean_string_cstr(obj))
        .to_string_lossy()
        .into_owned()
}

unsafe fn lean_option_string_to_rust(obj: *mut LeanObject) -> Option<String> {
    if lean_obj_tag(obj) == 0 {
        None
    } else {
        Some(lean_string_to_rust(lean_ctor_get(obj, 0)))
    }
}

// Temporary local replacement for exported Lean function
// `Init/System/IOError.lean:lean_io_error_to_string`.
pub unsafe fn lean_io_error_to_string(err: *mut LeanObject) -> *mut LeanObject {
    let msg = match lean_obj_tag(err) {
        LEAN_IO_ERROR_TAG_ALREADY_EXISTS => {
            let filename = lean_option_string_to_rust(lean_ctor_get(err, 0));
            let code =
                lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>() * 2) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 1));
            match filename {
                Some(filename) => format_fopen(
                    LEAN_IO_ERROR_TEXT_ALREADY_EXISTS,
                    &filename,
                    code,
                    Some(&details),
                ),
                None => format_other(LEAN_IO_ERROR_TEXT_ALREADY_EXISTS, code, Some(&details)),
            }
        }
        LEAN_IO_ERROR_TAG_OTHER_ERROR => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(&details, code, None)
        }
        LEAN_IO_ERROR_TAG_RESOURCE_BUSY => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_RESOURCE_BUSY, code, Some(&details))
        }
        LEAN_IO_ERROR_TAG_RESOURCE_VANISHED => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_RESOURCE_VANISHED, code, Some(&details))
        }
        LEAN_IO_ERROR_TAG_UNSUPPORTED_OPERATION => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(
                LEAN_IO_ERROR_TEXT_UNSUPPORTED_OPERATION,
                code,
                Some(&details),
            )
        }
        LEAN_IO_ERROR_TAG_HARDWARE_FAULT => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            format_other(LEAN_IO_ERROR_TEXT_HARDWARE_FAULT, code, None)
        }
        LEAN_IO_ERROR_TAG_UNSATISFIED_CONSTRAINTS => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            format_other(LEAN_IO_ERROR_TEXT_DIRECTORY_NOT_EMPTY, code, None)
        }
        LEAN_IO_ERROR_TAG_ILLEGAL_OPERATION => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_ILLEGAL_OPERATION, code, Some(&details))
        }
        LEAN_IO_ERROR_TAG_PROTOCOL_ERROR => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_PROTOCOL_ERROR, code, Some(&details))
        }
        LEAN_IO_ERROR_TAG_TIME_EXPIRED => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_TIME_EXPIRED, code, Some(&details))
        }
        LEAN_IO_ERROR_TAG_INTERRUPTED => {
            let filename = lean_string_to_rust(lean_ctor_get(err, 0));
            let code =
                lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>() * 2) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 1));
            format_fopen(
                LEAN_IO_ERROR_TEXT_INTERRUPTED_SYSTEM_CALL,
                &filename,
                code,
                Some(&details),
            )
        }
        LEAN_IO_ERROR_TAG_NO_FILE_OR_DIRECTORY => {
            let filename = lean_string_to_rust(lean_ctor_get(err, 0));
            let code =
                lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>() * 2) as u32);
            format_fopen(
                LEAN_IO_ERROR_TEXT_NO_FILE_OR_DIRECTORY,
                &filename,
                code,
                None,
            )
        }
        LEAN_IO_ERROR_TAG_INVALID_ARGUMENT => {
            let filename = lean_option_string_to_rust(lean_ctor_get(err, 0));
            let code =
                lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>() * 2) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 1));
            match filename {
                Some(filename) => format_fopen(
                    LEAN_IO_ERROR_TEXT_INVALID_ARGUMENT,
                    &filename,
                    code,
                    Some(&details),
                ),
                None => format_other(LEAN_IO_ERROR_TEXT_INVALID_ARGUMENT, code, Some(&details)),
            }
        }
        LEAN_IO_ERROR_TAG_PERMISSION_DENIED => {
            let filename = lean_option_string_to_rust(lean_ctor_get(err, 0));
            let code =
                lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>() * 2) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 1));
            match filename {
                Some(filename) => format_fopen(&details, &filename, code, None),
                None => format_other(&details, code, None),
            }
        }
        LEAN_IO_ERROR_TAG_RESOURCE_EXHAUSTED => {
            let filename = lean_option_string_to_rust(lean_ctor_get(err, 0));
            let code =
                lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>() * 2) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 1));
            match filename {
                Some(filename) => format_fopen(
                    LEAN_IO_ERROR_TEXT_RESOURCE_EXHAUSTED,
                    &filename,
                    code,
                    Some(&details),
                ),
                None => format_other(LEAN_IO_ERROR_TEXT_RESOURCE_EXHAUSTED, code, Some(&details)),
            }
        }
        LEAN_IO_ERROR_TAG_INAPPROPRIATE_TYPE => {
            let filename = lean_option_string_to_rust(lean_ctor_get(err, 0));
            let code =
                lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>() * 2) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 1));
            match filename {
                Some(filename) => format_fopen(
                    LEAN_IO_ERROR_TEXT_INAPPROPRIATE_TYPE,
                    &filename,
                    code,
                    Some(&details),
                ),
                None => format_other(LEAN_IO_ERROR_TEXT_INAPPROPRIATE_TYPE, code, Some(&details)),
            }
        }
        LEAN_IO_ERROR_TAG_NO_SUCH_THING => {
            let filename = lean_option_string_to_rust(lean_ctor_get(err, 0));
            let code =
                lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>() * 2) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 1));
            match filename {
                Some(filename) => format_fopen(
                    LEAN_IO_ERROR_TEXT_NO_SUCH_THING,
                    &filename,
                    code,
                    Some(&details),
                ),
                None => format_other(LEAN_IO_ERROR_TEXT_NO_SUCH_THING, code, Some(&details)),
            }
        }
        LEAN_IO_ERROR_TAG_UNEXPECTED_EOF => LEAN_IO_ERROR_TEXT_END_OF_FILE.to_owned(),
        LEAN_IO_ERROR_TAG_USER_ERROR => lean_string_to_rust(lean_ctor_get(err, 0)),
        _ => {
            let tag = lean_usize_to_nat(lean_obj_tag(err) as usize);
            let tag_text = lean_string_to_rust(tag);
            lean_dec(tag);
            format!("unknown IO.Error constructor {}", tag_text)
        }
    };

    lean_dec(err);
    let c_msg = CString::new(msg).expect("IO.Error string must not contain NUL");
    lean_mk_string(c_msg.as_ptr())
}
