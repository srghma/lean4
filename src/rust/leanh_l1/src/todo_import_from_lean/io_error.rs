use std::ffi::{CStr, CString};

use crate::{
    datatypes::{LeanObject, LeanOptionTag},
    emitted::{
        lean_ctor_get::lean_ctor_get, lean_ctor_get_uint32::lean_ctor_get_uint32,
        lean_dec::lean_dec, lean_mk_string::lean_mk_string, lean_obj_tag::lean_obj_tag,
        lean_option_tag::lean_option_tag,
    },
    r#priv::lean_string_cstr::lean_string_cstr,
};

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LeanIoErrorTag {
    AlreadyExists = 0,
    OtherError = 1,
    ResourceBusy = 2,
    ResourceVanished = 3,
    UnsupportedOperation = 4,
    HardwareFault = 5,
    UnsatisfiedConstraints = 6,
    IllegalOperation = 7,
    ProtocolError = 8,
    TimeExpired = 9,
    Interrupted = 10,
    NoFileOrDirectory = 11,
    InvalidArgument = 12,
    PermissionDenied = 13,
    ResourceExhausted = 14,
    InappropriateType = 15,
    NoSuchThing = 16,
    UnexpectedEof = 17,
    UserError = 18,
}

#[inline]
pub unsafe fn lean_io_error_tag(err: *const LeanObject) -> LeanIoErrorTag {
    match lean_obj_tag(err) {
        0 => LeanIoErrorTag::AlreadyExists,
        1 => LeanIoErrorTag::OtherError,
        2 => LeanIoErrorTag::ResourceBusy,
        3 => LeanIoErrorTag::ResourceVanished,
        4 => LeanIoErrorTag::UnsupportedOperation,
        5 => LeanIoErrorTag::HardwareFault,
        6 => LeanIoErrorTag::UnsatisfiedConstraints,
        7 => LeanIoErrorTag::IllegalOperation,
        8 => LeanIoErrorTag::ProtocolError,
        9 => LeanIoErrorTag::TimeExpired,
        10 => LeanIoErrorTag::Interrupted,
        11 => LeanIoErrorTag::NoFileOrDirectory,
        12 => LeanIoErrorTag::InvalidArgument,
        13 => LeanIoErrorTag::PermissionDenied,
        14 => LeanIoErrorTag::ResourceExhausted,
        15 => LeanIoErrorTag::InappropriateType,
        16 => LeanIoErrorTag::NoSuchThing,
        17 => LeanIoErrorTag::UnexpectedEof,
        18 => LeanIoErrorTag::UserError,
        n => panic!("invalid LeanIoErrorTag {n}"),
    }
}

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

unsafe fn lean_string_to_rust(obj: *const LeanObject) -> String {
    CStr::from_ptr(lean_string_cstr(obj))
        .to_string_lossy()
        .into_owned()
}

unsafe fn lean_option_string_to_rust(obj: *const LeanObject) -> Option<String> {
    match lean_option_tag(obj) {
        LeanOptionTag::None => None,
        LeanOptionTag::Some => Some(lean_string_to_rust(lean_ctor_get(obj, 0))),
    }
}

// Temporary local replacement for exported Lean function
// `Init/System/IOError.lean:lean_io_error_to_string`.
pub unsafe fn lean_io_error_to_string(err: *mut LeanObject) -> *mut LeanObject {
    let msg = match lean_io_error_tag(err) {
        LeanIoErrorTag::AlreadyExists => {
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
        LeanIoErrorTag::OtherError => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(&details, code, None)
        }
        LeanIoErrorTag::ResourceBusy => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_RESOURCE_BUSY, code, Some(&details))
        }
        LeanIoErrorTag::ResourceVanished => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_RESOURCE_VANISHED, code, Some(&details))
        }
        LeanIoErrorTag::UnsupportedOperation => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(
                LEAN_IO_ERROR_TEXT_UNSUPPORTED_OPERATION,
                code,
                Some(&details),
            )
        }
        LeanIoErrorTag::HardwareFault => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            format_other(LEAN_IO_ERROR_TEXT_HARDWARE_FAULT, code, None)
        }
        LeanIoErrorTag::UnsatisfiedConstraints => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            format_other(LEAN_IO_ERROR_TEXT_DIRECTORY_NOT_EMPTY, code, None)
        }
        LeanIoErrorTag::IllegalOperation => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_ILLEGAL_OPERATION, code, Some(&details))
        }
        LeanIoErrorTag::ProtocolError => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_PROTOCOL_ERROR, code, Some(&details))
        }
        LeanIoErrorTag::TimeExpired => {
            let code = lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>()) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 0));
            format_other(LEAN_IO_ERROR_TEXT_TIME_EXPIRED, code, Some(&details))
        }
        LeanIoErrorTag::Interrupted => {
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
        LeanIoErrorTag::NoFileOrDirectory => {
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
        LeanIoErrorTag::InvalidArgument => {
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
        LeanIoErrorTag::PermissionDenied => {
            let filename = lean_option_string_to_rust(lean_ctor_get(err, 0));
            let code =
                lean_ctor_get_uint32(err, (core::mem::size_of::<*mut LeanObject>() * 2) as u32);
            let details = lean_string_to_rust(lean_ctor_get(err, 1));
            match filename {
                Some(filename) => format_fopen(&details, &filename, code, None),
                None => format_other(&details, code, None),
            }
        }
        LeanIoErrorTag::ResourceExhausted => {
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
        LeanIoErrorTag::InappropriateType => {
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
        LeanIoErrorTag::NoSuchThing => {
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
        LeanIoErrorTag::UnexpectedEof => LEAN_IO_ERROR_TEXT_END_OF_FILE.to_owned(),
        LeanIoErrorTag::UserError => lean_string_to_rust(lean_ctor_get(err, 0)),
    };

    lean_dec(err);
    let c_msg = CString::new(msg).expect("IO.Error string must not contain NUL");
    lean_mk_string(c_msg.as_ptr())
}
