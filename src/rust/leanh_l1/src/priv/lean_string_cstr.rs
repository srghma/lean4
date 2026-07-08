use std::ffi::c_char;

use crate::datatypes::LeanObject;

pub unsafe fn lean_string_cstr(obj: *mut LeanObject) -> *const c_char {
    (obj as *const u8).add(32) as *const c_char
}
