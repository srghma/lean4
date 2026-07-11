use std::ffi::c_char;

use crate::{datatypes::LeanObject, r#priv::lean_to_string::lean_to_string};

pub unsafe fn lean_string_cstr(obj: *const LeanObject) -> *const c_char {
    unsafe { (*lean_to_string(obj)).m_data.as_ptr().cast() }
}
