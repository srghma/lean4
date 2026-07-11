use std::ffi::{CStr, c_char};

use leanh_l1::{
    datatypes::LeanObject, emitted::lean_mk_string_unchecked::lean_mk_string_unchecked,
};

pub unsafe fn lean_mk_ascii_string_unchecked(s: *const c_char) -> *mut LeanObject {
    let len = CStr::from_ptr(s).to_bytes().len();
    lean_mk_string_unchecked(s, len, len)
}
