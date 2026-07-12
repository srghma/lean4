use std::ffi::c_char;

use crate::datatypes::{LeanObject, LeanStringObject};

#[inline]
pub unsafe fn w_string_cstr(o: *mut LeanObject) -> *mut c_char {
    // TODO: move to priv bc is used
    (o as *mut u8).add(size_of::<LeanStringObject<0>>()) as *mut c_char
}
