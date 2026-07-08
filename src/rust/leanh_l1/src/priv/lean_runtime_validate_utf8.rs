use std::ffi::c_uchar;

use crate::{
    datatypes::Size, r#priv::lean_runtime_validate_utf8_one::lean_runtime_validate_utf8_one,
};

pub unsafe fn lean_runtime_validate_utf8(
    text: *const c_uchar,
    size: Size,
    pos: *mut Size,
    chars: *mut Size,
) -> bool {
    loop {
        if *pos >= size {
            return true;
        }
        if !lean_runtime_validate_utf8_one(text, size, pos) {
            return false;
        }
        *chars += 1;
    }
}
