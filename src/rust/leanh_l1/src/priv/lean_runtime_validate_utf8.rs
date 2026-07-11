use std::ffi::c_uchar;

use crate::{
    datatypes::Size, r#priv::lean_validate_utf8_one::lean_validate_utf8_one,
};

// in cpp this is just validate_utf8
pub unsafe fn lean_validate_utf8(
    text: *const c_uchar,
    size: Size,
    pos: *mut Size,
    chars: *mut Size,
) -> bool {
    loop {
        if *pos >= size {
            return true;
        }
        if !lean_validate_utf8_one(text, size, pos) {
            return false;
        }
        *chars += 1;
    }
}
