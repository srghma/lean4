use std::ffi::c_uchar;

use crate::r#priv::lean_validate_utf8_one::lean_validate_utf8_one;

// in cpp this is just validate_utf8
pub unsafe fn lean_validate_utf8(
    text: *const c_uchar,
    size: usize,
    pos: *mut usize,
    chars: *mut usize,
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
