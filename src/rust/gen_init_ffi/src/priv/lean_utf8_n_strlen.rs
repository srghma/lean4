use leanh_l1::datatypes::Size;
use std::ffi::{c_char, c_uchar};

use crate::r#priv::utf8_size::utf8_size;

pub unsafe fn lean_utf8_n_strlen(text: *const c_char, byte_size: Size) -> Size {
    let mut length = 0;
    let mut offset = 0;
    while offset < byte_size {
        let size = utf8_size(*text.add(offset) as c_uchar);
        length += 1;
        offset += size;
    }
    length
}
