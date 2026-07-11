use std::ffi::c_uchar;

pub(crate) fn utf8_size(byte: c_uchar) -> usize {
    if byte & 0x80 == 0 {
        1
    } else if byte & 0xE0 == 0xC0 {
        2
    } else if byte & 0xF0 == 0xE0 {
        3
    } else if byte & 0xF8 == 0xF0 {
        4
    } else if byte & 0xFC == 0xF8 {
        5
    } else if byte & 0xFE == 0xFC {
        6
    } else {
        1
    }
}
