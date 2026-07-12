use std::ffi::{c_char, c_uint};

pub unsafe fn lean_push_unicode_scalar(dst: *mut c_char, code: c_uint) -> c_uint {
    const TAG_CONT: c_uint = 0b10000000;
    const TAG_TWO_B: c_uint = 0b11000000;
    const TAG_THREE_B: c_uint = 0b11100000;
    const TAG_FOUR_B: c_uint = 0b11110000;

    let bytes = if code < 0x80 {
        [code, 0, 0, 0]
    } else if code < 0x800 {
        [
            ((code >> 6) & 0x1F) | TAG_TWO_B,
            (code & 0x3F) | TAG_CONT,
            0,
            0,
        ]
    } else if code < 0x10000 {
        [
            ((code >> 12) & 0x0F) | TAG_THREE_B,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
            0,
        ]
    } else {
        [
            ((code >> 18) & 0x07) | TAG_FOUR_B,
            ((code >> 12) & 0x3F) | TAG_CONT,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
        ]
    };

    let len = if code < 0x80 {
        1
    } else if code < 0x800 {
        2
    } else if code < 0x10000 {
        3
    } else {
        4
    };
    for (i, byte) in bytes.iter().enumerate().take(len) {
        *dst.add(i) = *byte as c_char;
    }
    len as c_uint
}
