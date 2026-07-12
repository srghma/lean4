use std::ffi::{c_uchar, c_uint};

pub unsafe fn lean_validate_utf8_one(text: *const c_uchar, size: usize, pos: *mut usize) -> bool {
    let i = *pos;
    let byte = *text.add(i) as c_uint;
    if byte & 0x80 == 0 {
        *pos = i + 1;
        return true;
    }

    if byte & 0xe0 == 0xc0 {
        if i + 1 >= size {
            return false;
        }
        let b1 = *text.add(i + 1) as c_uint;
        if b1 & 0xc0 != 0x80 {
            return false;
        }
        let scalar = ((byte & 0x1f) << 6) | (b1 & 0x3f);
        if scalar < 0x80 {
            return false;
        }
        *pos = i + 2;
        return true;
    }

    if byte & 0xf0 == 0xe0 {
        if i + 2 >= size {
            return false;
        }
        let b1 = *text.add(i + 1) as c_uint;
        let b2 = *text.add(i + 2) as c_uint;
        if b1 & 0xc0 != 0x80 || b2 & 0xc0 != 0x80 {
            return false;
        }
        let scalar = ((byte & 0x0f) << 12) | ((b1 & 0x3f) << 6) | (b2 & 0x3f);
        if scalar < 0x800 || (0xD800..=0xDFFF).contains(&scalar) {
            return false;
        }
        *pos = i + 3;
        return true;
    }

    if byte & 0xf8 == 0xf0 {
        if i + 3 >= size {
            return false;
        }
        let b1 = *text.add(i + 1) as c_uint;
        let b2 = *text.add(i + 2) as c_uint;
        let b3 = *text.add(i + 3) as c_uint;
        if b1 & 0xc0 != 0x80 || b2 & 0xc0 != 0x80 || b3 & 0xc0 != 0x80 {
            return false;
        }
        let scalar = ((byte & 0x07) << 18) | ((b1 & 0x3f) << 12) | ((b2 & 0x3f) << 6) | (b3 & 0x3f);
        if !(0x10000..=0x10FFFF).contains(&scalar) {
            return false;
        }
        *pos = i + 4;
        return true;
    }

    false
}
