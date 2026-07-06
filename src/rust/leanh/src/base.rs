use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

use crate::{
    datatypes::{
        LEAN_EXTERNAL_TAG, LeanExternalClass, LeanExternalFinalizeProc, LeanExternalForeachProc,
        LeanExternalObject, LeanObject, Size,
    },
    not_in_emit_rust::lean_alloc_small_object,
};
pub unsafe fn lean_runtime_validate_utf8_one(
    text: *const c_uchar,
    size: Size,
    pos: *mut Size,
) -> bool {
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

pub unsafe fn lean_runtime_validate_utf8(
    text: *const c_uchar,
    size: Size,
    pos: *mut Size,
    chars: *mut Size,
) -> bool {
    while *pos < size {
        if !lean_runtime_validate_utf8_one(text, size, pos) {
            return false;
        }
        *chars += 1;
    }
    true
}

static EXTERNAL_CLASSES: std::sync::Mutex<Vec<usize>> = std::sync::Mutex::new(Vec::new());
unsafe fn lean_external_noop_finalize(_: *mut c_void) {}

unsafe fn lean_external_noop_foreach(_: *mut c_void, _: *mut LeanObject) {}

pub unsafe fn lean_register_external_class(
    finalize: Option<LeanExternalFinalizeProc>,
    foreach: Option<LeanExternalForeachProc>,
) -> *mut LeanExternalClass {
    let class = Box::into_raw(Box::new(LeanExternalClass {
        m_finalize: finalize.unwrap_or(lean_external_noop_finalize),
        m_foreach: foreach.unwrap_or(lean_external_noop_foreach),
    }));
    EXTERNAL_CLASSES.lock().unwrap().push(class as usize);
    class
}

pub unsafe fn lean_runtime_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    let obj = lean_alloc_small_object(core::mem::size_of::<LeanExternalObject>())
        as *mut LeanExternalObject;
    (*obj).m_header.rc = 1;
    (*obj).m_header.other = 0;
    (*obj).m_header.tag = LEAN_EXTERNAL_TAG;
    (*obj).m_class = class;
    (*obj).m_data = data;
    obj as *mut LeanObject
}
