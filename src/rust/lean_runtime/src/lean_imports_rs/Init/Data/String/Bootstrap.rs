use crate::leanh::*;
// Generated stub file for Lean FFI imports
// Source: src/Init/Data/String/Bootstrap.lean

pub fn lean_string_push(_: *mut LeanObject, _: u32) -> *mut LeanObject {
    todo!("Stub for lean_string_push");
}

pub fn lean_string_posof(_: *mut LeanObject, _: u32) -> *mut LeanObject {
    todo!("Stub for lean_string_posof");
}

pub fn lean_string_offsetofpos(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_offsetofpos");
}

pub fn lean_string_utf8_extract(
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
) -> *mut LeanObject {
    todo!("Stub for lean_string_utf8_extract");
}

pub unsafe fn lean_string_length(s: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box((*(s as *mut LeanStringObject<0>)).m_length) }
}

pub fn lean_string_pushn(_: *mut LeanObject, _: u32, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_pushn");
}

pub fn lean_string_append(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_append");
}

pub fn lean_string_utf8_next(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_utf8_next");
}

pub fn lean_string_isempty(_: *mut LeanObject) -> u8 {
    todo!("Stub for lean_string_isempty");
}

pub fn lean_string_foldl(
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
) -> *mut LeanObject {
    todo!("Stub for lean_string_foldl");
}

pub fn lean_string_isprefixof(_: *mut LeanObject, _: *mut LeanObject) -> u8 {
    todo!("Stub for lean_string_isprefixof");
}

pub fn lean_string_any(_: *mut LeanObject, _: *mut LeanObject) -> u8 {
    todo!("Stub for lean_string_any");
}

pub fn lean_string_contains(_: *mut LeanObject, _: u32) -> u8 {
    todo!("Stub for lean_string_contains");
}

pub fn lean_string_utf8_get(_: *mut LeanObject, _: *mut LeanObject) -> u32 {
    todo!("Stub for lean_string_utf8_get");
}

pub fn lean_string_capitalize(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_capitalize");
}

pub unsafe fn lean_string_utf8_at_end(s: *mut LeanObject, pos: *mut LeanObject) -> u8 {
    let pos = unsafe { lean_unbox(pos) };
    let size = unsafe { (*(s as *mut LeanStringObject<0>)).m_size.saturating_sub(1) };
    (pos >= size) as u8
}

pub fn lean_string_nextwhile(
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
) -> *mut LeanObject {
    todo!("Stub for lean_string_nextwhile");
}

pub fn lean_string_trim(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_trim");
}

pub fn lean_string_intercalate(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_intercalate");
}

pub fn lean_string_front(_: *mut LeanObject) -> u32 {
    todo!("Stub for lean_string_front");
}

pub fn lean_string_drop(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_drop");
}

pub fn lean_string_dropright(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_dropright");
}

pub unsafe fn lean_string_get_byte_fast(s: *mut LeanObject, pos: *mut LeanObject) -> u8 {
    let pos = unsafe { lean_unbox(pos) };
    unsafe {
        (*(s as *mut LeanStringObject<0>))
            .m_data
            .as_ptr()
            .add(pos)
            .read()
    }
}

pub fn lean_string_mk(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_mk");
}

pub fn lean_substring_tostring(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_substring_tostring");
}

pub fn lean_substring_drop(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_substring_drop");
}

pub fn lean_substring_front(_: *mut LeanObject) -> u32 {
    todo!("Stub for lean_substring_front");
}

pub fn lean_substring_takewhile(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_substring_takewhile");
}

pub fn lean_substring_extract(
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
) -> *mut LeanObject {
    todo!("Stub for lean_substring_extract");
}

pub fn lean_substring_all(_: *mut LeanObject, _: *mut LeanObject) -> u8 {
    todo!("Stub for lean_substring_all");
}

pub fn lean_substring_beq(_: *mut LeanObject, _: *mut LeanObject) -> u8 {
    todo!("Stub for lean_substring_beq");
}

pub fn lean_substring_isempty(_: *mut LeanObject) -> u8 {
    todo!("Stub for lean_substring_isempty");
}

pub fn lean_substring_get(_: *mut LeanObject, _: *mut LeanObject) -> u32 {
    todo!("Stub for lean_substring_get");
}

pub fn lean_substring_prev(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_substring_prev");
}

pub fn lean_string_pos_sub(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_pos_sub");
}

pub fn lean_string_pos_min(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_string_pos_min");
}
