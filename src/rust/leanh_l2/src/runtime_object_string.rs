use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

use crate::{
    base::{lean_runtime_validate_utf8, lean_runtime_validate_utf8_one},
    datatypes::{LEAN_STRING_TAG, LeanObject, LeanStringObject},
    runtime_object_rc::lean_alloc_object,
};

pub(crate) unsafe fn lean_alloc_string(
    // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 469 (🔁)
    size: usize,
    capacity: usize,
    len: usize,
) -> *mut LeanObject {
    let byte_size = core::mem::size_of::<LeanStringObject<0>>()
        .checked_add(capacity)
        .expect("string allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanStringObject<0>;
    (*obj).m_header.rc = 1;
    (*obj).m_header.cs_size = 0;
    (*obj).m_header.other = 0;
    (*obj).m_header.tag = LEAN_STRING_TAG;
    (*obj).m_size = size;
    (*obj).m_capacity = capacity;
    (*obj).m_length = len;
    obj as *mut LeanObject
}

// ── string buffer helpers ───────────────────────────────────────────────────

#[inline]
unsafe fn w_string_cstr(o: *mut LeanObject) -> *mut c_char {
    (o as *mut u8).add(size_of::<LeanStringObject<0>>()) as *mut c_char
}
pub unsafe fn lean_mk_string_unchecked(
    // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 365 (🔁)
    s: *const c_char,
    sz: usize,
    len: usize,
) -> *mut LeanObject {
    let rsz = sz + 1;
    let r = lean_alloc_string(rsz, rsz, len);
    core::ptr::copy_nonoverlapping(s, w_string_cstr(r), sz);
    *w_string_cstr(r).add(sz) = 0;
    r
}

pub unsafe fn lean_mk_string_from_bytes(s: *const c_char, sz: usize) -> *mut LeanObject {
    let mut pos: usize = 0;
    let mut i: usize = 0;
    if lean_runtime_validate_utf8(s as *const u8, sz, &mut pos, &mut i) {
        lean_mk_string_unchecked(s, pos, i)
    } else {
        lean_mk_string_lossy_recover(s, sz, pos, i)
    }
}

// ── lossy UTF-8 recovery ─────────────────────────────────────────────────────

unsafe fn lean_mk_string_lossy_recover(
    s: *const c_char,
    sz: usize,
    pos: usize,
    i: usize,
) -> *mut LeanObject {
    let s = s as *const u8;
    let mut out: Vec<u8> = Vec::from(core::slice::from_raw_parts(s, pos));
    let mut char_count = i;
    let mut start = pos;
    let mut p = pos;
    while p < sz {
        let mut next = p;
        if lean_runtime_validate_utf8_one(s, sz, &mut next) {
            char_count += 1;
            p = next;
        } else {
            out.extend_from_slice(core::slice::from_raw_parts(s.add(start), p - start));
            out.extend_from_slice(b"\xef\xbf\xbd"); // U+FFFD
            p += 1;
            while p < sz && (*s.add(p) & 0xc0) == 0x80 {
                p += 1;
            }
            start = p;
            char_count += 1; // count the replacement char
        }
    }
    out.extend_from_slice(core::slice::from_raw_parts(s.add(start), sz - start));
    lean_mk_string_unchecked(out.as_ptr() as *const c_char, out.len(), char_count)
}
