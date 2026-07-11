use std::ffi::c_char;

use crate::{
    datatypes::LeanObject, emitted::lean_mk_string_unchecked::lean_mk_string_unchecked,
    r#priv::lean_validate_utf8_one::lean_validate_utf8_one,
};

// ── lossy UTF-8 recovery ─────────────────────────────────────────────────────
pub unsafe fn lean_mk_string_lossy_recover(
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
        if lean_validate_utf8_one(s, sz, &mut next) {
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
