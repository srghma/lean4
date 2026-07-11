use leanh_l1::{
    datatypes::LeanObject, emitted::lean_mk_string_unchecked::lean_mk_string_unchecked,
};
use std::ffi::c_char;

use crate::r#priv::lean_utf8_n_strlen::lean_utf8_n_strlen;

// ════════════════════════════════════════════════════════════════════════════
// String constructors
// ════════════════════════════════════════════════════════════════════════════

pub unsafe fn lean_mk_string_from_bytes_unchecked(s: *const c_char, sz: usize) -> *mut LeanObject {
    lean_mk_string_unchecked(s, sz, lean_utf8_n_strlen(s, sz))
}
