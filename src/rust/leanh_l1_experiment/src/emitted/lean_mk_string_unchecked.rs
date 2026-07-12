// from runtime_object_string
use std::ffi::c_char;

use crate::{
    datatypes::LeanObject,
    emitted::{lean_alloc_string::lean_alloc_string, w_string_cstr::w_string_cstr},
};

// ════════════════════════════════════════════════════════════════════════════
// String constructors
// ════════════════════════════════════════════════════════════════════════════

// NOT IN EmitRust; here because it is used in `lean_mk_string`, `lean_mk_string_unchecked`.

// ── string buffer helpers ───────────────────────────────────────────────────

#[inline]
pub unsafe fn lean_mk_string_unchecked(s: *const c_char, sz: usize, len: usize) -> *mut LeanObject {
    // TODO: move to priv bc is used
    let rsz = sz + 1;
    let r = lean_alloc_string(rsz, rsz, len);
    core::ptr::copy_nonoverlapping(s, w_string_cstr(r), sz);
    *w_string_cstr(r).add(sz) = 0;
    r
}
