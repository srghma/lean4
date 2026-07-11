// Generated duplicate-function bucket
// source: Init/Prelude.rs:73-76
// exact-text variant: no

use std::ffi::c_char;

use leanh_l1::{datatypes::LeanObject, r#priv::lean_string_cstr::lean_string_cstr};
use leanh_l1_initializers::r#priv::{
    lean_alloc_sarray::lean_alloc_sarray, lean_string_size::lean_string_size,
};

use crate::r#priv::lean_sarray_mut_cptr::lean_sarray_mut_cptr;

#[inline]
pub unsafe fn lean_string_to_utf8(s: *mut LeanObject) -> *mut LeanObject {
    let sz = lean_string_size(s) - 1;
    let r = lean_alloc_sarray(1, sz, sz);
    core::ptr::copy_nonoverlapping(
        lean_string_cstr(s),
        lean_sarray_mut_cptr(r) as *mut c_char,
        sz,
    );
    r
}
