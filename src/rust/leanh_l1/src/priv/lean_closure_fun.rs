use core::ffi::c_void;

use crate::{datatypes::LeanObject, r#priv::lean_to_closure::lean_to_closure};

#[inline]
pub unsafe fn lean_closure_fun(obj: *const LeanObject) -> *mut c_void {
    (*lean_to_closure(obj)).m_fun
}
