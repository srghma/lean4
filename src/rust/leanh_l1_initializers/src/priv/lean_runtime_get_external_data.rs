use leanh_l1::{datatypes::LeanObject, r#priv::lean_to_external::lean_to_external};
use std::ffi::c_void;

pub unsafe fn lean_runtime_get_external_data(obj: *const LeanObject) -> *mut c_void {
    unsafe { (*lean_to_external(obj)).m_data }
}
