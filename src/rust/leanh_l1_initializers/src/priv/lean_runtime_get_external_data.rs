use leanh_l1::datatypes::{LeanExternalObject, LeanObject};
use std::ffi::c_void;

pub unsafe fn lean_runtime_get_external_data(obj: *const LeanObject) -> *mut c_void {
    (*(obj as *const LeanExternalObject)).m_data
}
