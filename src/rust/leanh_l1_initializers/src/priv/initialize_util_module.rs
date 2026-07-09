use leanh_l1::datatypes::{LeanExternalObject, LeanObject, Size};
use std::ffi::c_void;

pub fn initialize_util_module() {
    unsafe { initialize_util_module_body() }
}
