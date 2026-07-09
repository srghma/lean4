use leanh_l1::datatypes::{LeanExternalObject, LeanObject, Size};
use std::ffi::c_void;

pub fn initialize_library_core_module() {
    unsafe { initialize_library_core_module_body() }
}
