use leanh_l1::datatypes::{LeanExternalObject, LeanObject, Size};
use std::ffi::c_void;

pub fn initialize_library_module() {
    // lean_cxx_initialize_num();
    lean_initialize_library_util();
    initialize_time_task();
    initialize_dynlib();
    initialize_ir_interpreter();
}
