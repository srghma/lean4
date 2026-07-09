use leanh_l1::datatypes::{LeanExternalObject, LeanObject, Size};
use std::ffi::c_void;

pub unsafe fn save_stack_info(main: bool) {
    save_stack_info_export(main);
}
