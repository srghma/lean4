use leanh_l1::{datatypes::LeanObject, todo_import_from_lean::io_error::LeanIoErrorTag};

use crate::todo_import_from_lean::lean_mk_io_error_helpers::mk_io_error_one_obj;

pub unsafe fn lean_mk_io_error_resource_vanished(
    os_code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    mk_io_error_one_obj(LeanIoErrorTag::ResourceVanished, os_code, details)
}
