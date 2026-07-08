use leanh_l1::{
    datatypes::LeanObject, todo_import_from_lean::io_error::LEAN_IO_ERROR_TAG_ILLEGAL_OPERATION,
};

use crate::todo_import_from_lean::lean_mk_io_error_helpers::mk_io_error_one_obj;

pub unsafe fn lean_mk_io_error_illegal_operation(
    os_code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    mk_io_error_one_obj(LEAN_IO_ERROR_TAG_ILLEGAL_OPERATION, os_code, details)
}
