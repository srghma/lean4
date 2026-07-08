use leanh_l1::{
    datatypes::LeanObject,
    todo_import_from_lean::io_error::LEAN_IO_ERROR_TAG_UNSATISFIED_CONSTRAINTS,
};

use crate::todo_import_from_lean::lean_mk_io_error_helpers::mk_io_error_one_obj;

pub unsafe fn lean_mk_io_error_unsatisfied_constraints(
    os_code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    mk_io_error_one_obj(LEAN_IO_ERROR_TAG_UNSATISFIED_CONSTRAINTS, os_code, details)
}
