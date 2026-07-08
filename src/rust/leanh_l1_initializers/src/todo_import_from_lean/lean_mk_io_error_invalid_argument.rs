use leanh_l1::{
    datatypes::LeanObject, r#priv::mk_option_none::mk_option_none,
    todo_import_from_lean::io_error::LEAN_IO_ERROR_TAG_INVALID_ARGUMENT,
};

use crate::todo_import_from_lean::lean_mk_io_error_helpers::mk_io_error_two_objs;
pub unsafe fn lean_mk_io_error_invalid_argument(
    os_code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    mk_io_error_two_objs(
        LEAN_IO_ERROR_TAG_INVALID_ARGUMENT,
        mk_option_none(),
        os_code,
        details,
    )
}
