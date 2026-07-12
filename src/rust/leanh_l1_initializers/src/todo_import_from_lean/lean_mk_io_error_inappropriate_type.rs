use leanh_l1::{
    datatypes::LeanObject, r#priv::mk_option_none::mk_option_none,
    todo_import_from_lean::io_error::LeanIoErrorTag,
};

use crate::todo_import_from_lean::lean_mk_io_error_helpers::mk_io_error_two_objs;

pub unsafe fn lean_mk_io_error_inappropriate_type(
    os_code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    mk_io_error_two_objs(LeanIoErrorTag::InappropriateType, mk_option_none(), os_code, details)
}
