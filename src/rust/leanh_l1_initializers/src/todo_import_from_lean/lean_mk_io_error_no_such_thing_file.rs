use leanh_l1::{datatypes::LeanObject, todo_import_from_lean::io_error::LeanIoErrorTag};

use crate::{
    runtime_object_task::mk_option_some::mk_option_some,
    todo_import_from_lean::lean_mk_io_error_helpers::mk_io_error_two_objs,
};

pub unsafe fn lean_mk_io_error_no_such_thing_file(
    filename: *mut LeanObject,
    os_code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    mk_io_error_two_objs(LeanIoErrorTag::NoSuchThing, mk_option_some(filename), os_code, details)
}
