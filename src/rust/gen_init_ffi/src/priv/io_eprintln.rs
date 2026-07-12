use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_dec::lean_dec, lean_io_result_is_ok::lean_io_result_is_ok},
    todo_import_from_lean::lean_io_eprintln::lean_io_eprintln,
};

pub unsafe fn io_eprintln(msg: *mut LeanObject) {
    let result = lean_io_eprintln(msg);
    debug_assert!(lean_io_result_is_ok(result));
    lean_dec(result);
}
