use crate::{
    datatypes::LeanObject,
    emitted::{lean_ctor_get::lean_ctor_get, lean_io_result_is_ok::lean_io_result_is_ok},
};

// Mirrors origin-master-src/include/lean/lean.h:2939 (`lean_io_result_get_value`).
#[inline]
pub unsafe fn lean_io_result_get_value(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_ok(obj));
    lean_ctor_get(obj, 0)
}
