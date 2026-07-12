use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_ctor_get::lean_ctor_get, lean_io_result_is_error::lean_io_result_is_error,
    },
};

pub unsafe fn lean_io_result_get_error(obj: *const LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_error(obj));
    lean_ctor_get(obj, 0)
}
