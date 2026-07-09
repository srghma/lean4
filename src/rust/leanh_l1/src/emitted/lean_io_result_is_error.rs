use crate::{datatypes::LeanObject, r#priv::lean_ptr_tag::lean_ptr_tag};

// Mirrors origin-master-src/include/lean/lean.h:2938 (`lean_io_result_is_error`).
#[inline]
pub unsafe fn lean_io_result_is_error(obj: *const LeanObject) -> bool {
    lean_ptr_tag(obj) == 1
}
