use crate::{datatypes::LeanObject, r#priv::lean_ptr_tag::lean_ptr_tag};

// Mirrors origin-master-src/include/lean/lean.h:2937 (`lean_io_result_is_ok`).
#[inline]
pub unsafe fn lean_io_result_is_ok(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == 0
}
