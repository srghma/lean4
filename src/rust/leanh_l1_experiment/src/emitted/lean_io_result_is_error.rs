use crate::datatypes::LeanObject;
use crate::emitted::lean_io_result_tag::lean_io_result_tag;

// Mirrors origin-master-src/include/lean/lean.h:2938 (`lean_io_result_is_error`).
#[inline]
pub unsafe fn lean_io_result_is_error(obj: *const LeanObject) -> bool {
    matches!(
        lean_io_result_tag(obj),
        crate::datatypes::LeanIoResultTag::Error
    )
}
