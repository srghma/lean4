use crate::datatypes::LeanObject;
use crate::emitted::lean_io_result_tag::lean_io_result_tag;

// Mirrors origin-master-src/include/lean/lean.h:2937 (`lean_io_result_is_ok`).
#[inline]
pub unsafe fn lean_io_result_is_ok(obj: *const LeanObject) -> bool {
    matches!(
        lean_io_result_tag(obj),
        crate::datatypes::LeanIoResultTag::Ok
    )
}
