use crate::{datatypes::LeanObject, emitted::lean_ctor_get_uint64::lean_ctor_get_uint64};

// Mirrors origin-master-src/include/lean/lean.h:2885-2887 (`lean_unbox_uint64`).
#[inline]
pub unsafe fn lean_unbox_uint64(obj: *const LeanObject) -> u64 {
    lean_ctor_get_uint64(obj, 0)
}
