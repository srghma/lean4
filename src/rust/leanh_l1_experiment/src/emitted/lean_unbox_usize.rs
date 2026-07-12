use crate::{datatypes::LeanObject, emitted::lean_ctor_get_usize::lean_ctor_get_usize};

// Mirrors origin-master-src/include/lean/lean.h:2895-2897 (`lean_unbox_usize`).
#[inline]
pub unsafe fn lean_unbox_usize(obj: *const LeanObject) -> usize {
    lean_ctor_get_usize(obj, 0)
}
