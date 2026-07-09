use crate::{datatypes::LeanObject, emitted::lean_ctor_get_float::lean_ctor_get_float};

// Mirrors origin-master-src/include/lean/lean.h:2905-2907 (`lean_unbox_float`).
#[inline]
pub unsafe fn lean_unbox_float(obj: *const LeanObject) -> f64 {
    lean_ctor_get_float(obj, 0)
}
