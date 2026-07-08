use crate::{datatypes::LeanObject, emitted::lean_ctor_get_float32::lean_ctor_get_float32};

// Mirrors origin-master-src/include/lean/lean.h:2915-2917 (`lean_unbox_float32`).
#[inline]
pub unsafe fn lean_unbox_float32(obj: *mut LeanObject) -> f32 {
    lean_ctor_get_float32(obj, 0)
}
