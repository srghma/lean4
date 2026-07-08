use crate::{datatypes::LeanObject, emitted::lean_unbox::lean_unbox};

// Mirrors the 64-bit branch of origin-master-src/include/lean/lean.h:2869-2877
// (`lean_unbox_uint32`). This crate only supports 64-bit targets.
#[inline]
pub unsafe fn lean_unbox_uint32(obj: *mut LeanObject) -> u32 {
    lean_unbox(obj) as u32
}
