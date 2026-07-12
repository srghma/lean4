use crate::{datatypes::LeanObject, r#priv::lean_usize_to_nat::lean_usize_to_nat};

// Mirrors origin-master-src/include/lean/lean.h:1406-1408 (`lean_unsigned_to_nat`).
#[inline]
pub unsafe fn lean_unsigned_to_nat(value: u32) -> *mut LeanObject {
    lean_usize_to_nat(value as usize)
}
