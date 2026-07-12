use leanh_l1::datatypes::LeanObject;

use crate::r#priv::lean_closure_byte_size::lean_closure_byte_size;

#[inline]
pub unsafe fn lean_closure_data_byte_size(obj: *const LeanObject) -> usize {
    unsafe { lean_closure_byte_size(obj) }
}
