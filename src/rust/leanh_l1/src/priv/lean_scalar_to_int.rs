use crate::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_scalar_to_int(a: *const LeanObject) -> i32 {
    assert!(crate::emitted::lean_is_scalar::lean_is_scalar(a));
    crate::emitted::lean_unbox::lean_unbox(a) as u32 as i32
}
