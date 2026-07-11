use crate::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_scalar_to_int64(a: *const LeanObject) -> i64 {
    assert!(crate::emitted::lean_is_scalar::lean_is_scalar(a));
    crate::emitted::lean_unbox::lean_unbox(a) as i32 as i64
}
