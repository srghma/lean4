use leanh_l1::{datatypes::LeanObject, emitted::lean_box::lean_box};

#[inline]
pub unsafe fn lean_level_mk_zero() -> *mut LeanObject {
    lean_box(0)
}
