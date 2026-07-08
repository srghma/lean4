use crate::{datatypes::LeanObject, emitted::lean_box::lean_box};

#[inline(always)]
pub unsafe fn mk_option_none() -> *mut LeanObject {
    unsafe { lean_box(0) }
}
