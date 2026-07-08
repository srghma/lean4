use crate::{datatypes::LeanObject, emitted::lean_box::lean_box};

const OPTION_NONE_SCALAR: usize = 0;

#[inline(always)]
pub unsafe fn mk_option_none() -> *mut LeanObject {
    unsafe { lean_box(OPTION_NONE_SCALAR) }
}
