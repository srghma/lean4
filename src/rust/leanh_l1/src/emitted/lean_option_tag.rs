use crate::datatypes::{LeanObject, LeanOptionTag};
use crate::r#priv::lean_ptr_tag::lean_ptr_tag;

#[inline]
pub unsafe fn lean_option_tag(obj: *const LeanObject) -> LeanOptionTag {
    LeanOptionTag::from_u8(lean_ptr_tag(obj))
}
