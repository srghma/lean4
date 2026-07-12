use crate::datatypes::{LeanObject, LeanOptionTag};
use crate::r#priv::lean_ptr_tag::lean_ptr_tag;

#[inline]
pub unsafe fn lean_option_tag(obj: *const LeanObject) -> LeanOptionTag {
    match lean_ptr_tag(obj) {
        0 => LeanOptionTag::None,
        1 => LeanOptionTag::Some,
        n => panic!("invalid LeanOptionTag {n}"),
    }
}
