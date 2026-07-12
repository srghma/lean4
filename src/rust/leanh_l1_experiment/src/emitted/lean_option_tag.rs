use crate::datatypes::{LeanObject, LeanObjectTag, LeanOptionTag};
use crate::r#priv::lean_ptr_tag::lean_ptr_tag;

#[inline]
pub unsafe fn lean_option_tag(obj: *const LeanObject) -> LeanOptionTag {
    match lean_ptr_tag(obj) {
        LeanObjectTag::Ctor(0) => LeanOptionTag::None,
        LeanObjectTag::Ctor(1) => LeanOptionTag::Some,
        tag => panic!("invalid LeanOptionTag {tag:?}"),
    }
}
