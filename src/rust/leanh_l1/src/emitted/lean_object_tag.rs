use crate::datatypes::{LeanObject, LeanObjectTag};
use crate::r#priv::lean_ptr_tag::lean_ptr_tag;

#[inline]
pub unsafe fn lean_object_tag(obj: *const LeanObject) -> LeanObjectTag {
    lean_ptr_tag(obj)
}
