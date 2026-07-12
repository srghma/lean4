use crate::datatypes::{LeanIoResultTag, LeanObject};
use crate::r#priv::lean_ptr_tag::lean_ptr_tag;

#[inline]
pub unsafe fn lean_io_result_tag(obj: *const LeanObject) -> LeanIoResultTag {
    LeanIoResultTag::from_u8(lean_ptr_tag(obj))
}
