use crate::datatypes::{LeanIoResultTag, LeanObject, LeanObjectTag};
use crate::r#priv::lean_ptr_tag::lean_ptr_tag;

#[inline]
pub unsafe fn lean_io_result_tag(obj: *const LeanObject) -> LeanIoResultTag {
    match lean_ptr_tag(obj) {
        LeanObjectTag::Ctor(0) => LeanIoResultTag::Ok,
        LeanObjectTag::Ctor(1) => LeanIoResultTag::Error,
        tag => panic!("invalid LeanIoResultTag {tag:?}"),
    }
}
