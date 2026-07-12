use crate::datatypes::{LeanIoResultTag, LeanObject};
use crate::r#priv::lean_ptr_tag::lean_ptr_tag;

#[inline]
pub unsafe fn lean_io_result_tag(obj: *const LeanObject) -> LeanIoResultTag {
    match lean_ptr_tag(obj) {
        0 => LeanIoResultTag::Ok,
        1 => LeanIoResultTag::Error,
        n => panic!("invalid LeanIoResultTag {n}"),
    }
}
