use crate::{
    datatypes::{LEAN_ARRAY_TAG, LeanObject},
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

#[inline]
pub unsafe fn lean_is_array(obj: *const LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_ARRAY_TAG
}
