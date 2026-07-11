use crate::{
    datatypes::{LEAN_SCALAR_ARRAY_TAG, LeanObject},
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

#[inline]
pub unsafe fn lean_is_sarray(obj: *const LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_SCALAR_ARRAY_TAG
}
