use crate::{
    datatypes::{LEAN_THUNK_TAG, LeanObject},
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

#[inline]
pub unsafe fn lean_is_thunk(obj: *const LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_THUNK_TAG
}
