use crate::{
    datatypes::{LeanArrayObject, LeanObject},
    r#priv::lean_is_array::lean_is_array,
};

#[inline]
pub unsafe fn lean_to_array(obj: *const LeanObject) -> *const LeanArrayObject<0> {
    assert!(lean_is_array(obj));
    obj as *const LeanArrayObject<0>
}
