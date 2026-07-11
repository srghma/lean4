use crate::{
    datatypes::{LeanObject, LeanScalarArray},
    r#priv::lean_is_sarray::lean_is_sarray,
};

#[inline]
pub unsafe fn lean_to_sarray(obj: *const LeanObject) -> *const LeanScalarArray<0> {
    assert!(lean_is_sarray(obj));
    obj as *const LeanScalarArray<0>
}
