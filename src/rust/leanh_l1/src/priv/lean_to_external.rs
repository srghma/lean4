use crate::{
    datatypes::{LeanExternalObject, LeanObject},
    r#priv::lean_is_external::lean_is_external,
};

#[inline]
pub unsafe fn lean_to_external(obj: *const LeanObject) -> *const LeanExternalObject {
    assert!(lean_is_external(obj));
    obj as *const LeanExternalObject
}
