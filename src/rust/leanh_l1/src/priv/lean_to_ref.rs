use crate::{
    datatypes::{LeanObject, LeanRefObject},
    r#priv::lean_is_ref::lean_is_ref,
};

#[inline]
pub unsafe fn lean_to_ref(obj: *const LeanObject) -> *const LeanRefObject {
    assert!(lean_is_ref(obj));
    obj as *const LeanRefObject
}
