use crate::{
    datatypes::{LeanCtorObject, LeanObject},
    r#priv::lean_is_ctor::lean_is_ctor,
};

#[inline]
pub unsafe fn lean_to_ctor(obj: *const LeanObject) -> *const LeanCtorObject<0> {
    assert!(lean_is_ctor(obj));
    obj as *const LeanCtorObject<0>
}
