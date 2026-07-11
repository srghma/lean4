use crate::{
    datatypes::{LeanClosureObject, LeanObject},
    r#priv::lean_is_closure::lean_is_closure,
};

#[inline]
pub unsafe fn lean_to_closure(obj: *const LeanObject) -> *const LeanClosureObject<0> {
    assert!(lean_is_closure(obj));
    obj as *const LeanClosureObject<0>
}
