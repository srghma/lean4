use crate::{
    datatypes::{LeanObject, LeanTaskObject},
    r#priv::lean_is_task::lean_is_task,
};

#[inline]
pub unsafe fn lean_to_task(obj: *const LeanObject) -> *const LeanTaskObject {
    assert!(lean_is_task(obj));
    obj as *const LeanTaskObject
}
