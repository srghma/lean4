use crate::{
    datatypes::{LeanObject, LeanThunkObject},
    r#priv::lean_is_thunk::lean_is_thunk,
};

#[inline]
pub unsafe fn lean_to_thunk(obj: *const LeanObject) -> *const LeanThunkObject {
    assert!(lean_is_thunk(obj));
    obj as *const LeanThunkObject
}
