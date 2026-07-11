use crate::{
    datatypes::{LeanObject, LeanPromiseObject},
    r#priv::lean_is_promise::lean_is_promise,
};

#[inline]
pub unsafe fn lean_to_promise(obj: *const LeanObject) -> *const LeanPromiseObject {
    assert!(lean_is_promise(obj));
    obj as *const LeanPromiseObject
}
