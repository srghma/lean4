use crate::{
    datatypes::{LeanObject, LeanStringObject},
    r#priv::lean_is_string::lean_is_string,
};

#[inline]
pub unsafe fn lean_to_string(obj: *const LeanObject) -> *const LeanStringObject<0> {
    assert!(lean_is_string(obj));
    obj as *const LeanStringObject<0>
}
