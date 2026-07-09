use leanh_l1::datatypes::LeanObject;

use crate::{
    r#priv::lean_string_size::lean_string_size,
    runtime_object_string::lean_string_eq_cold::lean_string_eq_cold,
};

#[inline]
pub(crate) unsafe fn lean_string_eq(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
    s1 == s2 || (lean_string_size(s1) == lean_string_size(s2) && lean_string_eq_cold(s1, s2))
}
