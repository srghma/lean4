use leanh_l1::{datatypes::LeanObject, r#priv::lean_string_size::lean_string_size};

use crate::runtime_object_string::lean_string_eq_cold::lean_string_eq_cold;

#[inline]
pub unsafe fn lean_string_eq(s1: *const LeanObject, s2: *const LeanObject) -> bool {
    s1 == s2 || (lean_string_size(s1) == lean_string_size(s2) && lean_string_eq_cold(s1, s2))
}
