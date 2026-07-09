use leanh_l1::{datatypes::LeanObject, r#priv::lean_string_cstr::lean_string_cstr};

use crate::r#priv::lean_string_size::lean_string_size;

// ════════════════════════════════════════════════════════════════════════════
// String comparisons
// ════════════════════════════════════════════════════════════════════════════

pub unsafe fn lean_string_eq_cold(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
    let sz = lean_string_size(s1);
    core::slice::from_raw_parts(lean_string_cstr(s1) as *const u8, sz)
        == core::slice::from_raw_parts(lean_string_cstr(s2) as *const u8, sz)
}
