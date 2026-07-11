// Generated duplicate-function bucket
// source: Init/Data/String/Bootstrap.rs:25-27
// source: Init/Data/String/Length.rs:6-8
// exact-text variant: yes

use leanh_l1::{datatypes::LeanObject, r#priv::lean_to_string::lean_to_string};

pub unsafe fn lean_string_length(obj: *const LeanObject) -> usize {
    unsafe { (*lean_to_string(obj)).m_length }
}
