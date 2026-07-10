// Generated duplicate-function bucket
// source: Init/Data/String/Bootstrap.rs:25-27
// source: Init/Data/String/Length.rs:6-8
// exact-text variant: yes

use leanh_l1::datatypes::{LeanObject, LeanStringObject};

pub unsafe fn lean_string_length(obj: *const LeanObject) -> usize {
    let string = obj as *const LeanStringObject<0>;
    unsafe { (*string).m_length }
}
