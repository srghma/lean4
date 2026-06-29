// Generated duplicate-function bucket
// source: Init/Data/String/Bootstrap.rs:25-27
// source: Init/Data/String/Length.rs:6-8
// exact-text variant: yes

use crate::leanh::*;
use crate::leanh;

pub unsafe fn lean_string_length(s: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box((*(s as *mut LeanStringObject<0>)).m_length) }
}
