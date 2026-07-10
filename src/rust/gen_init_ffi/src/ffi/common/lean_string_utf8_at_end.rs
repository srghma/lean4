// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:88-92
// source: Init/Data/String/Bootstrap.rs:73-77
// exact-text variant: yes

use leanh_l1::datatypes::{LeanObject,LeanScalarArray,LeanStringObject};

pub unsafe fn lean_string_utf8_at_end(s: *mut LeanObject, pos: *mut LeanObject) -> u8 {
    let pos = unsafe { lean_unbox(pos) };
    let size = unsafe { (*(s as *mut LeanStringObject<0>)).m_size.saturating_sub(1) };
    (pos >= size) as u8
}
