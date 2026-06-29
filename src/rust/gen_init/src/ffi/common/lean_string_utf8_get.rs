// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:65-67
// exact-text variant: no

use crate::leanh::*;
use crate::leanh;

pub unsafe fn lean_string_utf8_get(s: *mut LeanObject, pos: *mut LeanObject) -> u32 {
    unsafe { lean_string_utf8_get_fast(s, pos) }
}
