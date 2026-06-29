// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:80-82
// exact-text variant: no

use runtime::leanh_extra::*;
use crate::ffi::lean_string_utf8_next_fast;
use runtime::leanh_extra as leanh;

pub unsafe fn lean_string_utf8_next(s: *mut LeanObject, pos: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_string_utf8_next_fast(s, pos) }
}
