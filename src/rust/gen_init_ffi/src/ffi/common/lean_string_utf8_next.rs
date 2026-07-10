// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:80-82
// exact-text variant: no

use crate::lean_string_utf8_next_fast;
use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};

pub unsafe fn lean_string_utf8_next(s: *mut LeanObject, pos: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_string_utf8_next_fast(s, pos) }
}
