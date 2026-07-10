// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:65-67
// exact-text variant: no

use crate::lean_string_utf8_get_fast;
use leanh_l1::datatypes::{LeanObject,LeanScalarArray,LeanStringObject};

pub unsafe fn lean_string_utf8_get(s: *const LeanObject, pos: *const LeanObject) -> u32 {
    unsafe { lean_string_utf8_get_fast(s, pos) }
}
