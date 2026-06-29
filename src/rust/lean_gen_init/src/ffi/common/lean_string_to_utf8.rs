// Generated duplicate-function bucket
// source: Init/Prelude.rs:73-76
// exact-text variant: no

use crate::leanh::*;
use crate::leanh;

#[inline]
pub unsafe fn lean_string_to_utf8(s: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_string_to_utf8(s) }
}
