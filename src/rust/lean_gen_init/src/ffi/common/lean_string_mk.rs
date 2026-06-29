// Generated duplicate-function bucket
// source: Init/Prelude.rs:279-282
// exact-text variant: no

use crate::leanh::*;
use crate::leanh;

#[inline]
pub unsafe fn lean_string_mk(chars: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_string_mk(chars) }
}
