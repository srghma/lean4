// Generated duplicate-function bucket
// source: Init/Prelude.rs:279-282
// exact-text variant: no

use runtime::leanh_extra as leanh;
use runtime::leanh_extra::*;

#[inline]
pub unsafe fn lean_string_mk(chars: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_string_mk(chars) }
}
