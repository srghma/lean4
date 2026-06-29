// Generated duplicate-function bucket
// source: Init/Prelude.rs:18-21
// exact-text variant: no

use runtime::leanh_extra::*;
use runtime::leanh_extra as leanh;

#[inline]
pub unsafe fn lean_uint16_to_nat(n: u16) -> *mut LeanObject {
    unsafe { leanh::lean_uint16_to_nat(n) }
}
