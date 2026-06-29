// Generated duplicate-function bucket
// source: Init/Prelude.rs:8-11
// exact-text variant: no

use runtime::leanh_extra::*;
use runtime::leanh_extra as leanh;

#[inline]
pub unsafe fn lean_uint8_to_nat(n: u8) -> *mut LeanObject {
    unsafe { leanh::lean_uint8_to_nat(n) }
}
