// Generated duplicate-function bucket
// source: Init/Prelude.rs:178-181
// exact-text variant: no

use runtime::leanh_extra::*;
use runtime::leanh_extra as leanh;

#[inline]
pub unsafe fn lean_uint32_of_nat(n: *mut LeanObject) -> u32 {
    unsafe { leanh::lean_uint32_of_nat(n) }
}
