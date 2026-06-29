// Generated duplicate-function bucket
// source: Init/Prelude.rs:38-41
// exact-text variant: no

use runtime::leanh_extra as leanh;
use runtime::leanh_extra::*;

#[inline]
pub unsafe fn lean_uint64_to_nat(n: u64) -> *mut LeanObject {
    unsafe { leanh::lean_uint64_to_nat(n) }
}
