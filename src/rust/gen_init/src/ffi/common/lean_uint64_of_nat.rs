// Generated duplicate-function bucket
// source: Init/Prelude.rs:198-201
// exact-text variant: no

use runtime::leanh_extra::*;
use runtime::leanh_extra as leanh;

#[inline]
pub unsafe fn lean_uint64_of_nat(n: *mut LeanObject) -> u64 {
    unsafe { leanh::lean_uint64_of_nat(n) }
}
