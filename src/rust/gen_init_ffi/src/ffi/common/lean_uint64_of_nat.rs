// Generated duplicate-function bucket
// source: Init/Prelude.rs:198-201
// exact-text variant: no

use runtime::leanh_extra as leanh;
use runtime::leanh_extra::*;

#[inline]
pub unsafe fn lean_uint64_of_nat(n: *mut LeanObject) -> u64 {
    unsafe { leanh::lean_uint64_of_nat(n) }
}
