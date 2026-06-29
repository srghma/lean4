// Generated duplicate-function bucket
// source: Init/Prelude.rs:38-41
// exact-text variant: no

use crate::leanh::*;
use crate::leanh;

#[inline]
pub unsafe fn lean_uint64_to_nat(n: u64) -> *mut LeanObject {
    unsafe { leanh::lean_uint64_to_nat(n) }
}
