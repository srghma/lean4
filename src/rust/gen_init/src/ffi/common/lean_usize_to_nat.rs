// Generated duplicate-function bucket
// source: Init/Prelude.rs:48-51
// exact-text variant: no

use runtime::leanh_extra::*;
use runtime::leanh_extra as leanh;

#[inline]
pub unsafe fn lean_usize_to_nat(n: usize) -> *mut LeanObject {
    unsafe { leanh::lean_usize_to_nat(n) }
}
