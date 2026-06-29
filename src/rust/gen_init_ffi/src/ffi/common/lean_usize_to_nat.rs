// Generated duplicate-function bucket
// source: Init/Prelude.rs:48-51
// exact-text variant: no

use runtime::leanh_extra as leanh;
use runtime::leanh_extra::*;

#[inline]
pub unsafe fn lean_usize_to_nat(n: usize) -> *mut LeanObject {
    unsafe { leanh::lean_usize_to_nat(n) }
}
