// Generated duplicate-function bucket
// source: Init/Prelude.rs:48-51
// exact-text variant: no

use leanh_l1::datatypes::{LeanObject,LeanScalarArray,LeanStringObject};

#[inline]
pub unsafe fn lean_usize_to_nat(n: usize) -> *mut LeanObject {
    unsafe { leanh::lean_usize_to_nat(n) }
}
