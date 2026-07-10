// Generated duplicate-function bucket
// source: Init/Prelude.rs:198-201
// exact-text variant: no

use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};

#[inline]
pub unsafe fn lean_uint64_of_nat(n: *mut LeanObject) -> u64 {
    unsafe { leanh::lean_uint64_of_nat(n) }
}
