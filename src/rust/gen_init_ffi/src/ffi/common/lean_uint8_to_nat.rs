// Generated duplicate-function bucket
// source: Init/Prelude.rs:8-11
// exact-text variant: no

use leanh_l1::datatypes::{LeanObject,LeanScalarArray,LeanStringObject};

#[inline]
pub unsafe fn lean_uint8_to_nat(n: u8) -> *mut LeanObject {
    unsafe { leanh::lean_uint8_to_nat(n) }
}
