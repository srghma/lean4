// Generated duplicate-function bucket
// source: Init/Data/ByteArray/Basic.rs:17-19
// exact-text variant: no

use runtime::leanh_extra::*;

pub unsafe fn lean_sarray_size(array: *const LeanObject) -> usize {
    unsafe { (*(array as *const LeanScalarArray<0>)).m_size }
}
