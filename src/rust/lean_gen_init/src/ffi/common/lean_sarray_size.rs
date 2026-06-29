// Generated duplicate-function bucket
// source: Init/Data/ByteArray/Basic.rs:17-19
// exact-text variant: no

use crate::leanh::*;
use crate::leanh;

pub unsafe fn lean_sarray_size(array: *mut LeanObject) -> usize {
    unsafe { (*(array as *mut LeanScalarArray<0>)).m_size }
}
