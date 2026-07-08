use core::sync::atomic::Ordering;

use crate::{
    datatypes::{LeanOnceCell, UsizeInitFn},
    runtime_once::lean_usize_once_cold,
};

// Mirrors origin-master-src/include/lean/lean.h:3327-3331 (`lean_usize_once`).
#[inline]
pub unsafe fn lean_usize_once(loc: *mut usize, tok: *mut LeanOnceCell, init: UsizeInitFn) -> usize {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_usize_once_cold(loc, tok, init)
    }
}
