use core::sync::atomic::Ordering;

use crate::{
    datatypes::{LeanOnceCell, U32InitFn},
    runtime_once::lean_uint32_once_cold,
};

// Mirrors origin-master-src/include/lean/lean.h:3309-3313 (`lean_uint32_once`).
#[inline]
pub unsafe fn lean_uint32_once(loc: *mut u32, tok: *mut LeanOnceCell, init: U32InitFn) -> u32 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_uint32_once_cold(loc, tok, init)
    }
}
