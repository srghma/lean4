use core::sync::atomic::Ordering;

use crate::{
    datatypes::{LeanOnceCell, U16InitFn},
    runtime_once::lean_uint16_once_cold,
};

// Mirrors origin-master-src/include/lean/lean.h:3300-3304 (`lean_uint16_once`).
#[inline]
pub unsafe fn lean_uint16_once(loc: *mut u16, tok: *mut LeanOnceCell, init: U16InitFn) -> u16 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_uint16_once_cold(loc, tok, init)
    }
}
