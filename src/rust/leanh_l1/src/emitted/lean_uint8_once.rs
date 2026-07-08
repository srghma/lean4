use core::sync::atomic::Ordering;

use crate::{
    datatypes::{LeanOnceCell, U8InitFn},
    runtime_once::lean_uint8_once_cold,
};

// Mirrors origin-master-src/include/lean/lean.h:3291-3295 (`lean_uint8_once`).
#[inline]
pub unsafe fn lean_uint8_once(loc: *mut u8, tok: *mut LeanOnceCell, init: U8InitFn) -> u8 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_uint8_once_cold(loc, tok, init)
    }
}
