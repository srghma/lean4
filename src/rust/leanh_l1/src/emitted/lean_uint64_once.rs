use core::sync::atomic::Ordering;

use crate::{
    datatypes::{LeanOnceCell, U64InitFn},
    runtime_once::lean_uint64_once_cold,
};

// Mirrors origin-master-src/include/lean/lean.h:3318-3322 (`lean_uint64_once`).
#[inline]
pub unsafe fn lean_uint64_once(loc: *mut u64, tok: *mut LeanOnceCell, init: U64InitFn) -> u64 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_uint64_once_cold(loc, tok, init)
    }
}
