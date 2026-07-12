use core::sync::atomic::Ordering;

use crate::{
    datatypes::{F32InitFn, LeanOnceCell},
    runtime_once::lean_float32_once_cold,
};

// Mirrors origin-master-src/include/lean/lean.h:3336-3340 (`lean_float32_once`).
#[inline]
pub unsafe fn lean_float32_once(loc: *mut f32, tok: *mut LeanOnceCell, init: F32InitFn) -> f32 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_float32_once_cold(loc, tok, init)
    }
}
