use core::sync::atomic::Ordering;

use crate::{
    datatypes::{F64InitFn, LeanOnceCell},
    runtime_once::lean_float_once_cold,
};

// Mirrors origin-master-src/include/lean/lean.h:3345-3349 (`lean_float_once`).
#[inline]
pub unsafe fn lean_float_once(loc: *mut f64, tok: *mut LeanOnceCell, init: F64InitFn) -> f64 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_float_once_cold(loc, tok, init)
    }
}
