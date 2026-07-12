use core::sync::atomic::Ordering;

use crate::{
    datatypes::{BoolInitFn, LeanOnceCell},
    runtime_once::lean_bool_once_cold,
};

#[inline]
pub unsafe fn lean_bool_once(loc: *mut bool, tok: *mut LeanOnceCell, init: BoolInitFn) -> bool {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_bool_once_cold(loc, tok, init)
    }
}
