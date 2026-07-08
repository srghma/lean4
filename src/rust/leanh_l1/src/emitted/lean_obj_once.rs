use core::sync::atomic::Ordering;

use crate::{
    datatypes::{LeanObject, LeanOnceCell, ObjInitFn},
    runtime_once::lean_obj_once_cold,
};

// Mirrors origin-master-src/include/lean/lean.h:3282-3286 (`lean_obj_once`).
#[inline]
pub unsafe fn lean_obj_once(
    loc: *mut *mut LeanObject,
    tok: *mut LeanOnceCell,
    init: ObjInitFn,
) -> *mut LeanObject {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_obj_once_cold(loc, tok, init)
    }
}
