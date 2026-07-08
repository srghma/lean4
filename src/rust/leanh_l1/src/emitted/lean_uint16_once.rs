use crate::datatypes::{LeanObject, Size};

// appended by move_rust_fn_to_leanh_l1.ts from src/rust/leanh_l2/src/in_emit_rust.rs:308-318

#[inline]
pub unsafe fn lean_uint16_once(loc: *mut u16, tok: *mut LeanOnceCell, init: U16InitFn) -> u16 {
    unsafe {
        if (*tok).state.load(Ordering::Acquire) == 1 {
            *loc
        } else {
            run_once(loc, tok, init)
        }
    }
}

