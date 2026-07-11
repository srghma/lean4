use std::sync::atomic::{AtomicI32, Ordering};

use crate::{
    datatypes::{BoolInitFn, LeanObject, LeanOnceCell},
    emitted::lean_mark_persistent::lean_mark_persistent,
};

type ObjInitFn = unsafe fn() -> *mut LeanObject;
type U8InitFn = unsafe fn() -> u8;
type U16InitFn = unsafe fn() -> u16;
type U32InitFn = unsafe fn() -> u32;
type U64InitFn = unsafe fn() -> u64;
type UsizeInitFn = unsafe fn() -> usize;
type F32InitFn = unsafe fn() -> f32;
type F64InitFn = unsafe fn() -> f64;

fn lock_once_cell(lock: &AtomicI32) {
    while lock
        .compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        std::thread::yield_now();
    }
}

fn unlock_once_cell(lock: &AtomicI32) {
    lock.store(0, Ordering::Release);
}
unsafe fn run_once<T: Copy>(loc: *mut T, tok: *mut LeanOnceCell, init: unsafe fn() -> T) -> T {
    let tok = &*tok;
    lock_once_cell(&tok.lock);
    if tok.state.load(Ordering::Acquire) != 1 {
        *loc = init();
        tok.state.store(1, Ordering::Release);
    }
    let result = *loc;
    unlock_once_cell(&tok.lock);
    result
}

pub unsafe fn lean_obj_once_cold(
    loc: *mut *mut LeanObject,
    tok: *mut LeanOnceCell,
    init: ObjInitFn,
) -> *mut LeanObject {
    let tok_ref = &*tok;
    lock_once_cell(&tok_ref.lock);
    if tok_ref.state.load(Ordering::Acquire) != 1 {
        *loc = init();
        lean_mark_persistent(*loc);
        tok_ref.state.store(1, Ordering::Release);
    }
    let result = *loc;
    unlock_once_cell(&tok_ref.lock);
    result
}

pub unsafe fn lean_uint8_once_cold(loc: *mut u8, tok: *mut LeanOnceCell, init: U8InitFn) -> u8 {
    run_once(loc, tok, init)
}

pub unsafe fn lean_bool_once_cold(loc: *mut bool, tok: *mut LeanOnceCell, init: BoolInitFn) -> bool {
    run_once(loc, tok, init)
}

pub unsafe fn lean_uint16_once_cold(loc: *mut u16, tok: *mut LeanOnceCell, init: U16InitFn) -> u16 {
    run_once(loc, tok, init)
}

pub unsafe fn lean_uint32_once_cold(loc: *mut u32, tok: *mut LeanOnceCell, init: U32InitFn) -> u32 {
    run_once(loc, tok, init)
}

pub unsafe fn lean_uint64_once_cold(loc: *mut u64, tok: *mut LeanOnceCell, init: U64InitFn) -> u64 {
    run_once(loc, tok, init)
}

pub unsafe fn lean_usize_once_cold(
    loc: *mut usize,
    tok: *mut LeanOnceCell,
    init: UsizeInitFn,
) -> usize {
    run_once(loc, tok, init)
}

pub unsafe fn lean_float32_once_cold(
    loc: *mut f32,
    tok: *mut LeanOnceCell,
    init: F32InitFn,
) -> f32 {
    run_once(loc, tok, init)
}

pub unsafe fn lean_float_once_cold(loc: *mut f64, tok: *mut LeanOnceCell, init: F64InitFn) -> f64 {
    run_once(loc, tok, init)
}
