/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

pub(crate) type ObjInitFn = unsafe extern "C" fn() -> *mut LeanObject;
pub(crate) type U8InitFn = unsafe extern "C" fn() -> u8;
pub(crate) type U16InitFn = unsafe extern "C" fn() -> u16;
pub(crate) type U32InitFn = unsafe extern "C" fn() -> u32;
pub(crate) type U64InitFn = unsafe extern "C" fn() -> u64;
pub(crate) type UsizeInitFn = unsafe extern "C" fn() -> usize;
pub(crate) type F32InitFn = unsafe extern "C" fn() -> f32;
pub(crate) type F64InitFn = unsafe extern "C" fn() -> f64;

#[inline]
fn lock_once_cell(lock: &AtomicI32) {
    while lock
        .compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        #[cfg(feature = "std")]
        std::thread::yield_now();
    }
}

#[inline]
fn unlock_once_cell(lock: &AtomicI32) {
    lock.store(0, Ordering::Release);
}

#[inline]
unsafe fn run_once<T: Copy>(
    loc: *mut T,
    tok: *mut LeanOnceCell,
    init: unsafe extern "C" fn() -> T,
) -> T {
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

#[inline]
pub(crate) unsafe fn lean_obj_once_cold(
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

#[inline]
pub(crate) unsafe fn lean_uint8_once_cold(
    loc: *mut u8,
    tok: *mut LeanOnceCell,
    init: U8InitFn,
) -> u8 {
    run_once(loc, tok, init)
}

#[inline]
pub(crate) unsafe fn lean_uint16_once_cold(
    loc: *mut u16,
    tok: *mut LeanOnceCell,
    init: U16InitFn,
) -> u16 {
    run_once(loc, tok, init)
}

#[inline]
pub(crate) unsafe fn lean_uint32_once_cold(
    loc: *mut u32,
    tok: *mut LeanOnceCell,
    init: U32InitFn,
) -> u32 {
    run_once(loc, tok, init)
}

#[inline]
pub(crate) unsafe fn lean_uint64_once_cold(
    loc: *mut u64,
    tok: *mut LeanOnceCell,
    init: U64InitFn,
) -> u64 {
    run_once(loc, tok, init)
}

#[inline]
pub(crate) unsafe fn lean_usize_once_cold(
    loc: *mut usize,
    tok: *mut LeanOnceCell,
    init: UsizeInitFn,
) -> usize {
    run_once(loc, tok, init)
}

#[inline]
pub(crate) unsafe fn lean_float32_once_cold(
    loc: *mut f32,
    tok: *mut LeanOnceCell,
    init: F32InitFn,
) -> f32 {
    run_once(loc, tok, init)
}

#[inline]
pub(crate) unsafe fn lean_float_once_cold(
    loc: *mut f64,
    tok: *mut LeanOnceCell,
    init: F64InitFn,
) -> f64 {
    run_once(loc, tok, init)
}
