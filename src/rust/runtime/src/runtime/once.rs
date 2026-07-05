/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use leanh::*;
use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};


pub(crate) type ObjInitFn = unsafe fn() -> *mut LeanObject; // duplicate in leanh at line 12 (🔁)
pub(crate) type U8InitFn = unsafe fn() -> u8; // duplicate in leanh at line 13 (🔁)
pub(crate) type U16InitFn = unsafe fn() -> u16; // duplicate in leanh at line 14 (🔁)
pub(crate) type U32InitFn = unsafe fn() -> u32; // duplicate in leanh at line 15 (🔁)
pub(crate) type U64InitFn = unsafe fn() -> u64; // duplicate in leanh at line 16 (🔁)
pub(crate) type UsizeInitFn = unsafe fn() -> usize; // duplicate in leanh at line 17 (🔁)
pub(crate) type F32InitFn = unsafe fn() -> f32; // duplicate in leanh at line 18 (🔁)
pub(crate) type F64InitFn = unsafe fn() -> f64; // duplicate in leanh at line 19 (🔁)

#[inline]
fn lock_once_cell(lock: &AtomicI32) { // duplicate in leanh at line 22 (🔁)
    while lock
        .compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        #[cfg(feature = "std")]
        std::thread::yield_now();
    }
}

#[inline]
fn unlock_once_cell(lock: &AtomicI32) { // duplicate in leanh at line 33 (🔁)
    lock.store(0, Ordering::Release);
}

#[inline]
unsafe fn run_once<T: Copy>( // duplicate in leanh at line 38 (🔁)
    loc: *mut T,
    tok: *mut LeanOnceCell,
    init: unsafe fn() -> T,
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
pub(crate) unsafe fn lean_obj_once_cold( // duplicate in leanh at line 55 (🔁)
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
pub(crate) unsafe fn lean_obj_once( // duplicate in leanh at line 73 (🔁)
    loc: *mut *mut LeanObject,
    tok: *mut LeanOnceCell,
    init: ObjInitFn,
) -> *mut LeanObject {
    let tok_ref = &*tok;
    if tok_ref.state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_obj_once_cold(loc, tok, init)
    }
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
pub(crate) unsafe fn lean_uint8_once( // duplicate in leanh at line 96 (🔁)
    loc: *mut u8,
    tok: *mut LeanOnceCell,
    init: U8InitFn,
) -> u8 {
    let tok_ref = &*tok;
    if tok_ref.state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_uint8_once_cold(loc, tok, init)
    }
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
pub(crate) unsafe fn lean_uint16_once( // duplicate in leanh at line 119 (🔁)
    loc: *mut u16,
    tok: *mut LeanOnceCell,
    init: U16InitFn,
) -> u16 {
    let tok_ref = &*tok;
    if tok_ref.state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_uint16_once_cold(loc, tok, init)
    }
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
pub(crate) unsafe fn lean_uint32_once( // duplicate in leanh at line 142 (🔁)
    loc: *mut u32,
    tok: *mut LeanOnceCell,
    init: U32InitFn,
) -> u32 {
    let tok_ref = &*tok;
    if tok_ref.state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_uint32_once_cold(loc, tok, init)
    }
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
pub(crate) unsafe fn lean_uint64_once( // duplicate in leanh at line 165 (🔁)
    loc: *mut u64,
    tok: *mut LeanOnceCell,
    init: U64InitFn,
) -> u64 {
    let tok_ref = &*tok;
    if tok_ref.state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_uint64_once_cold(loc, tok, init)
    }
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
pub(crate) unsafe fn lean_usize_once( // duplicate in leanh at line 188 (🔁)
    loc: *mut usize,
    tok: *mut LeanOnceCell,
    init: UsizeInitFn,
) -> usize {
    let tok_ref = &*tok;
    if tok_ref.state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_usize_once_cold(loc, tok, init)
    }
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
pub(crate) unsafe fn lean_float32_once( // duplicate in leanh at line 211 (🔁)
    loc: *mut f32,
    tok: *mut LeanOnceCell,
    init: F32InitFn,
) -> f32 {
    let tok_ref = &*tok;
    if tok_ref.state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_float32_once_cold(loc, tok, init)
    }
}

#[inline]
pub(crate) unsafe fn lean_float_once_cold(
    loc: *mut f64,
    tok: *mut LeanOnceCell,
    init: F64InitFn,
) -> f64 {
    run_once(loc, tok, init)
}

#[inline]
pub(crate) unsafe fn lean_float_once( // duplicate in leanh at line 234 (🔁)
    loc: *mut f64,
    tok: *mut LeanOnceCell,
    init: F64InitFn,
) -> f64 {
    let tok_ref = &*tok;
    if tok_ref.state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_float_once_cold(loc, tok, init)
    }
}
