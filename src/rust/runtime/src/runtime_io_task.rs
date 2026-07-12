/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::runtime_expr_shared::LeanTaskState;
use crate::*;
use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

pub unsafe fn lean_io_check_canceled() -> bool {
    lean_io_check_canceled()
}

pub unsafe fn lean_io_cancel(t: *mut LeanObject) -> *mut LeanObject {
    lean_io_cancel_core(t);
    lean_box(0)
}

pub unsafe fn lean_io_get_task_state(t: *const LeanObject) -> LeanTaskState {
    lean_io_get_task_state_core(t)
}

pub unsafe fn lean_io_wait(t: *mut LeanObject) -> *mut LeanObject {
    let value = lean_task_get(t);
    lean_inc(value);
    lean_dec(t);
    value
}

pub unsafe fn lean_io_wait_any(task_list: *mut LeanObject) -> *mut LeanObject {
    let task = lean_io_wait_any_core(task_list);
    let value = lean_task_get(task);
    lean_inc(value);
    value
}
