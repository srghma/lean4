/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use leanh::*;
use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};


pub(crate) mod runtime_io_task_impl {

    extern "C" {
        fn lean_io_check_canceled_core() -> bool;
        fn lean_io_cancel_core(t: *mut LeanObject);
        fn lean_io_get_task_state_core(t: *mut LeanObject) -> u8;
        fn lean_io_wait_any_core(task_list: *mut LeanObject) -> *mut LeanObject;
        fn lean_task_spawn_core(
            c: *mut LeanObject,
            prio: core::ffi::c_uint,
            keep_alive: bool,
        ) -> *mut LeanObject;
        fn lean_task_map_core(
            f: *mut LeanObject,
            t: *mut LeanObject,
            prio: core::ffi::c_uint,
            sync: bool,
            keep_alive: bool,
        ) -> *mut LeanObject;
        fn lean_task_bind_core(
            t: *mut LeanObject,
            f: *mut LeanObject,
            prio: core::ffi::c_uint,
            sync: bool,
            keep_alive: bool,
        ) -> *mut LeanObject;
    }

    #[cfg(false)]
    unsafe fn lean_closure_set(c: *mut LeanObject, idx: usize, value: *mut LeanObject) { // duplicate in leanh at line 42 (🔁)
        (*(c as *mut LeanClosureObject))
            .data
            .as_mut_ptr()
            .add(idx)
            .write(value);
    }

    unsafe fn lean_io_as_task_fn(
        act: *mut LeanObject,
        _world: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_apply_1(act, lean_io_mk_world())
    }

    unsafe fn lean_io_bind_task_fn(
        f: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_apply_2(f, a, lean_io_mk_world())
    }

    #[inline]
    pub(crate) unsafe fn lean_io_check_canceled() -> u8 { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:505
        lean_io_check_canceled_core() as u8
    }

    #[inline]
    pub(crate) unsafe fn lean_io_cancel(t: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:511
        lean_io_cancel_core(t);
        lean_box(0)
    }

    #[inline]
    pub(crate) unsafe fn lean_io_get_task_state(t: *mut LeanObject) -> u8 { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:555
        lean_io_get_task_state_core(t)
    }

    #[inline]
    pub(crate) unsafe fn lean_io_wait(t: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:567
        let value = lean_task_get(t);
        lean_inc(value);
        lean_dec(t);
        value
    }

    #[inline]
    pub(crate) unsafe fn lean_io_wait_any(task_list: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:573
        let task = lean_io_wait_any_core(task_list);
        let value = lean_task_get(task);
        lean_inc(value);
        value
    }

    #[inline]
    pub(crate) unsafe fn lean_io_as_task( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:244
        act: *mut LeanObject,
        prio: *mut LeanObject,
    ) -> *mut LeanObject {
        let c = lean_alloc_closure(lean_io_as_task_fn as *mut c_void, 2, 1);
        lean_closure_set(c, 0, act);
        lean_task_spawn_core(c, lean_unbox(prio) as core::ffi::c_uint, true)
    }

    #[inline]
    pub(crate) unsafe fn lean_io_map_task( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:257
        f: *mut LeanObject,
        t: *mut LeanObject,
        prio: *mut LeanObject,
        sync: u8,
    ) -> *mut LeanObject {
        let c = lean_alloc_closure(lean_io_bind_task_fn as *mut c_void, 2, 1);
        lean_closure_set(c, 0, f);
        lean_task_map_core(c, t, lean_unbox(prio) as core::ffi::c_uint, sync != 0, true)
    }

    #[inline]
    pub(crate) unsafe fn lean_io_bind_task( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:271
        t: *mut LeanObject,
        f: *mut LeanObject,
        prio: *mut LeanObject,
        sync: u8,
    ) -> *mut LeanObject {
        let c = lean_alloc_closure(lean_io_bind_task_fn as *mut c_void, 2, 1);
        lean_closure_set(c, 0, f);
        lean_task_bind_core(t, c, lean_unbox(prio) as core::ffi::c_uint, sync != 0, true)
    }
}
