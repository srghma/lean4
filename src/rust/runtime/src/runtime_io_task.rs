/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_task_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

    unsafe extern "C" {
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

    unsafe fn lean_io_as_task_fn(act: *mut LeanObject, _world: *mut LeanObject) -> *mut LeanObject {
        lean_apply_1(act, lean_io_mk_world())
    }

    unsafe fn lean_io_bind_task_fn(f: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject {
        lean_apply_2(f, a, lean_io_mk_world())
    }

    pub unsafe fn lean_io_check_canceled() -> u8 {
        lean_io_check_canceled_core() as u8
    }

    pub unsafe fn lean_io_cancel(t: *mut LeanObject) -> *mut LeanObject {
        lean_io_cancel_core(t);
        lean_box(0)
    }

    pub unsafe fn lean_io_get_task_state(t: *mut LeanObject) -> u8 {
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

    pub unsafe fn lean_io_as_task(act: *mut LeanObject, prio: *mut LeanObject) -> *mut LeanObject {
        let c = lean_alloc_closure(lean_io_as_task_fn as *mut c_void, 2, 1);
        lean_closure_set(c, 0, act);
        lean_task_spawn_core(c, lean_unbox(prio) as core::ffi::c_uint, true)
    }

    pub unsafe fn lean_io_map_task(
        f: *mut LeanObject,
        t: *mut LeanObject,
        prio: *mut LeanObject,
        sync: u8,
    ) -> *mut LeanObject {
        let c = lean_alloc_closure(lean_io_bind_task_fn as *mut c_void, 2, 1);
        lean_closure_set(c, 0, f);
        lean_task_map_core(c, t, lean_unbox(prio) as core::ffi::c_uint, sync != 0, true)
    }

    pub unsafe fn lean_io_bind_task(
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
