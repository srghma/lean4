/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_task_impl {
    use super::*;

    extern "C" {
        fn lean_io_check_canceled_core() -> bool;
        fn lean_io_cancel_core(t: *mut LeanObject);
        fn lean_io_wait_any_core(task_list: *mut LeanObject) -> *mut LeanObject;
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_check_canceled() -> u8 {
        lean_io_check_canceled_core() as u8
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_cancel(t: *mut LeanObject) -> *mut LeanObject {
        lean_io_cancel_core(t);
        lean_box(0)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_get_task_state(t: *mut LeanObject) -> u8 {
        lean_io_get_task_state_core(t)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_wait(t: *mut LeanObject) -> *mut LeanObject {
        let value = lean_task_get(t);
        lean_inc(value);
        lean_dec(t);
        value
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_wait_any(task_list: *mut LeanObject) -> *mut LeanObject {
        let task = lean_io_wait_any_core(task_list);
        let value = lean_task_get(task);
        lean_inc(value);
        value
    }
}
