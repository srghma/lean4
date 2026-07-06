/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_stack_info_impl {
    use crate::{
        runtime_exception::{throw_get_stack_size_failed, throw_stack_space_exception},
        runtime_thread::lthread_get_thread_stack_size,
    };
    use core::ffi::c_char;
    use std::cell::Cell;

    pub unsafe fn get_stack_size_export(main: bool) -> usize {
        get_stack_size(main)
    }
    pub unsafe fn get_used_stack_size_export() -> usize {
        let curr = get_stack_pointer();
        let base = G_STACK_BASE.with(|cell| cell.get());
        base.saturating_sub(curr)
    }
    pub unsafe fn get_available_stack_size_export() -> usize {
        let used = get_used_stack_size_export();
        let size = G_STACK_SIZE.with(|cell| cell.get());
        size.saturating_sub(used)
    }
    pub unsafe fn check_stack_export(component_name: *const c_char) {
        let init = G_STACK_INFO_INIT.with(|cell| cell.get());
        if !init {
            save_stack_info_export(false);
        }
        let curr = get_stack_pointer();
        let threshold = G_STACK_THRESHOLD.with(|cell| cell.get());
        if curr < threshold {
            throw_stack_space_exception(component_name);
        }
    }

    /// Returns `true` if there is enough stack space (no deep recursion detected).
    /// This is the Result-returning variant used by the Rust type checker.
    pub unsafe fn lean_stack_has_space() -> bool {
        let init = G_STACK_INFO_INIT.with(|cell| cell.get());
        if !init {
            save_stack_info_export(false);
        }
        let curr = get_stack_pointer();
        let threshold = G_STACK_THRESHOLD.with(|cell| cell.get());
        curr >= threshold
    }
}
pub use runtime_stack_info_impl::*;
