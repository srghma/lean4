/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_memory_impl {
    use crate::*;
    use core::ffi::c_char;
    use std::cell::Cell;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use sysinfo::System;

    const LEAN_CHECK_MEM_THRESHOLD: usize = 200;

    static G_MAX_MEMORY: AtomicUsize = AtomicUsize::new(0);

    thread_local! {
        static G_COUNTER: Cell<usize> = Cell::new(0);
    }

    fn current_rss() -> usize {
        let Ok(pid) = sysinfo::get_current_pid() else {
            return 0;
        };
        let mut system = System::new_all();
        system.refresh_all();
        system
            .process(pid)
            .map(|process| process.memory() as usize)
            .unwrap_or(0)
    }

    fn peak_rss() -> usize {
        current_rss()
    }

    pub fn lean_internal_get_default_max_memory() -> *mut LeanObject {
        const DEFAULT: usize = 0;

        unsafe { lean_box(DEFAULT) }
    }
    pub fn set_max_memory(max: usize) {
        G_MAX_MEMORY.store(max, Ordering::SeqCst);
    }

    pub fn lean_internal_set_max_memory(max: usize) -> *mut LeanObject {
        set_max_memory(max);
        unsafe { lean_box(0) }
    }
    pub fn set_max_memory_megabyte(max: u32) {
        let m = (max as usize).wrapping_mul(1024).wrapping_mul(1024);
        set_max_memory(m);
    }
    pub unsafe fn check_memory(component_name: *const c_char) {
        let max = G_MAX_MEMORY.load(Ordering::SeqCst);
        if max == 0 {
            return;
        }
        let counter = G_COUNTER.with(|cell| {
            let val = cell.get() + 1;
            cell.set(val);
            val
        });
        if counter >= LEAN_CHECK_MEM_THRESHOLD {
            G_COUNTER.with(|cell| cell.set(0));
            let r = peak_rss();
            if r > 0 && r < max {
                return;
            }
            let r = current_rss();
            if r == 0 || r < max {
                return;
            }
            unsafe {
                throw_memory_exception(component_name);
            }
        }
    }
    pub unsafe fn get_allocated_memory() -> usize {
        current_rss()
    }

    /// Returns `true` if memory usage is within configured limits.
    /// This is the Result-returning variant used by the Rust type checker.
    pub unsafe fn lean_memory_within_limit() -> bool {
        let max = G_MAX_MEMORY.load(Ordering::SeqCst);
        if max == 0 {
            return true;
        }
        let counter = G_COUNTER.with(|cell| {
            let val = cell.get() + 1;
            cell.set(val);
            val
        });
        if counter >= LEAN_CHECK_MEM_THRESHOLD {
            G_COUNTER.with(|cell| cell.set(0));
            let r = peak_rss();
            if r > 0 && r < max {
                return true;
            }
            let r = current_rss();
            if r == 0 || r < max {
                return true;
            }
            return false;
        }
        true
    }
}
pub use runtime_memory_impl::*;
