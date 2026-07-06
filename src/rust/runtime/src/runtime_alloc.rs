/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_alloc_impl {
    use super::*;
    use core::cell::Cell;
    use core::ffi::c_void;

    extern "C" {
        fn mi_malloc_small(sz: usize) -> *mut c_void;
        fn mi_free(ptr: *mut c_void);
    }

    thread_local! {
        static G_HEARTBEAT: Cell<u64> = const { Cell::new(0) };
    }

    pub fn initialize_alloc() {}

    pub fn finalize_alloc() {}

    pub unsafe fn lean_alloc_small(sz: u32, _slot_idx: u32) -> *mut c_void {
        let mem = mi_malloc_small(sz as usize);
        if mem.is_null() {
            lean_internal_panic_out_of_memory();
        }
        (*(mem as *mut LeanObject)).cs_size = sz as u16;
        mem
    }

    pub unsafe fn lean_free_small(ptr: *mut c_void) {
        mi_free(ptr);
    }

    pub unsafe fn lean_small_mem_size(ptr: *mut c_void) -> u32 {
        (*(ptr as *mut LeanObject)).cs_size as u32
    }

    pub unsafe fn set_heartbeats(count: u64) {
        G_HEARTBEAT.with(|cell| cell.set(count));
    }

    pub fn add_heartbeats(count: u64) {
        G_HEARTBEAT.with(|cell| cell.set(cell.get().wrapping_add(count)));
    }

    pub unsafe fn lean_inc_heartbeat() {
        add_heartbeats(1);
    }

    pub fn get_num_heartbeats() -> u64 {
        G_HEARTBEAT.with(|cell| cell.get())
    }

    pub fn lean_get_num_heartbeats() -> u64 {
        get_num_heartbeats()
    }

    pub fn lean_set_heartbeats(count: u64) {
        unsafe {
            set_heartbeats(count);
        }
    }
}

pub(crate) use runtime_alloc_impl::{
    add_heartbeats, finalize_alloc, get_num_heartbeats, initialize_alloc, lean_alloc_small,
    lean_free_small, lean_get_num_heartbeats, lean_inc_heartbeat, lean_set_heartbeats,
    lean_small_mem_size, set_heartbeats,
};
