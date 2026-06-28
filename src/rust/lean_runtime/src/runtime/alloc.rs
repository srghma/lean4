/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/


pub(crate) mod runtime_alloc_impl {
    use std::cell::Cell;

    thread_local! {
        static G_HEARTBEAT: Cell<u64> = const { Cell::new(0) };
    }
    pub unsafe fn set_heartbeats(count: u64) {
        G_HEARTBEAT.with(|cell| cell.set(count));
    }

    pub unsafe fn add_heartbeats(count: u64) {
        G_HEARTBEAT.with(|cell| cell.set(cell.get().wrapping_add(count)));
    }

    #[inline]
    pub(crate) unsafe fn lean_inc_heartbeat() {
        add_heartbeats(1);
    }

    pub fn get_num_heartbeats() -> u64 {
        G_HEARTBEAT.with(|cell| cell.get())
    }

    #[inline]
    pub(crate) fn lean_get_num_heartbeats() -> u64 {
        get_num_heartbeats()
    }

    #[inline]
    pub(crate) fn lean_set_heartbeats(count: u64) {
        unsafe {
            set_heartbeats(count);
        }
    }
}

pub(crate) use runtime_alloc_impl::{lean_get_num_heartbeats, lean_set_heartbeats};
