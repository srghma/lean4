/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_alloc_impl {
    use crate::*;
    use core::cell::Cell;

    thread_local! {
        static G_HEARTBEAT: Cell<u64> = const { Cell::new(0) };
    }

    pub fn initialize_alloc() {}

    pub fn finalize_alloc() {}

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
    add_heartbeats, get_num_heartbeats, lean_get_num_heartbeats, lean_inc_heartbeat,
    lean_set_heartbeats, set_heartbeats,
};
