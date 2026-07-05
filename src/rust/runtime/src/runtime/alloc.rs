/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use std::cell::Cell;

thread_local! {
    static G_HEARTBEAT: Cell<u64> = const { Cell::new(0) };
}

#[inline]
pub fn set_heartbeats(count: u64) {
    G_HEARTBEAT.with(|cell| cell.set(count));
}

#[inline]
pub fn add_heartbeats(count: u64) {
    G_HEARTBEAT.with(|cell| cell.set(cell.get().wrapping_add(count)));
}

#[inline]
pub(crate) unsafe fn lean_inc_heartbeat() {
    add_heartbeats(1);
}

#[inline]
pub fn get_num_heartbeats() -> u64 {
    G_HEARTBEAT.with(|cell| cell.get())
}

#[inline]
pub(crate) fn lean_get_num_heartbeats() -> u64 {
    get_num_heartbeats()
}

#[inline]
pub(crate) fn lean_set_heartbeats(count: u64) {
    set_heartbeats(count);
}
