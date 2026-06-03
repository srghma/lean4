/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_alloc_impl {
    use std::cell::Cell;

    thread_local! {
        static G_HEARTBEAT: Cell<u64> = const { Cell::new(0) };
    }

    #[cfg(not(lean_small_allocator))]
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean16initialize_allocEv")]
    pub extern "C" fn initialize_alloc() {}

    #[cfg(not(lean_small_allocator))]
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean14finalize_allocEv")]
    pub extern "C" fn finalize_alloc() {}

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean14set_heartbeatsEm")]
    pub extern "C" fn set_heartbeats(count: u64) {
        G_HEARTBEAT.with(|cell| cell.set(count));
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean14add_heartbeatsEm")]
    pub extern "C" fn add_heartbeats(count: u64) {
        G_HEARTBEAT.with(|cell| cell.set(cell.get().wrapping_add(count)));
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_inc_heartbeat() {
        add_heartbeats(1);
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean18get_num_heartbeatsEv")]
    pub extern "C" fn get_num_heartbeats() -> u64 {
        G_HEARTBEAT.with(|cell| cell.get())
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_get_num_heartbeats() -> u64 {
        get_num_heartbeats()
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_set_heartbeats(count: u64) {
        set_heartbeats(count);
    }
}

pub(crate) use runtime_alloc_impl::{lean_get_num_heartbeats, lean_set_heartbeats};
