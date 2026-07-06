/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_interrupt_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::ffi::c_char;
    use core::ptr;
    use leanh::LeanRefObject;
    use std::cell::Cell;

    unsafe extern "C" {
        fn lean_uncaught_exceptions() -> bool;
        fn lean_throw_interrupted() -> !;
        fn throw_heartbeat_exception() -> !;

        fn check_memory(component_name: *const c_char);

        fn check_stack(component_name: *const c_char);
    }

    unsafe fn lean_to_ref(o: *mut LeanObject) -> *mut LeanRefObject {
        o as *mut LeanRefObject
    }

    thread_local! {
        static G_CANCEL_TK: Cell<*mut LeanObject> = Cell::new(core::ptr::null_mut());
    }
    pub fn inc_heartbeat() {
        G_HEARTBEAT.with(|cell| cell.set(cell.get().wrapping_add(1)));
    }
    pub fn set_max_heartbeat_thousands(max: u32) {
        G_MAX_HEARTBEAT.with(|cell| cell.set((max as usize).wrapping_mul(1000)));
    }
    pub unsafe fn check_heartbeat() {
        inc_heartbeat();
        let max = G_MAX_HEARTBEAT.with(|cell| cell.get());
        let current = G_HEARTBEAT.with(|cell| cell.get());
        if max > 0 && current > max {
            throw_heartbeat_exception();
        }
    }
    pub unsafe fn check_interrupted() {
        let tk = G_CANCEL_TK.with(|cell| cell.get());
        if !tk.is_null() {
            if cancel_tk_is_set(tk) && !lean_uncaught_exceptions() {
                lean_throw_interrupted();
            }
        }
    }

    unsafe fn cancel_tk_is_set(tk: *mut LeanObject) -> bool {
        let set_ref = lean_ctor_get(tk, 1);
        lean_unbox((*lean_to_ref(set_ref)).m_value) != 0
    }
    pub unsafe fn check_system(component_name: *const c_char, do_check_interrupted: bool) {
        check_stack(component_name);
        check_memory(component_name);
        if do_check_interrupted {
            check_interrupted();
            check_heartbeat();
        }
    }

    pub unsafe fn sleep_for(ms: u32, mut step_ms: u32) {
        if step_ms == 0 {
            step_ms = 1;
        }
        let rounds = ms / step_ms;
        let c = std::time::Duration::from_millis(step_ms as u64);
        let r = std::time::Duration::from_millis((ms % step_ms) as u64);
        for _ in 0..rounds {
            std::thread::sleep(c);
            check_interrupted();
        }
        std::thread::sleep(r);
        check_interrupted();
    }

    // FFI wrappers for Lean code
    pub fn lean_internal_get_default_max_heartbeat() -> *mut LeanObject {
        const DEFAULT: usize = 0;

        unsafe { lean_box(DEFAULT) }
    }

    pub fn lean_internal_set_max_heartbeat(max: usize) -> *mut LeanObject {
        set_max_heartbeat(max);
        unsafe { lean_box(0) }
    }

    // Helper functions for cancel token get/set
    pub fn g_cancel_tk_get() -> *mut LeanObject {
        G_CANCEL_TK.with(|cell| cell.get())
    }

    pub fn g_cancel_tk_set(val: *mut LeanObject) {
        G_CANCEL_TK.with(|cell| cell.set(val));
    }

    // C++ Scope wrappers

    #[repr(C)]
    pub struct ScopeHeartbeat {
        m_old: usize,
    }

    impl ScopeHeartbeat {
        unsafe fn ctor(this: *mut ScopeHeartbeat, curr: usize) {
            let old = G_HEARTBEAT.with(|cell| cell.get());
            G_HEARTBEAT.with(|cell| cell.set(curr));
            ptr::write(ptr::addr_of_mut!((*this).m_old), old);
        }
        unsafe fn dtor(this: *mut ScopeHeartbeat) {
            G_HEARTBEAT.with(|cell| cell.set((*this).m_old));
        }
    }
    pub unsafe fn scope_heartbeat_ctor_complete(this: *mut ScopeHeartbeat, curr: usize) {
        ScopeHeartbeat::ctor(this, curr);
    }
    pub unsafe fn scope_heartbeat_ctor_base(this: *mut ScopeHeartbeat, curr: usize) {
        ScopeHeartbeat::ctor(this, curr);
    }
    pub unsafe fn scope_heartbeat_dtor_complete(this: *mut ScopeHeartbeat) {
        ScopeHeartbeat::dtor(this);
    }
    pub unsafe fn scope_heartbeat_dtor_base(this: *mut ScopeHeartbeat) {
        ScopeHeartbeat::dtor(this);
    }

    #[repr(C)]
    pub struct ScopeMaxHeartbeat {
        m_old: usize,
    }

    impl ScopeMaxHeartbeat {
        unsafe fn ctor(this: *mut ScopeMaxHeartbeat, max: usize) {
            let old = get_max_heartbeat();
            set_max_heartbeat(max);
            ptr::write(ptr::addr_of_mut!((*this).m_old), old);
        }
        unsafe fn dtor(this: *mut ScopeMaxHeartbeat) {
            set_max_heartbeat((*this).m_old);
        }
    }
    pub unsafe fn scope_max_heartbeat_ctor_complete(this: *mut ScopeMaxHeartbeat, max: usize) {
        ScopeMaxHeartbeat::ctor(this, max);
    }
    pub unsafe fn scope_max_heartbeat_ctor_base(this: *mut ScopeMaxHeartbeat, max: usize) {
        ScopeMaxHeartbeat::ctor(this, max);
    }
    pub unsafe fn scope_max_heartbeat_dtor_complete(this: *mut ScopeMaxHeartbeat) {
        ScopeMaxHeartbeat::dtor(this);
    }
    pub unsafe fn scope_max_heartbeat_dtor_base(this: *mut ScopeMaxHeartbeat) {
        ScopeMaxHeartbeat::dtor(this);
    }

    #[repr(C)]
    pub struct ScopeCancelTk {
        m_old: *mut LeanObject,
    }

    impl ScopeCancelTk {
        unsafe fn ctor(this: *mut ScopeCancelTk, tk: *mut LeanObject) {
            let old = g_cancel_tk_get();
            g_cancel_tk_set(tk);
            ptr::write(ptr::addr_of_mut!((*this).m_old), old);
        }
        unsafe fn dtor(this: *mut ScopeCancelTk) {
            g_cancel_tk_set((*this).m_old);
        }
    }
    pub unsafe fn scope_cancel_tk_ctor_complete(this: *mut ScopeCancelTk, tk: *mut LeanObject) {
        ScopeCancelTk::ctor(this, tk);
    }
    pub unsafe fn scope_cancel_tk_ctor_base(this: *mut ScopeCancelTk, tk: *mut LeanObject) {
        ScopeCancelTk::ctor(this, tk);
    }
    pub unsafe fn scope_cancel_tk_dtor_complete(this: *mut ScopeCancelTk) {
        ScopeCancelTk::dtor(this);
    }
    pub unsafe fn scope_cancel_tk_dtor_base(this: *mut ScopeCancelTk) {
        ScopeCancelTk::dtor(this);
    }

    /// Result-returning heartbeat check for the Rust type checker.
    /// Returns `Err(true)` if timeout, `Ok(())` otherwise.
    /// The caller converts `Err(true)` → `KernelError::DeterministicTimeout`.
    pub fn check_heartbeat_exceeded() -> bool {
        inc_heartbeat();
        let max = G_MAX_HEARTBEAT.with(|cell| cell.get());
        let current = G_HEARTBEAT.with(|cell| cell.get());
        max > 0 && current > max
    }

    /// Result-returning interrupted check for the Rust type checker.
    /// Returns `true` if interrupted.
    pub fn check_interrupted_flag() -> bool {
        let tk = G_CANCEL_TK.with(|cell| cell.get());
        if tk.is_null() {
            return false;
        }
        unsafe { cancel_tk_is_set(tk) && !lean_uncaught_exceptions() }
    }

    /// Set both the max heartbeat and the cancel token, returning old values for restoration.
    pub fn scope_max_heartbeat_push(max: usize) -> usize {
        let old = get_max_heartbeat();
        set_max_heartbeat(max);
        old
    }

    pub fn scope_max_heartbeat_pop(old: usize) {
        set_max_heartbeat(old);
    }

    pub fn scope_cancel_tk_push(tk: *mut LeanObject) -> *mut LeanObject {
        let old = g_cancel_tk_get();
        g_cancel_tk_set(tk);
        old
    }

    pub fn scope_cancel_tk_pop(old: *mut LeanObject) {
        g_cancel_tk_set(old);
    }
}
pub use runtime_interrupt_impl::*;
