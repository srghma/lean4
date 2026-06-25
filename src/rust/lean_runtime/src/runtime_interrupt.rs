/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

pub(crate) mod runtime_interrupt_impl {
    use super::*;
    use core::ffi::c_char;
    use std::cell::Cell;

    extern "C" {
        #[link_name = "_ZN4lean12check_memoryEPKc"]
        fn check_memory(component_name: *const c_char);

        #[link_name = "_ZN4lean11check_stackEPKc"]
        fn check_stack(component_name: *const c_char);
    }

    #[repr(C)]
    struct LeanRefObject {
        header: LeanObject,
        value: *mut LeanObject,
    }

    unsafe fn lean_to_ref(o: *mut LeanObject) -> *mut LeanRefObject {
        o as *mut LeanRefObject
    }

    thread_local! {
        static G_MAX_HEARTBEAT: Cell<usize> = Cell::new(0);
        static G_HEARTBEAT: Cell<usize> = Cell::new(0);
        static G_CANCEL_TK: Cell<*mut LeanObject> = Cell::new(core::ptr::null_mut());
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean13inc_heartbeatEv"
    )]
    pub extern "C" fn inc_heartbeat() {
        G_HEARTBEAT.with(|cell| cell.set(cell.get().wrapping_add(1)));
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15reset_heartbeatEv"
    )]
    pub extern "C" fn reset_heartbeat() {
        G_HEARTBEAT.with(|cell| cell.set(0));
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean17set_max_heartbeatEm"
    )]
    pub extern "C" fn set_max_heartbeat(max: usize) {
        G_MAX_HEARTBEAT.with(|cell| cell.set(max));
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean17get_max_heartbeatEv"
    )]
    pub extern "C" fn get_max_heartbeat() -> usize {
        G_MAX_HEARTBEAT.with(|cell| cell.get())
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean27set_max_heartbeat_thousandsEj"
    )]
    pub extern "C" fn set_max_heartbeat_thousands(max: u32) {
        G_MAX_HEARTBEAT.with(|cell| cell.set((max as usize).wrapping_mul(1000)));
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15check_heartbeatEv"
    )]
    pub unsafe extern "C" fn check_heartbeat() {
        inc_heartbeat();
        let max = G_MAX_HEARTBEAT.with(|cell| cell.get());
        let current = G_HEARTBEAT.with(|cell| cell.get());
        if max > 0 && current > max {
            throw_heartbeat_exception();
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean17check_interruptedEv"
    )]
    pub unsafe extern "C" fn check_interrupted() {
        let tk = G_CANCEL_TK.with(|cell| cell.get());
        if !tk.is_null() {
            if cancel_tk_is_set(tk) && !has_uncaught_exception() {
                throw_interrupted();
            }
        }
    }

    unsafe fn cancel_tk_is_set(tk: *mut LeanObject) -> bool {
        let set_ref = lean_ctor_get(tk, 1);
        lean_unbox((*lean_to_ref(set_ref)).value) != 0
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean12check_systemEPKcb"
    )]
    pub unsafe extern "C" fn check_system(
        component_name: *const c_char,
        do_check_interrupted: bool,
    ) {
        check_stack(component_name);
        check_memory(component_name);
        if do_check_interrupted {
            check_interrupted();
            check_heartbeat();
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean9sleep_forEjj")]
    pub unsafe extern "C" fn sleep_for(ms: u32, mut step_ms: u32) {
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
    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_internal_get_default_max_heartbeat() -> *mut LeanObject {
        #[cfg(feature = "default-max-heartbeat")]
        const DEFAULT: usize = 200000; // standard Lean default
        #[cfg(not(feature = "default-max-heartbeat"))]
        const DEFAULT: usize = 0;

        unsafe { lean_box(DEFAULT) }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_internal_set_max_heartbeat(max: usize) -> *mut LeanObject {
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

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15scope_heartbeatC1Em"
    )]
    pub unsafe extern "C" fn scope_heartbeat_ctor_complete(this: *mut ScopeHeartbeat, curr: usize) {
        ScopeHeartbeat::ctor(this, curr);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15scope_heartbeatC2Em"
    )]
    pub unsafe extern "C" fn scope_heartbeat_ctor_base(this: *mut ScopeHeartbeat, curr: usize) {
        ScopeHeartbeat::ctor(this, curr);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15scope_heartbeatD1Ev"
    )]
    pub unsafe extern "C" fn scope_heartbeat_dtor_complete(this: *mut ScopeHeartbeat) {
        ScopeHeartbeat::dtor(this);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15scope_heartbeatD2Ev"
    )]
    pub unsafe extern "C" fn scope_heartbeat_dtor_base(this: *mut ScopeHeartbeat) {
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

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean19scope_max_heartbeatC1Em"
    )]
    pub unsafe extern "C" fn scope_max_heartbeat_ctor_complete(
        this: *mut ScopeMaxHeartbeat,
        max: usize,
    ) {
        ScopeMaxHeartbeat::ctor(this, max);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean19scope_max_heartbeatC2Em"
    )]
    pub unsafe extern "C" fn scope_max_heartbeat_ctor_base(
        this: *mut ScopeMaxHeartbeat,
        max: usize,
    ) {
        ScopeMaxHeartbeat::ctor(this, max);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean19scope_max_heartbeatD1Ev"
    )]
    pub unsafe extern "C" fn scope_max_heartbeat_dtor_complete(this: *mut ScopeMaxHeartbeat) {
        ScopeMaxHeartbeat::dtor(this);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean19scope_max_heartbeatD2Ev"
    )]
    pub unsafe extern "C" fn scope_max_heartbeat_dtor_base(this: *mut ScopeMaxHeartbeat) {
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

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15scope_cancel_tkC1EP11lean_object"
    )]
    pub unsafe extern "C" fn scope_cancel_tk_ctor_complete(
        this: *mut ScopeCancelTk,
        tk: *mut LeanObject,
    ) {
        ScopeCancelTk::ctor(this, tk);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15scope_cancel_tkC2EP11lean_object"
    )]
    pub unsafe extern "C" fn scope_cancel_tk_ctor_base(
        this: *mut ScopeCancelTk,
        tk: *mut LeanObject,
    ) {
        ScopeCancelTk::ctor(this, tk);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15scope_cancel_tkD1Ev"
    )]
    pub unsafe extern "C" fn scope_cancel_tk_dtor_complete(this: *mut ScopeCancelTk) {
        ScopeCancelTk::dtor(this);
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15scope_cancel_tkD2Ev"
    )]
    pub unsafe extern "C" fn scope_cancel_tk_dtor_base(this: *mut ScopeCancelTk) {
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
        unsafe { cancel_tk_is_set(tk) && !has_uncaught_exception() }
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
