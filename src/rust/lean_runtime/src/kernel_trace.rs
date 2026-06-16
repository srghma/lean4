/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Rust implementation of kernel/trace.cpp functions.
C++ shim handles: register_trace_class (throws), tout::~tout(), operator<<(ostream&, tclass)
This file handles: initialize_trace, finalize_trace, is_trace_class_enabled, scope_trace_env
*/

use std::cell::Cell;

// Thread-local replacement for LEAN_THREAD_PTR(const options, g_opts).
// Stores options const* — a pointer to the options struct which itself is {lean_object* m_obj}.
// So this is *const *mut LeanObject (pointer to the inner lean_object* field).
thread_local! {
    static G_OPTS: Cell<*const *mut LeanObject> = Cell::new(std::ptr::null());
}

extern "C" {
    fn lean_is_trace_class_enabled(opts: *mut LeanObject, cls: *mut LeanObject) -> bool;
}

// initialize_trace / finalize_trace — empty no-ops
#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean16initialize_traceEv")]
pub unsafe extern "C" fn lean_cxx_initialize_trace() {}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean14finalize_traceEv")]
pub unsafe extern "C" fn lean_cxx_finalize_trace() {}

// is_trace_class_enabled — delegates to Lean-exported function.
// n is `name const&` which in x86-64 ABI is lean::name const* = pointer to {lean_object*}.
// We dereference to get the inner lean_object* and call lean_inc (mimicking to_obj_arg()).
#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean22is_trace_class_enabledERKNS_4nameE")]
pub unsafe extern "C" fn lean_cxx_is_trace_class_enabled(n: *const *mut LeanObject) -> bool {
    let opts_holder = G_OPTS.get();
    if opts_holder.is_null() {
        return false;
    }
    let opts_obj = *opts_holder;
    lean_inc(opts_obj);
    let n_obj = *n;
    lean_inc(n_obj);
    lean_is_trace_class_enabled(opts_obj, n_obj)
}

// scope_trace_env — RAII for thread-local g_opts.
// Layout matches C++ class: { m_old_opts: const options* } = { *const *mut LeanObject }
#[repr(C)]
pub struct ScopeTraceEnv {
    m_old_opts: *const *mut LeanObject,
}

// C1 constructor. opts is `options const&` = lean::options const* = *const *mut LeanObject.
#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean15scope_trace_envC1ERKNS_16elab_environmentERKNS_7optionsE")]
pub unsafe extern "C" fn lean_cxx_scope_trace_env_ctor_c1(
    this: *mut ScopeTraceEnv,
    _env: *const *mut LeanObject,
    opts: *const *mut LeanObject,
) {
    let old = G_OPTS.get();
    (*this).m_old_opts = old;
    G_OPTS.set(opts);
}

// C2 constructor (usually identical to C1)
#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean15scope_trace_envC2ERKNS_16elab_environmentERKNS_7optionsE")]
pub unsafe extern "C" fn lean_cxx_scope_trace_env_ctor_c2(
    this: *mut ScopeTraceEnv,
    _env: *const *mut LeanObject,
    opts: *const *mut LeanObject,
) {
    lean_cxx_scope_trace_env_ctor_c1(this, _env, opts);
}

// D1 destructor
#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean15scope_trace_envD1Ev")]
pub unsafe extern "C" fn lean_cxx_scope_trace_env_dtor_c1(this: *mut ScopeTraceEnv) {
    let old = (*this).m_old_opts;
    G_OPTS.set(old);
}

// D2 destructor (usually identical to D1)
#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean15scope_trace_envD2Ev")]
pub unsafe extern "C" fn lean_cxx_scope_trace_env_dtor_c2(this: *mut ScopeTraceEnv) {
    lean_cxx_scope_trace_env_dtor_c1(this);
}
