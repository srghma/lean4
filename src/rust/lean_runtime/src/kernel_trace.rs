// Port of kernel/trace.cpp
// Copyright (c) 2015 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: trace.cpp uses LEAN_THREAD_PTR (a C++ thread-local pointer) and
// scope_trace_env RAII — both C++-only constructs. Rust owns the trivial
// initialize_trace / finalize_trace pair (both no-ops in the original).

mod kernel_trace_impl {
    use super::*;

    #[export_name = "_ZN4lean16initialize_traceEv"]
    pub unsafe extern "C" fn initialize_trace() {
        // No-op — matches the original C++ body.
    }

    #[export_name = "_ZN4lean14finalize_traceEv"]
    pub unsafe extern "C" fn finalize_trace() {
        // No-op — matches the original C++ body.
    }
}
