// Port of kernel/trace.cpp
// Copyright (c) 2015 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: trace.cpp uses LEAN_THREAD_PTR (a C++ thread-local pointer) and
// scope_trace_env RAII — both C++-only constructs. initialize_trace / finalize_trace
// are no-ops in the original C++ too.
// When libleancpp.a is linked (lean_use_libleancpp), those symbols are provided
// by C++ directly; otherwise the no-op stubs in lib.rs satisfy the extern block.
mod kernel_trace_impl {}
