// Port of kernel/inductive.cpp
// Copyright (c) 2018 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: inductive.cpp contains add_inductive_fn and elim_nested_inductive_fn —
// large C++ classes that build inductive type declarations. Rust owns
// initialize_inductive / finalize_inductive and delegates to C++ shims.
// When libleancpp.a is linked (lean_use_libleancpp), those symbols are provided
// by C++ directly; otherwise the no-op stubs in lib.rs satisfy the extern block.
mod kernel_inductive_impl {}
