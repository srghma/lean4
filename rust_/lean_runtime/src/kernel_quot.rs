// Port of kernel/quot.cpp
// Copyright (c) 2018 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: quot.cpp builds the Quot type axioms by constructing lean::expr / lean::level
// objects using C++ constructors. Rust owns initialize_quot / finalize_quot and
// delegates to C++ shims.
// When libleancpp.a is linked (lean_use_libleancpp), those symbols are provided
// by C++ directly; otherwise the no-op stubs in lib.rs satisfy the extern block.
mod kernel_quot_impl {}
