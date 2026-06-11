// Port of kernel/type_checker.cpp
// Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: type_checker.cpp is the Lean kernel type checker — ~800 lines of C++
// templates and virtual dispatch over lean::expr. Rust owns initialize_type_checker
// / finalize_type_checker and delegates to C++ shims.
// When libleancpp.a is linked (lean_use_libleancpp), those symbols are provided
// by C++ directly; otherwise the no-op stubs in lib.rs satisfy the extern block.
mod kernel_type_checker_impl {}
