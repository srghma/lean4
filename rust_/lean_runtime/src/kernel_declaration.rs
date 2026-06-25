// Port of kernel/declaration.cpp
// Copyright (c) 2014 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
// NOTE: declaration.cpp constructs C++ value types (reducibility_hints,
// definition_val, constant_info, …) using C++ constructors and template
// helpers. Rust owns initialize_declaration / finalize_declaration and
// delegates to C++ shims.
// When libleancpp.a is linked (lean_use_libleancpp), those symbols are provided
// by C++ directly; otherwise the no-op stubs in lib.rs satisfy the extern block.
mod kernel_declaration_impl {}
