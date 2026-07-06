/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Compatibility init/finalize hooks for the C++ declaration facade.
The declaration data constructors are Lean definitions exported from
src/Lean/Declaration.lean; typed C++ callers are inline in declaration.h.
*/

mod kernel_declaration_impl {
    pub fn initialize_declaration() {}
    pub fn finalize_declaration() {}
}
fn
