/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Compatibility init/finalize hooks for the C++ declaration facade.
The declaration data constructors are Lean definitions exported from
src/Lean/Declaration.lean; typed C++ callers are inline in declaration.h.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_declaration_impl {
    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean22initialize_declarationEv")]
    pub extern "C" fn initialize_declaration() {}

    #[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean20finalize_declarationEv")]
    pub extern "C" fn finalize_declaration() {}
}
