
/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Compatibility init/finalize hooks for the C++ quotient facade.
The remaining typed quotient helpers are inline in quot.h.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_quot_impl {
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean15initialize_quotEv"
    )]
    pub extern "C" fn initialize_quot() {}

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean13finalize_quotEv"
    )]
    pub extern "C" fn finalize_quot() {}
}
