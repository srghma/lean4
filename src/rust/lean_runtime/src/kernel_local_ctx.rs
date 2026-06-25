
/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Compatibility init/finalize hooks for the C++ local_ctx facade.
The LocalContext data constructors and operations are Lean definitions exported
from src/Lean/LocalContext.lean; typed C++ callers are inline in local_ctx.h.
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_local_ctx_impl {
    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean20initialize_local_ctxEv"
    )]
    pub extern "C" fn initialize_local_ctx() {}

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean18finalize_local_ctxEv"
    )]
    pub extern "C" fn finalize_local_ctx() {}
}
