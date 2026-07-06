/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Compatibility init/finalize hooks for the C++ local_ctx facade.
The LocalContext data constructors and operations are Lean definitions exported
from src/Lean/LocalContext.lean; typed C++ callers are inline in local_ctx.h.
*/

mod kernel_local_ctx_impl {
    pub fn initialize_local_ctx() {}
    pub fn finalize_local_ctx() {}
}
