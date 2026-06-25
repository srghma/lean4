
/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Rust replacement for library/num.cpp.
initialize_num / finalize_num are empty no-ops.
All other num functions are unused (verified: no external callers).
*/

// initialize_num / finalize_num — empty no-ops
#[cfg_attr(
    feature = "export-runtime-ffi",
    export_name = "_ZN4lean14initialize_numEv"
)]
pub unsafe extern "C" fn lean_cxx_initialize_num() {}

#[cfg_attr(
    feature = "export-runtime-ffi",
    export_name = "_ZN4lean12finalize_numEv"
)]
pub unsafe extern "C" fn lean_cxx_finalize_num() {}
