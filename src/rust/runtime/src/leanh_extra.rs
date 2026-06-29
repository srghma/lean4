/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(dead_code, non_upper_case_globals, non_snake_case)]

// Temporary runtime helper surface extracted from generated FFI modules.
// These helpers still live in `leanh` today; generated crates import them
// through `runtime::leanh_extra` so `crate::leanh` remains the EmitRust ABI
// import path. The implementations should move here as the runtime modules
// are restored from their current staged state.
pub use leanh::*;
