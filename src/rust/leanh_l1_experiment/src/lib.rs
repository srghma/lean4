/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(non_upper_case_globals, unsafe_op_in_unsafe_fn)]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Lean Rust support crates require 64-bit pointer width");

pub mod datatypes;
pub mod emit_rust_output_example;
