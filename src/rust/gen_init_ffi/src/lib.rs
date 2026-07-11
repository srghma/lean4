#![allow(non_snake_case, non_upper_case_globals, unsafe_op_in_unsafe_fn)]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Lean Rust support crates require 64-bit pointer width");

pub mod ffi;
pub mod r#priv;
