#![allow(non_upper_case_globals, unsafe_op_in_unsafe_fn)]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Lean Rust support crates require 64-bit pointer width");

pub mod emitted;
pub mod r#priv;
pub mod runtime_io_error;
pub mod runtime_io_stream;
pub mod runtime_mutex;
pub mod runtime_object_task;
pub mod todo_import_from_lean;
pub mod runtime_stack_overflow;
