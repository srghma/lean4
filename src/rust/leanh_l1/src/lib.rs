/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(non_upper_case_globals, unsafe_op_in_unsafe_fn)]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Lean Rust support crates require 64-bit pointer width");

pub mod datatypes;
pub mod emitted;
pub mod r#priv;
pub mod runtime_apply;
pub mod runtime_exception;
pub mod runtime_interrupt;
pub mod runtime_mpz;
pub mod runtime_object_nat_int;
pub mod runtime_object_panic;
pub mod runtime_object_rc;
pub mod runtime_object_task;
pub mod runtime_once;
pub mod runtime_stack_info;
pub mod runtime_stack_overflow;
pub mod runtime_thread;
pub mod todo_import_from_lean;
