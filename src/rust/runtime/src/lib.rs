/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(
    non_upper_case_globals,
    non_snake_case,
    dead_code,
    unsafe_op_in_unsafe_fn,
    // unused_variables,
    // unused_assignments,
    // unused_parens,
    // unused_mut,
    // unused_imports
)]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Lean Rust runtime supports only 64-bit pointer width");

pub mod base;
pub mod kernel_abstract;
pub mod kernel_declaration;
pub mod kernel_environment;
pub mod kernel_equiv_manager;
pub mod kernel_expr;
pub mod kernel_expr_eq_fn;
pub mod kernel_for_each_fn;
pub mod kernel_instantiate;
pub mod kernel_level;
pub mod kernel_local_ctx;
pub mod kernel_num;
pub mod kernel_quot;
pub mod kernel_replace_fn;
pub mod kernel_trace;
pub mod kernel_type_checker;
pub mod library_constants;
pub mod library_dynlib;
pub mod library_elab_environment;
pub mod library_expr_lt;
pub mod library_formatter;
pub mod library_instantiate_mvars;
pub mod library_ir_interpreter;
pub mod library_llvm;
pub mod library_module;
pub mod library_print;
pub mod library_time_task;
pub mod library_util;
pub mod runtime_alloc;
pub mod runtime_compact;
pub mod runtime_compact_writer;
pub mod runtime_debug;
pub mod runtime_dns;
pub mod runtime_event_loop;
pub mod runtime_exception;
pub mod runtime_float;
pub mod runtime_interrupt;
pub mod runtime_io_error;
pub mod runtime_io_fs;
pub mod runtime_io_handle;
pub mod runtime_io_ref;
pub mod runtime_io_stream;
pub mod runtime_io_task;
pub mod runtime_libuv;
pub mod runtime_memory;
pub mod runtime_mpn;
pub mod runtime_mpz;
pub mod runtime_mutex;
pub mod runtime_net_addr;
pub mod runtime_object_array;
pub mod runtime_object_name;
pub mod runtime_object_nat_int;
pub mod runtime_object_panic;
pub mod runtime_object_rc;
pub mod runtime_object_size;
pub mod runtime_object_string;
pub mod runtime_object_task;
pub mod runtime_once;
pub mod runtime_process;
pub mod runtime_sharecommon;
pub mod runtime_signal;
pub mod runtime_stack_info;
pub mod runtime_stack_overflow;
pub mod runtime_system;
pub mod runtime_tcp;
pub mod runtime_thread;
pub mod runtime_timer;
pub mod runtime_udp;

pub use base::*;
pub(crate) use runtime_alloc::runtime_alloc_impl;
pub(crate) use runtime_apply::runtime_apply_impl;
pub(crate) use runtime_float::{lean_box_float, lean_box_float32};
pub(crate) use runtime_interrupt::runtime_interrupt_impl;
pub(crate) use runtime_object_array::runtime_object_array_impl;
pub(crate) use runtime_object_name::runtime_object_name_impl;
pub(crate) use runtime_object_nat_int::runtime_object_nat_int_impl;
pub(crate) use runtime_object_panic::runtime_object_panic_impl;
pub(crate) use runtime_object_rc::runtime_object_rc_impl;
pub(crate) use runtime_object_rc::runtime_object_rc_impl::{
    LeanArrayObject, LeanClosureObject, LeanExternalClass, LeanExternalObject, LeanMpzObject,
    LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject, LeanTaskObject,
    LeanThunkObject,
};
pub(crate) use runtime_object_size::runtime_object_size_impl;
pub(crate) use runtime_object_string::runtime_object_string_impl;
pub(crate) use runtime_object_task::runtime_object_task_impl;

#[allow(unused_imports)]
pub use gmp_mpfr_sys::gmp::{
    mpz_add as __gmpz_add, mpz_add_ui as __gmpz_add_ui, mpz_and as __gmpz_and,
    mpz_clear as __gmpz_clear, mpz_cmp as __gmpz_cmp, mpz_cmp_si as __gmpz_cmp_si,
    mpz_cmp_ui as __gmpz_cmp_ui, mpz_divexact as __gmpz_divexact,
    mpz_fdiv_q_2exp as __gmpz_fdiv_q_2exp, mpz_fdiv_r_2exp as __gmpz_fdiv_r_2exp,
    mpz_fits_sint_p as __gmpz_fits_sint_p, mpz_fits_uint_p as __gmpz_fits_uint_p,
    mpz_gcd as __gmpz_gcd, mpz_get_si as __gmpz_get_si, mpz_get_ui as __gmpz_get_ui,
    mpz_getlimbn as __gmpz_getlimbn, mpz_init as __gmpz_init, mpz_init_set as __gmpz_init_set,
    mpz_init_set_si as __gmpz_init_set_si, mpz_init_set_str as __gmpz_init_set_str,
    mpz_init_set_ui as __gmpz_init_set_ui, mpz_ior as __gmpz_ior, mpz_mul as __gmpz_mul,
    mpz_mul_2exp as __gmpz_mul_2exp, mpz_mul_si as __gmpz_mul_si, mpz_mul_ui as __gmpz_mul_ui,
    mpz_neg as __gmpz_neg, mpz_pow_ui as __gmpz_pow_ui, mpz_set as __gmpz_set,
    mpz_size as __gmpz_size, mpz_sizeinbase as __gmpz_sizeinbase, mpz_sub as __gmpz_sub,
    mpz_sub_ui as __gmpz_sub_ui, mpz_swap as __gmpz_swap, mpz_t as MpzStruct, mpz_t as MpzT,
    mpz_tdiv_q as __gmpz_tdiv_q, mpz_tdiv_q_2exp as __gmpz_tdiv_q_2exp,
    mpz_tdiv_q_ui as __gmpz_tdiv_q_ui, mpz_tdiv_qr as __gmpz_tdiv_qr, mpz_tdiv_r as __gmpz_tdiv_r,
    mpz_xor as __gmpz_xor,
};
