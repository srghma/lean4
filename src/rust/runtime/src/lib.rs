/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(
    non_upper_case_globals,
    non_snake_case,
    dead_code,
    // unused_variables,
    // unused_assignments,
    // unused_parens,
    // unused_mut,
    // unused_imports
)]

mod base;
mod kernel_abstract;
mod kernel_declaration;
mod kernel_environment;
mod kernel_equiv_manager;
mod kernel_expr;
mod kernel_expr_eq_fn;
mod kernel_for_each_fn;
mod kernel_instantiate;
mod kernel_level;
mod kernel_local_ctx;
mod kernel_num;
mod kernel_quot;
mod kernel_replace_fn;
mod kernel_trace;
mod kernel_type_checker;
mod library_constants;
mod library_dynlib;
mod library_elab_environment;
mod library_expr_lt;
mod library_formatter;
mod library_instantiate_mvars;
mod library_ir_interpreter;
mod library_llvm;
mod library_module;
mod library_print;
mod library_time_task;
mod library_util;
mod runtime_alloc;
mod runtime_apply;
mod runtime_compact;
mod runtime_compact_writer;
mod runtime_debug;
mod runtime_dns;
mod runtime_event_loop;
mod runtime_exception;
mod runtime_float;
mod runtime_interrupt;
mod runtime_io_error;
mod runtime_io_fs;
mod runtime_io_handle;
mod runtime_io_ref;
mod runtime_io_stream;
mod runtime_io_task;
mod runtime_libuv;
mod runtime_memory;
mod runtime_mpn;
mod runtime_mpz;
mod runtime_mutex;
mod runtime_net_addr;
mod runtime_object_array;
mod runtime_object_name;
mod runtime_object_nat_int;
mod runtime_object_panic;
mod runtime_object_rc;
mod runtime_object_size;
mod runtime_object_string;
mod runtime_object_task;
mod runtime_once;
mod runtime_process;
mod runtime_sharecommon;
mod runtime_signal;
mod runtime_stack_info;
mod runtime_stack_overflow;
mod runtime_system;
mod runtime_tcp;
mod runtime_thread;
mod runtime_timer;
mod runtime_udp;

pub use base::*;
pub(crate) use runtime_alloc::runtime_alloc_impl;
pub(crate) use runtime_apply::runtime_apply_impl;
pub(crate) use runtime_object_array::runtime_object_array_impl;
pub(crate) use runtime_object_name::runtime_object_name_impl;
pub(crate) use runtime_object_nat_int::runtime_object_nat_int_impl;
pub(crate) use runtime_object_panic::runtime_object_panic_impl;
pub(crate) use runtime_object_rc::runtime_object_rc_impl;
pub(crate) use runtime_object_size::runtime_object_size_impl;
pub(crate) use runtime_object_string::runtime_object_string_impl;
pub(crate) use runtime_object_task::runtime_object_task_impl;
pub(crate) use runtime_interrupt::runtime_interrupt_impl;
pub(crate) use runtime_float::{lean_box_float, lean_box_float32};
pub(crate) use runtime_object_rc::runtime_object_rc_impl::{
    LeanArrayObject, LeanClosureObject, LeanExternalClass, LeanExternalObject, LeanMpzObject,
    LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject, LeanTaskObject,
    LeanThunkObject,
};

#[allow(unused_imports)]
pub use gmp_mpfr_sys::gmp::{
    mpz_t as MpzStruct, mpz_t as MpzT, mpz_add as __gmpz_add,
    mpz_add_ui as __gmpz_add_ui, mpz_and as __gmpz_and, mpz_clear as __gmpz_clear,
    mpz_cmp as __gmpz_cmp, mpz_cmp_si as __gmpz_cmp_si, mpz_cmp_ui as __gmpz_cmp_ui,
    mpz_divexact as __gmpz_divexact, mpz_fdiv_q_2exp as __gmpz_fdiv_q_2exp,
    mpz_fdiv_r_2exp as __gmpz_fdiv_r_2exp, mpz_fits_sint_p as __gmpz_fits_sint_p,
    mpz_fits_uint_p as __gmpz_fits_uint_p, mpz_gcd as __gmpz_gcd,
    mpz_get_si as __gmpz_get_si, mpz_get_ui as __gmpz_get_ui,
    mpz_getlimbn as __gmpz_getlimbn, mpz_init as __gmpz_init,
    mpz_init_set as __gmpz_init_set, mpz_init_set_si as __gmpz_init_set_si,
    mpz_init_set_str as __gmpz_init_set_str, mpz_init_set_ui as __gmpz_init_set_ui,
    mpz_ior as __gmpz_ior, mpz_mul as __gmpz_mul, mpz_mul_2exp as __gmpz_mul_2exp,
    mpz_mul_si as __gmpz_mul_si, mpz_mul_ui as __gmpz_mul_ui, mpz_neg as __gmpz_neg,
    mpz_pow_ui as __gmpz_pow_ui, mpz_set as __gmpz_set, mpz_size as __gmpz_size,
    mpz_sizeinbase as __gmpz_sizeinbase, mpz_sub as __gmpz_sub,
    mpz_sub_ui as __gmpz_sub_ui, mpz_swap as __gmpz_swap, mpz_tdiv_q as __gmpz_tdiv_q,
    mpz_tdiv_q_2exp as __gmpz_tdiv_q_2exp, mpz_tdiv_q_ui as __gmpz_tdiv_q_ui,
    mpz_tdiv_qr as __gmpz_tdiv_qr, mpz_tdiv_r as __gmpz_tdiv_r, mpz_xor as __gmpz_xor,
};
