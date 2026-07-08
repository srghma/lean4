/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(non_upper_case_globals, unsafe_op_in_unsafe_fn)]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Lean Rust support crates require 64-bit pointer width");

pub mod common1;
pub mod datatypes;
pub mod lean_alloc_ctor;
pub mod lean_box;
pub mod lean_box_float;
pub mod lean_box_float32;
pub mod lean_box_uint32;
pub mod lean_box_uint64;
pub mod lean_box_usize;
pub mod lean_ctor_set_float;
pub mod lean_ctor_set_uint64;
pub mod lean_ctor_set_usize;
pub mod lean_is_scalar;
pub mod lean_unbox;
pub mod runtime_object_panic;
// pub mod base;
// pub mod in_emit_rust;
// pub mod kernel_type_checker;
// pub mod not_in_emit_rust;
// pub mod runtime_apply;
// pub mod runtime_event_loop;
// pub mod runtime_exception;
// pub mod runtime_interrupt;
// pub mod runtime_io_stream;
// pub mod runtime_libuv;
// pub mod runtime_mutex;
// pub mod runtime_object_name;
// pub mod runtime_object_panic;
// pub mod runtime_object_rc;
// pub mod runtime_object_string;
// pub mod runtime_object_task;
// pub mod runtime_process;
// pub mod runtime_stack_info;
// pub mod runtime_stack_overflow;
// pub mod runtime_thread;
// pub mod runtime_timer;

// pub use arity::lean_apply_m;
// pub use datatypes::{
//     F32InitFn, F64InitFn, LEAN_ARRAY_TAG, LEAN_CLOSURE_MAX_ARGS, LEAN_CLOSURE_TAG,
//     LEAN_EXTERNAL_TAG, LEAN_MAX_CTOR_TAG, LEAN_MAX_SMALL_NAT, LEAN_MPZ_TAG, LEAN_OBJECT_SIZE_DELTA,
//     LEAN_PROMISE_TAG, LEAN_REF_TAG, LEAN_RESERVED_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG,
//     LEAN_STRUCT_ARRAY_TAG, LEAN_TASK_TAG, LEAN_THUNK_TAG, LeanArrayObject, LeanClosureObject,
//     LeanCtorObject, LeanExternalClass, LeanExternalFinalizeProc, LeanExternalForeachProc,
//     LeanExternalObject, LeanMpzObject, LeanMpzStruct, LeanObject, LeanOnceCell, LeanPromiseObject,
//     LeanRefObject, LeanScalarArray, LeanStringObject, LeanTaskImp, LeanTaskObject, LeanThunkObject,
//     MpzT, ObjInitFn, Size, U8InitFn, U16InitFn, U32InitFn, U64InitFn, UsizeInitFn,
// };
// pub use in_emit_rust::{
//     lean_alloc_closure, lean_box_float, lean_box_float32, lean_box_uint32, lean_box_uint64,
//     lean_box_usize, lean_closure_set, lean_cstr_to_nat, lean_ctor_get, lean_ctor_get_float,
//     lean_ctor_get_float32, lean_ctor_get_uint8, lean_ctor_get_uint16, lean_ctor_get_uint32,
//     lean_ctor_get_uint64, lean_ctor_get_usize, lean_ctor_release, lean_ctor_set,
//     lean_ctor_set_float, lean_ctor_set_float32, lean_ctor_set_tag, lean_ctor_set_uint8,
//     lean_ctor_set_uint16, lean_ctor_set_uint32, lean_ctor_set_uint64, lean_ctor_set_usize,
//     lean_dec, lean_dec_ref, lean_dec_ref_known, lean_float_once, lean_float32_once, lean_inc,
//     lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_init_task_manager, lean_initialize,
//     lean_initialize_runtime_module, lean_io_mark_end_initialization, lean_io_result_get_value,
//     lean_io_result_is_error, lean_io_result_is_ok, lean_io_result_mk_ok, lean_io_result_show_error,
//     lean_is_exclusive, lean_is_scalar, lean_mark_persistent, lean_mk_string,
//     lean_mk_string_unchecked, lean_obj_once, lean_obj_tag, lean_run_main, lean_setup_args,
//     lean_small_nat, lean_uint8_dec_eq, lean_uint8_dec_le, lean_uint8_dec_lt, lean_uint8_of_nat_mk,
//     lean_uint8_once, lean_uint8_to_nat, lean_uint16_dec_eq, lean_uint16_dec_le, lean_uint16_dec_lt,
//     lean_uint16_of_nat, lean_uint16_of_nat_mk, lean_uint16_once, lean_uint16_to_nat,
//     lean_uint32_dec_eq, lean_uint32_dec_le, lean_uint32_dec_lt, lean_uint32_of_nat,
//     lean_uint32_of_nat_mk, lean_uint32_once, lean_uint32_to_nat, lean_uint64_dec_eq,
//     lean_uint64_dec_le, lean_uint64_dec_lt, lean_uint64_of_nat, lean_uint64_of_nat_mk,
//     lean_uint64_once, lean_uint64_to_nat, lean_unbox, lean_unbox_float, lean_unbox_float32,
//     lean_unbox_uint32, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
// };
// pub use not_in_emit_rust::{
//     dec_for_del, get_next, lean_align, lean_alloc_ctor, lean_alloc_ctor_memory, lean_alloc_object,
//     lean_alloc_small_object, lean_alloc_string, lean_array_byte_size, lean_array_cptr,
//     lean_array_size, lean_box, lean_closure_arg_cptr, lean_closure_byte_size,
//     lean_closure_num_fixed, lean_ctor_num_objs, lean_ctor_obj_cptr, lean_ctor_scalar_cptr,
//     lean_dealloc, lean_dec_ref_cold, lean_del_core, lean_del_core_other, lean_free_object,
//     lean_free_small_object, lean_global_alloc, lean_global_dealloc, lean_is_ref,
//     lean_is_scalar_bool, lean_is_st, lean_mpz_clear, lean_obj_once_cold, lean_ptr_tag,
//     lean_sarray_byte_size, lean_string_byte_size, lean_string_data, lean_usize_to_nat,
//     lock_once_cell, pop_back, push_back, run_once, set_next, unlock_once_cell,
// };
