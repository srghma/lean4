/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(dead_code, non_upper_case_globals, non_snake_case)]

pub mod r#gen;
pub mod lean_imports_rs;
pub mod leanh;
// mod runtime;
// mod kernel;
// mod library;

pub use leanh::*;
// pub use runtime::{
//     get_init_fn_name_for, get_max_memory_opt_name, get_profiling_threshold, get_profiler,
//     get_timeout_opt_name, get_verbose, get_verbose_opt_name, initialize_constructions_util,
//     initialize_name, initialize_name_generator, initialize_options, lean_finalize,
//     lean_initialize, lean_io_error_to_string_rust, lean_io_result_get_error,
//     lean_io_result_get_value, lean_io_result_is_ok, lean_runtime_mk_cnstr, lean_string_cstr,
//     mk_constructions_name_generator, mk_embedded_nul_error, options_ctor_c1,
//     options_ctor_c2, options_get_bool, options_update,
// };
// pub use runtime::lean_mk_string;
//
// pub(crate) use kernel::{finalize_level, initialize_level};
// pub(crate) use library::{
//     finalize_ir_interpreter, finalize_time_task,
// };
// pub(crate) use runtime::{
//     lean_alloc_closure, lean_alloc_object, lean_apply_1, lean_apply_2, lean_array_push,
//     lean_decode_io_error, lean_decode_uv_error, lean_dec_ref_cold, lean_get_num_heartbeats,
//     lean_float32_once_cold, lean_float_once_cold, lean_io_promise_new,
//     lean_io_promise_resolve, lean_mark_mt, lean_mark_persistent, lean_mk_string_from_bytes,
//     lean_name_eq, lean_obj_once_cold, lean_set_heartbeats, lean_task_get,
//     lean_uint16_once_cold, lean_uint32_once_cold, lean_uint64_once_cold,
//     lean_uint8_once_cold, lean_usize_once_cold, lean_alloc_small_object, runtime_alloc_impl,
//     runtime_apply_impl, runtime_io_stream_impl, runtime_object_array_impl,
//     runtime_object_name_impl, runtime_object_nat_int_impl, runtime_object_panic_impl,
//     runtime_object_rc_impl, runtime_object_size_impl, runtime_object_string_impl,
// };
