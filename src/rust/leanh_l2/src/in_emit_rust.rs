/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use core::ffi::{c_char, c_int, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicI32, Ordering};

use crate::datatypes::{
    F32InitFn, F64InitFn, LeanClosureObject, LeanCtorObject, LeanObject, LeanOnceCell, ObjInitFn,
    Size, U16InitFn, U32InitFn, U64InitFn, U8InitFn, UsizeInitFn, LEAN_CLOSURE_TAG,
    LEAN_MAX_CTOR_TAG,
};
use crate::not_in_emit_rust::{
    lean_alloc_ctor, lean_alloc_ctor_memory, lean_box, lean_closure_arg_cptr,
    lean_closure_num_fixed, lean_ctor_num_objs, lean_ctor_obj_cptr, lean_ctor_scalar_cptr,
    lean_is_ref, lean_is_scalar_bool, lean_obj_once_cold, lean_ptr_tag, lean_usize_to_nat,
    quar_report_uaf, run_once, LEAN_UAF_POISON_RC, UAF_DETECT,
};
use crate::runtime_io_stream::initialize_io;
use crate::runtime_libuv::initialize_libuv;
use crate::runtime_mutex::initialize_mutex;
use crate::runtime_object_panic::lean_string_cstr;
use crate::runtime_object_rc::{
    lean_alloc_object, lean_dec_ref_cold, lean_free_object, lean_mark_persistent,
};
use crate::runtime_object_string::lean_mk_string_unchecked;
use crate::runtime_process::initialize_process;
use crate::runtime_stack_info::save_stack_info;
use crate::runtime_stack_overflow::initialize_stack_overflow;

