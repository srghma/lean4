// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_rc.rs:469-532

use std::sync::atomic::Ordering;

use crate::{
    datatypes::{
        LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MPZ_TAG, LEAN_PROMISE_TAG,
        LEAN_REF_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG, LEAN_THUNK_TAG,
        LeanMpzObject, LeanObject, LeanPromiseObject, LeanTaskObject,
    },
    r#priv::{
        dec_for_del::dec_for_del, lean_array_byte_size::lean_array_byte_size,
        lean_array_cptr::lean_array_cptr, lean_array_size::lean_array_size,
        lean_closure_arg_cptr::lean_closure_arg_cptr,
        lean_closure_byte_size::lean_closure_byte_size,
        lean_closure_num_fixed::lean_closure_num_fixed, lean_dealloc::lean_dealloc,
        lean_free_small_object::lean_free_small_object,
        lean_runtime_deactivate_promise::lean_runtime_deactivate_promise,
        lean_runtime_deactivate_task::lean_runtime_deactivate_task,
        lean_sarray_byte_size::lean_sarray_byte_size, lean_string_byte_size::lean_string_byte_size,
        lean_to_external::lean_to_external, lean_to_promise::lean_to_promise,
        lean_to_ref::lean_to_ref, lean_to_task::lean_to_task, lean_to_thunk::lean_to_thunk,
    },
    runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic,
};

#[inline(always)]
pub unsafe fn lean_del_core_other(o: *mut LeanObject, tag: u8, todo: &mut *mut LeanObject) {
    match tag {
        LEAN_CLOSURE_TAG => {
            let it = lean_closure_arg_cptr(o);
            for i in 0..lean_closure_num_fixed(o) {
                dec_for_del(*it.add(i), todo);
            }
            lean_dealloc(o, lean_closure_byte_size(o));
        }
        LEAN_ARRAY_TAG => {
            let it = lean_array_cptr(o);
            for i in 0..lean_array_size(o) {
                dec_for_del(*it.add(i), todo);
            }
            lean_dealloc(o, lean_array_byte_size(o));
        }
        LEAN_SCALAR_ARRAY_TAG => {
            lean_dealloc(o, lean_sarray_byte_size(o));
        }
        LEAN_STRING_TAG => {
            lean_dealloc(o, lean_string_byte_size(o));
        }
        LEAN_MPZ_TAG => {
            let mpz = core::ptr::addr_of_mut!((*(o as *mut LeanMpzObject)).m_value);
            gmp_mpfr_sys::gmp::mpz_clear(mpz);
            lean_free_small_object(o);
        }
        LEAN_THUNK_TAG => {
            let thunk = lean_to_thunk(o);
            let c = (*thunk).m_closure.load(Ordering::Acquire);
            if !c.is_null() {
                dec_for_del(c, todo);
            }
            let v = (*thunk).m_value.load(Ordering::Acquire);
            if !v.is_null() {
                dec_for_del(v, todo);
            }
            lean_free_small_object(o);
        }
        LEAN_REF_TAG => {
            let value = (*lean_to_ref(o)).m_value;
            if !value.is_null() {
                dec_for_del(value, todo);
            }
            lean_free_small_object(o);
        }
        LEAN_TASK_TAG => {
            lean_runtime_deactivate_task(lean_to_task(o) as *mut LeanTaskObject);
        }
        LEAN_PROMISE_TAG => {
            lean_runtime_deactivate_promise(lean_to_promise(o) as *mut LeanPromiseObject);
        }
        LEAN_EXTERNAL_TAG => {
            let external = lean_to_external(o);
            ((*(*external).m_class).m_finalize)((*external).m_data);
            lean_free_small_object(o);
        }
        _ => {
            lean_internal_panic(c"lean_del_core: unknown object tag".as_ptr());
        }
    }
}
