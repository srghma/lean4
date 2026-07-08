// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_rc.rs:469-532

use std::sync::atomic::Ordering;

use crate::{
    datatypes::{
        LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MPZ_TAG, LEAN_PROMISE_TAG,
        LEAN_REF_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG, LEAN_THUNK_TAG,
        LeanExternalObject, LeanMpzObject, LeanObject, LeanPromiseObject, LeanRefObject,
        LeanTaskObject, LeanThunkObject,
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
            let t = o as *mut LeanThunkObject;
            let c = (*t).m_closure.load(Ordering::Acquire);
            if !c.is_null() {
                dec_for_del(c, todo);
            }
            let v = (*t).m_value.load(Ordering::Acquire);
            if !v.is_null() {
                dec_for_del(v, todo);
            }
            lean_free_small_object(o);
        }
        LEAN_REF_TAG => {
            let r = o as *mut LeanRefObject;
            if !(*r).m_value.is_null() {
                dec_for_del((*r).m_value, todo);
            }
            lean_free_small_object(o);
        }
        LEAN_TASK_TAG => {
            lean_runtime_deactivate_task(o as *mut LeanTaskObject);
        }
        LEAN_PROMISE_TAG => {
            lean_runtime_deactivate_promise(o as *mut LeanPromiseObject);
        }
        LEAN_EXTERNAL_TAG => {
            let e = o as *mut LeanExternalObject;
            ((*(*e).m_class).m_finalize)((*e).m_data);
            lean_free_small_object(o);
        }
        _ => {
            lean_internal_panic(c"lean_del_core: unknown object tag".as_ptr());
        }
    }
}
