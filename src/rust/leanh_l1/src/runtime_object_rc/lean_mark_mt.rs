#[cfg(lean_multi_thread)]
use std::{ffi::c_void, sync::atomic::Ordering};

use crate::emitted::lean_box::lean_box;
#[cfg(lean_multi_thread)]
use crate::{
    datatypes::{
        LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MAX_CTOR_TAG, LEAN_MPZ_TAG,
        LEAN_PROMISE_TAG, LEAN_REF_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG,
        LEAN_THUNK_TAG, LeanExternalObject, LeanObject, LeanPromiseObject, LeanRefObject,
        LeanThunkObject,
    },
    emitted::lean_alloc_closure::lean_alloc_closure,
    emitted::lean_dec::lean_dec,
    emitted::lean_is_scalar::lean_is_scalar_bool,
    r#priv::{
        lean_array_cptr::lean_array_cptr, lean_array_size::lean_array_size,
        lean_closure_arg_cptr::lean_closure_arg_cptr,
        lean_closure_num_fixed::lean_closure_num_fixed, lean_ctor_num_objs::lean_ctor_num_objs,
        lean_ctor_obj_cptr::lean_ctor_obj_cptr, lean_is_st::lean_is_st, lean_ptr_tag::lean_ptr_tag,
    },
    runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic,
    runtime_object_task::lean_task_get::lean_task_get,
};

unsafe fn mark_mt_fn(o: *mut LeanObject) -> *mut LeanObject {
    lean_mark_mt(o);
    lean_dec(o);
    lean_box(0)
}

#[cfg(not(lean_multi_thread))]
pub unsafe fn lean_mark_mt(_o: *mut LeanObject) {}

#[cfg(lean_multi_thread)]
pub unsafe fn lean_mark_mt(o: *mut LeanObject) {
    if lean_is_scalar_bool(o) || !lean_is_st(o) {
        return;
    }

    let mut todo = vec![o];
    while let Some(cur) = todo.pop() {
        if !lean_is_scalar_bool(cur) && lean_is_st(cur) {
            (*cur).rc = -(*cur).rc;
            let tag = lean_ptr_tag(cur);
            if tag <= LEAN_MAX_CTOR_TAG {
                let it = lean_ctor_obj_cptr(cur);
                for i in 0..lean_ctor_num_objs(cur) {
                    todo.push(*it.add(i));
                }
            } else {
                match tag {
                    LEAN_SCALAR_ARRAY_TAG | LEAN_STRING_TAG | LEAN_MPZ_TAG => {}
                    LEAN_EXTERNAL_TAG => {
                        let fn_obj = lean_alloc_closure(mark_mt_fn as *mut c_void, 1, 0);
                        let e = cur as *mut LeanExternalObject;
                        ((*(*e).m_class).m_foreach)((*e).m_data, fn_obj);
                        lean_dec(fn_obj);
                    }
                    LEAN_TASK_TAG => {
                        todo.push(lean_task_get(cur));
                    }
                    LEAN_PROMISE_TAG => {
                        let p = cur as *mut LeanPromiseObject;
                        todo.push((*p).m_result as *mut LeanObject);
                    }
                    LEAN_CLOSURE_TAG => {
                        let it = lean_closure_arg_cptr(cur);
                        for i in 0..lean_closure_num_fixed(cur) {
                            todo.push(*it.add(i));
                        }
                    }
                    LEAN_ARRAY_TAG => {
                        let it = lean_array_cptr(cur);
                        for i in 0..lean_array_size(cur) {
                            todo.push(*it.add(i));
                        }
                    }
                    LEAN_THUNK_TAG => {
                        let t = cur as *mut LeanThunkObject;
                        let c = (*t).m_closure.load(Ordering::Acquire);
                        if !c.is_null() {
                            todo.push(c);
                        }
                        let v = (*t).m_value.load(Ordering::Acquire);
                        if !v.is_null() {
                            todo.push(v);
                        }
                    }
                    LEAN_REF_TAG => {
                        let r = cur as *mut LeanRefObject;
                        if !(*r).m_value.is_null() {
                            todo.push((*r).m_value);
                        }
                    }
                    _ => {
                        lean_internal_panic(c"lean_mark_mt: unknown tag".as_ptr());
                    }
                }
            }
        }
    }
}
