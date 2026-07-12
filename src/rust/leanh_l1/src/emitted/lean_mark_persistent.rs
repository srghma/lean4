use std::{ffi::c_void, sync::atomic::Ordering};

use crate::{
    datatypes::{LeanObject, LeanObjectTag},
    emitted::{
        lean_alloc_closure::lean_alloc_closure, lean_box::lean_box, lean_dec::lean_dec,
        lean_is_scalar::lean_is_scalar,
    },
    r#priv::{
        lean_array_cptr::lean_array_cptr, lean_array_size::lean_array_size,
        lean_closure_arg_cptr::lean_closure_arg_cptr,
        lean_closure_num_fixed::lean_closure_num_fixed, lean_ctor_num_objs::lean_ctor_num_objs,
        lean_ctor_obj_cptr::lean_ctor_obj_cptr, lean_has_rc::lean_has_rc,
        lean_is_ctor::lean_is_ctor, lean_to_external::lean_to_external,
        lean_to_promise::lean_to_promise, lean_to_ref::lean_to_ref, lean_to_thunk::lean_to_thunk,
        lsan_ignore::lsan_ignore,
    },
    runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic,
    runtime_object_task::lean_task_get::lean_task_get,
};

unsafe fn mark_persistent_fn(o: *mut LeanObject) -> *mut LeanObject {
    lean_mark_persistent(o);
    lean_box(0)
}

pub unsafe fn lean_mark_persistent(o: *mut LeanObject) {
    // TODO: export
    let mut todo = vec![o];
    while let Some(cur) = todo.pop() {
        if !lean_is_scalar(cur) && lean_has_rc(cur) {
            (*cur).rc = 0;
            lsan_ignore(cur);
            let tag = (*cur).tag();
            if lean_is_ctor(cur) {
                let it = lean_ctor_obj_cptr(cur);
                for i in 0..lean_ctor_num_objs(cur) {
                    todo.push(*it.add(i));
                }
            } else {
                match tag {
                    LeanObjectTag::ScalarArray | LeanObjectTag::String | LeanObjectTag::Mpz => {}
                    LeanObjectTag::External => {
                        let fn_obj = lean_alloc_closure(mark_persistent_fn as *mut c_void, 1, 0);
                        let external = lean_to_external(cur);
                        ((*(*external).m_class).m_foreach)((*external).m_data, fn_obj);
                        lean_dec(fn_obj);
                    }
                    LeanObjectTag::Task => {
                        todo.push(lean_task_get(cur));
                    }
                    LeanObjectTag::Promise => {
                        todo.push((*lean_to_promise(cur)).m_result as *mut LeanObject);
                    }
                    LeanObjectTag::Closure => {
                        let it = lean_closure_arg_cptr(cur);
                        for i in 0..lean_closure_num_fixed(cur) {
                            todo.push(*it.add(i));
                        }
                    }
                    LeanObjectTag::Array => {
                        let it = lean_array_cptr(cur);
                        for i in 0..lean_array_size(cur) {
                            todo.push(*it.add(i));
                        }
                    }
                    LeanObjectTag::Thunk => {
                        let thunk = lean_to_thunk(cur);
                        let c = (*thunk).m_closure.load(Ordering::Acquire);
                        if !c.is_null() {
                            todo.push(c);
                        }
                        let v = (*thunk).m_value.load(Ordering::Acquire);
                        if !v.is_null() {
                            todo.push(v);
                        }
                    }
                    LeanObjectTag::Ref => {
                        let value = (*lean_to_ref(cur)).m_value;
                        if !value.is_null() {
                            todo.push(value);
                        }
                    }
                    _ => {
                        lean_internal_panic("lean_mark_persistent: unknown tag");
                    }
                }
            }
        }
    }
}
