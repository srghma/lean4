use core::{
    ffi::c_void,
    ptr,
    sync::atomic::{AtomicI32, Ordering},
};
use libmimalloc_sys as mi;

#[cfg(all(lean_has_address_sanitizer, unix))]
use libloading::os::unix::Library as UnixLibrary;

use crate::{
    datatypes::{
        LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MAX_CTOR_TAG, LEAN_MPZ_TAG,
        LEAN_PROMISE_TAG, LEAN_REF_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG,
        LEAN_THUNK_TAG, LeanExternalObject, LeanMpzObject, LeanObject, LeanPromiseObject,
        LeanRefObject, LeanTaskObject, LeanThunkObject,
    },
    in_emit_rust::{lean_alloc_closure, lean_dec},
    not_in_emit_rust::{
        dec_for_del, lean_array_byte_size, lean_array_cptr, lean_array_size, lean_box,
        lean_closure_arg_cptr, lean_closure_byte_size, lean_closure_num_fixed, lean_ctor_num_objs,
        lean_ctor_obj_cptr, lean_dealloc, lean_free_small_object, lean_has_rc, lean_is_scalar_bool,
        lean_ptr_tag, lean_sarray_byte_size, lean_string_byte_size, pop_back,
    },
    runtime_object_panic::{lean_internal_panic, lean_internal_panic_out_of_memory},
    runtime_object_task::{
        lean_runtime_deactivate_promise, lean_runtime_deactivate_task, lean_task_get,
    },
};

#[cfg(all(lean_has_address_sanitizer, unix))]
unsafe fn ignore_lsan_object(ptr: *mut c_void) {
    let lib = UnixLibrary::this();
    if let Ok(ignore) = unsafe { lib.get::<unsafe fn(*mut c_void)>(c"__lsan_ignore_object") } {
        unsafe { (*ignore)(ptr) };
    }
}

#[cfg(lean_has_address_sanitizer)]
#[inline(always)]
unsafe fn lsan_ignore(o: *mut LeanObject) {
    ignore_lsan_object(o as *mut c_void);
}

#[cfg(not(lean_has_address_sanitizer))]
#[inline(always)]
unsafe fn lsan_ignore(_o: *mut LeanObject) {}

unsafe fn mark_persistent_fn(o: *mut LeanObject) -> *mut LeanObject {
    lean_mark_persistent(o);
    lean_box(0)
}

pub unsafe fn lean_mark_persistent(o: *mut LeanObject) {
    // TODO: export
    // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 356 (🔁)
    let mut todo = vec![o];
    while let Some(cur) = todo.pop() {
        if !lean_is_scalar_bool(cur) && lean_has_rc(cur) {
            (*cur).rc = 0;
            lsan_ignore(cur);
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
                        let fn_obj = lean_alloc_closure(mark_persistent_fn as *mut c_void, 1, 0);
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
                        lean_internal_panic(c"lean_mark_persistent: unknown tag".as_ptr());
                    }
                }
            }
        }
    }
}
