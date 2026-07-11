use std::{ptr, sync::atomic::Ordering};

use leanh_l1::{
    datatypes::{LeanObject, LeanThunkObject},
    emitted::lean_box::lean_box,
    runtime_apply::lean_apply_1,
    runtime_object_rc::lean_mark_mt::lean_mark_mt,
};

pub unsafe fn lean_thunk_get_core(t: *mut LeanObject) -> *mut LeanObject {
    let thunk = t as *mut LeanThunkObject;
    let c = (*thunk).m_closure.swap(ptr::null_mut(), Ordering::AcqRel);
    if !c.is_null() {
        let r = lean_apply_1(c, lean_box(0));
        debug_assert!(!r.is_null());
        debug_assert!((*thunk).m_value.load(Ordering::Acquire).is_null());
        lean_mark_mt(r);
        (*thunk).m_value.store(r, Ordering::Release);
        r
    } else {
        while (*thunk).m_value.load(Ordering::Acquire).is_null() {
            std::thread::yield_now();
        }
        (*thunk).m_value.load(Ordering::Acquire)
    }
}
