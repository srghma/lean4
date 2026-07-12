use leanh_l1::{
    datatypes::{LeanObject, LeanObjectTag, LeanTaskImp, LeanTaskObject},
    emitted::{lean_dec_ref::lean_dec_ref, lean_inc::lean_inc, lean_is_scalar::lean_is_scalar},
    runtime_apply::lean_apply_1,
    runtime_object_rc::lean_mark_mt::lean_mark_mt,
    runtime_object_task::scoped_current_task::current_task,
};
use std::sync::atomic::Ordering;

use crate::r#priv::{mk_closure_2_1::mk_closure_2_1, task_bind_fn2::task_bind_fn2};

pub unsafe fn task_bind_fn1(
    x: *mut LeanObject,
    f: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    let v = (*(x as *mut LeanTaskObject))
        .m_value
        .load(Ordering::Relaxed);
    debug_assert!(!v.is_null());
    lean_inc(v);
    lean_dec_ref(x);

    let new_task_obj = lean_apply_1(f, v);
    debug_assert!(!lean_is_scalar(new_task_obj) && matches!((*new_task_obj).tag(), LeanObjectTag::Task));
    let new_task = new_task_obj as *mut LeanTaskObject;

    if !(*new_task).m_value.load(Ordering::Acquire).is_null() {
        let result = (*new_task).m_value.load(Ordering::Relaxed);
        lean_inc(result);
        lean_dec_ref(new_task_obj);
        return result;
    }

    // Suspend: store continuation in m_closure of the current task.
    let ct = current_task();
    debug_assert!(!ct.is_null());
    let ct_imp = (*ct).m_imp as *mut LeanTaskImp;
    debug_assert!((*ct_imp).m_closure.is_null());
    let continuation = mk_closure_2_1(task_bind_fn2, new_task_obj);
    lean_mark_mt(continuation);
    (*ct_imp).m_closure = continuation;
    core::ptr::null_mut()
}
