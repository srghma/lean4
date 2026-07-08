use crate::{
    datatypes::LeanObject, lean_dec_ref::lean_dec_ref, lean_inc::lean_inc,
    runtime_object_task::lean_task_get::lean_task_get,
};
pub unsafe fn lean_task_get_own(t: *mut LeanObject) -> *mut LeanObject {
    let v = lean_task_get(t);
    unsafe { lean_inc(v) };
    lean_dec_ref(t);
    v
}
