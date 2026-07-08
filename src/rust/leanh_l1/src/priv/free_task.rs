use crate::{
    datatypes::{LeanObject, LeanTaskImp, LeanTaskObject},
    r#priv::{free_task_imp::free_task_imp, lean_free_small_object::lean_free_small_object},
};

pub unsafe fn free_task(t: *mut LeanTaskObject) {
    let imp = unsafe { (*t).m_imp as *mut LeanTaskImp };
    if !imp.is_null() {
        unsafe { free_task_imp(imp) };
    }
    unsafe { lean_free_small_object(t as *mut LeanObject) };
}
