use crate::{
    datatypes::{LeanObject, LeanPromiseObject},
    emitted::lean_dec_ref::lean_dec_ref,
    r#priv::{lean_free_small_object::lean_free_small_object, mk_option_none::mk_option_none},
    runtime_object_task::{p1_get_task_manager::get_task_manager, p3_resolve::resolve},
};

pub unsafe fn lean_deactivate_promise(promise: *mut LeanPromiseObject) {
    if let Some(tm) = get_task_manager() {
        let none = unsafe { mk_option_none() };
        unsafe { resolve(&tm, (*promise).m_result, none) };
        unsafe {
            let task = (*promise).m_result;
            lean_dec_ref(core::ptr::addr_of_mut!((*task).m_header));
        }
    }
    unsafe { lean_free_small_object(promise as *mut LeanObject) };
}
