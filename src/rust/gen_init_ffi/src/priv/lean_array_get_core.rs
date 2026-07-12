use leanh_l1::datatypes::LeanObject;

pub unsafe fn lean_array_get_core(a: *mut LeanObject, idx: usize) -> *mut LeanObject {
    let a = leanh_l1::r#priv::lean_to_array::lean_to_array(a);
    debug_assert!(idx < leanh_l1::r#priv::lean_array_size::lean_array_size(a as *mut LeanObject));
    unsafe { (*a).m_data[idx] }
}
