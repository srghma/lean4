use leanh_l1::{datatypes::LeanObject, r#priv::lean_to_sarray::lean_to_sarray};

pub unsafe fn lean_sarray_cptr(obj: *const LeanObject) -> *const u8 {
    unsafe { (*lean_to_sarray(obj)).m_data.as_ptr() }
}
