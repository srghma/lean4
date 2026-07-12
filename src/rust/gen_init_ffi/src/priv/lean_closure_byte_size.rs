use leanh_l1::{
    datatypes::{LeanClosureObject, LeanObject},
    r#priv::lean_to_closure::lean_to_closure,
};

#[inline]
pub unsafe fn lean_closure_byte_size(obj: *const LeanObject) -> usize {
    let obj = lean_to_closure(obj);
    core::mem::size_of::<LeanClosureObject<0>>()
        + core::mem::size_of::<*mut LeanObject>() * unsafe { (*obj).m_num_fixed as usize }
}
