use leanh_l1::datatypes::{LeanObject, LeanScalarArray};

#[inline]
pub(crate) unsafe fn lean_sarray_mut_cptr(o: *mut LeanObject) -> *mut u8 {
    (o as *mut u8).add(core::mem::size_of::<LeanScalarArray<0>>())
}
