use core::ptr::addr_of;
use leanh_l1::datatypes::{LeanObject, LeanScalarArray};

pub unsafe fn lean_sarray_cptr(obj: *const LeanObject) -> *const u8 {
    addr_of!((*(obj as *const LeanScalarArray<0>)).m_data).cast::<u8>() // TODO: return lean_to_sarray(o)->m_data;
}
