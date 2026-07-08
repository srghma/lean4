use leanh_l1::datatypes::{LeanObject, LeanScalarArray, Size};
pub(crate) unsafe fn lean_sarray_set_size(obj: *mut LeanObject, size: Size) {
    let sarray = obj as *mut LeanScalarArray<0>;
    (*sarray).m_size = size;
}
