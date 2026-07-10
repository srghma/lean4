use leanh_l1::datatypes::{LeanObject, LeanScalarArray, Size};

pub unsafe fn lean_sarray_size(obj: *const LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray<0>;
    (*sarray).m_size
}
