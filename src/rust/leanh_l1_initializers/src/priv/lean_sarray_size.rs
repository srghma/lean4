use leanh_l1::{
    datatypes::{LeanObject, Size},
    r#priv::lean_to_sarray::lean_to_sarray,
};

pub unsafe fn lean_sarray_size(obj: *const LeanObject) -> Size {
    (*lean_to_sarray(obj)).m_size
}
