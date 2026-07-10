use leanh_l1::datatypes::{LeanObject, LeanStringObject};

pub unsafe fn lean_string_size(obj: *const LeanObject) -> usize {
    let string = obj as *const LeanStringObject<0>;
    (*string).m_size
}
