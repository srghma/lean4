use leanh_l1::{datatypes::LeanObject, emitted::lean_box::lean_box};

// List.nil ignores its (erased) element-type argument.
pub unsafe fn lean_mk_list_nil(_ty: *mut LeanObject) -> *mut LeanObject {
    lean_box(0)
}
