use leanh_l1::{datatypes::LeanObject, emitted::lean_box::lean_box};

// --- Name ---
// Name.anonymous is the boxed scalar 0.
pub unsafe fn lean_name_anonymous() -> *mut LeanObject {
    lean_box(0)
}
