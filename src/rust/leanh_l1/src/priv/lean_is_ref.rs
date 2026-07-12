// appended by move_rust_fn_to_leanh_l1.ts from src/rust/leanh_l2/src/not_in_emit_rust.rs:47-52

use crate::{
    datatypes::{LeanObject, LeanObjectTag},
    emitted::lean_object_tag::lean_object_tag,
};

// NOT IN EmitRust; here because it is used in `lean_dec_ref_known`.
#[inline]
pub unsafe fn lean_is_ref(obj: *const LeanObject) -> bool {
    matches!(lean_object_tag(obj), LeanObjectTag::Ref)
}
