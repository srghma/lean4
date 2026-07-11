// appended by move_rust_fn_to_leanh_l1.ts from src/rust/leanh_l2/src/not_in_emit_rust.rs:47-52

use crate::{
    datatypes::{LEAN_REF_TAG, LeanObject},
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

// NOT IN EmitRust; here because it is used in `lean_dec_ref_known`.
#[inline]
pub unsafe fn lean_is_ref(obj: *const LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_REF_TAG }
}
