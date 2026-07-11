// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_string.rs:77-85

use crate::{
    datatypes::{LEAN_MAX_SMALL_NAT, LeanObject},
    emitted::lean_box::lean_box,
    r#priv::lean_big_usize_to_nat::lean_big_usize_to_nat,
};

#[inline]
pub unsafe fn lean_usize_to_nat(n: usize) -> *mut LeanObject {
    // TODO: use likely
    if n <= LEAN_MAX_SMALL_NAT {
        lean_box(n)
    } else {
        lean_big_usize_to_nat(n)
    }
}
