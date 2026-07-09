use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_is_scalar::lean_is_scalar, lean_unbox::lean_unbox},
    runtime_object_nat_int::lean_nat_big_eq,
};

// appended by move_rust_fn_to_leanh_l1_initializers.ts from ../lean4-rust/src/rust/lean_runtime/src/kernel_type_checker.rs:1126-1135

// --- Nat comparisons / helpers ---
pub unsafe fn lean_nat_eq(a: *const LeanObject, b: *const LeanObject) -> bool {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        lean_unbox(a) == lean_unbox(b)
    } else {
        lean_nat_big_eq(a as *mut _, b as *mut _)
    }
}
