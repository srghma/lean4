use leanh_l1::{datatypes::LeanObject, runtime_object_nat_int::lean_alloc_mpz_from_mpz};

use crate::r#priv::{sharecommon_data::ShareCommonFn, sharecommon_fn_save::sharecommon_fn_save};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:75-79

pub(crate) unsafe fn sharecommon_fn_visit_mpz(this: &mut ShareCommonFn, a: *mut LeanObject) {
    let new_a = lean_alloc_mpz_from_mpz(a);
    sharecommon_fn_save(this, a, new_a);
}
