use std::ffi::c_char;

use crate::{datatypes::LeanObject, r#priv::lean_mk_string_from_bytes::lean_mk_string_from_bytes};

pub unsafe fn lean_mk_string(s: *const c_char) -> *mut LeanObject {
    lean_mk_string_from_bytes(s, libc::strlen(s))
}

// // appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/kernel_type_checker.rs:366-370 and from src/rust/runtime/src/kernel_type_checker.rs:340-345
//
// #[inline(always)]
// unsafe fn lean_mk_string(s: *const u8, n: usize) -> *mut LeanObject {
//     lean_mk_string_from_bytes(s.cast(), n)
// }
//
// // appended by move_rust_fn_to_leanh_l1.ts from src/rust/leanh_l2/src/in_emit_rust.rs:421-426
// pub unsafe fn lean_mk_string(s: *const c_char) -> *mut LeanObject {
//     unsafe {
//         let len = libc::strlen(s);
//         lean_mk_string_unchecked(s, len, len)
//     }
// }
