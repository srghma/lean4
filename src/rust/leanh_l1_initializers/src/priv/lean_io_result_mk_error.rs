// appended by move_rust_fn_to_leanh_l1_initializers.ts from ../lean4-rust/src/rust/lean_runtime/src/lib.rs:2582-2587

// appended by move_rust_fn_to_leanh_l1_initializers.ts from src/rust/runtime/src/base.rs:1278-1282

use leanh_l1::{
    datatypes::{LeanIoResultTag, LeanObject},
    emitted::{lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set},
};

// pub unsafe fn lean_io_result_mk_error(error: *mut LeanObject) -> *mut LeanObject {
//     let mut fields = [error];
//     lean_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
// }
pub unsafe fn lean_io_result_mk_error(error: *mut LeanObject) -> *mut LeanObject {
    let obj = lean_alloc_ctor(LeanIoResultTag::Error as u32, 1, 0);
    lean_ctor_set(obj, 0, error);
    obj
}
