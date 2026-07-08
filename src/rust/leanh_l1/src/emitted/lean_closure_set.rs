use crate::{
    datatypes::LeanObject,
    r#priv::{
        lean_closure_arg_cptr::lean_closure_arg_cptr,
        lean_closure_num_fixed::lean_closure_num_fixed,
    },
};

// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_io_task.rs:34-41 and from src/rust/runtime/src/runtime_io_task.rs:35-42
// unsafe fn lean_closure_set(c: *mut LeanObject, idx: usize, value: *mut LeanObject) {
//     (*(c as *mut LeanClosureObject<0>))
//         .m_objs
//         .as_mut_ptr()
//         .add(idx)
//         .write(value);
// }
// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/library_ir_interpreter.rs:262-272 and from src/rust/runtime/src/library_ir_interpreter.rs:230-242
// unsafe fn lean_closure_set(cls: *mut LeanObject, idx: usize, val: *mut LeanObject) {
//     // closure args are after the LeanClosureObject header (16 bytes: header=8, fun=ptr, arity=u16, num_fixed=u16, padding)
//     const LEAN_CLOSURE_OBJECT_SIZE: usize = core::mem::size_of::<LeanClosureObject<0>>();
//     (cls as *mut u8)
//         .add(LEAN_CLOSURE_OBJECT_SIZE)
//         .cast::<*mut LeanObject>()
//         .add(idx)
//         .write(val);
// }

// appended by move_rust_fn_to_leanh_l1.ts from src/rust/leanh_l2/src/in_emit_rust.rs:32-39

#[inline]
pub unsafe fn lean_closure_set(obj: *mut LeanObject, idx: u32, value: *mut LeanObject) {
    unsafe {
        debug_assert!((idx as usize) < lean_closure_num_fixed(obj));
        *lean_closure_arg_cptr(obj).add(idx as usize) = value;
    }
}
