// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_rc.rs:293-297

use crate::{
    datatypes::{LeanClosureObject, LeanObject},
    r#priv::lean_to_closure::lean_to_closure,
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_closure_set`, `lean_ctor_release`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_closure_arg_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe {
        (*(lean_to_closure(obj) as *mut LeanClosureObject<0>))
            .m_objs
            .as_mut_ptr()
    }
}
