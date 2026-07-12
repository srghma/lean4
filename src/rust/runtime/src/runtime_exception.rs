/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_exception_impl {
    use crate::runtime_expr_shared::{EXCEPT_ERROR_TAG, EXCEPT_OK_TAG};
    use core::ffi::c_char;
    use leanh_l1::runtime_exception::{abort_with_message, cstr_to_string};
    use leanh_l1::{
        datatypes::LeanObject,
        emitted::{lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set},
    };

    pub fn throw_heartbeat_exception() -> ! {
        abort_with_message("(deterministic) timeout")
    }

    pub unsafe fn throw_memory_exception(component_name: *const c_char) -> ! {
        let component_name = cstr_to_string(component_name);
        abort_with_message(&format!(
            "excessive memory consumption detected at '{component_name}' (potential solution: increase memory consumption threshold)"
        ))
    }

    pub fn lean_throw_interrupted() -> ! {
        abort_with_message("interrupted")
    }

    // TODO: is this correct? this is not present in cpp
    pub fn lean_uncaught_exceptions() -> bool {
        false
    }

    pub unsafe fn mk_except_ok(value: *mut LeanObject) -> *mut LeanObject {
        let result = lean_alloc_ctor(EXCEPT_OK_TAG, 1, 0);
        lean_ctor_set(result, 0, value);
        result
    }

    pub unsafe fn mk_except_err(error: *mut LeanObject) -> *mut LeanObject {
        let result = lean_alloc_ctor(EXCEPT_ERROR_TAG, 1, 0);
        lean_ctor_set(result, 0, error);
        result
    }
}
pub use runtime_exception_impl::*;
