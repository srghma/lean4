/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::leanh::*;
use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};
use crate::runtime::*;

pub(crate) mod kernel_environment_impl {
    use crate::kernel::type_checker::kernel_type_checker_impl::lean_rust_add_decl;
    use super::*;

    #[inline(always)]
    unsafe fn add_decl_dispatch(
        env: *mut LeanObject,
        decl: *mut LeanObject,
        check: u8,
    ) -> *mut LeanObject {
        lean_rust_add_decl(env, decl, check)
    }

    #[inline]
    pub(crate) unsafe fn lean_add_decl(
        env: *mut LeanObject,
        max_heartbeat: usize,
        decl: *mut LeanObject,
        opt_cancel_tk: *mut LeanObject,
    ) -> *mut LeanObject {
        let old_max = scope_max_heartbeat_push(max_heartbeat);
        let cancel_tk = if lean_is_scalar(opt_cancel_tk) {
            core::ptr::null_mut()
        } else {
            lean_ctor_get(opt_cancel_tk, 0)
        };
        let old_tk = scope_cancel_tk_push(cancel_tk);

        let result = add_decl_dispatch(env, decl, 1);

        scope_max_heartbeat_pop(old_max);
        scope_cancel_tk_pop(old_tk);

        result
    }

    #[inline]
    pub(crate) unsafe fn lean_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        add_decl_dispatch(env, decl, 0)
    }
}
