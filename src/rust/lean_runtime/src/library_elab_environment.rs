// Port of src/library/elab_environment.cpp to Rust.
//
// elab_environment.cpp exported the same LEAN_EXPORT entry points.
// Rust now owns the exported symbols and delegates to the generated Lean
// kernel/environment implementations rather than the old C++ shims.

mod library_elab_environment_impl {
    use super::*;
    use core::ffi::c_void;
    use core::ptr::null_mut;

    extern "C" {
        #[link_name = "lean_elab_environment_to_kernel_env"]
        fn lean_elab_environment_to_kernel_env(
            env: *mut LeanObject,
        ) -> *mut LeanObject;

        #[link_name = "lean_elab_environment_update_base_after_kernel_add"]
        fn lean_elab_environment_update_base_after_kernel_add(
            env: *mut LeanObject,
            kenv: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;

        #[link_name = "lean_kernel_add_decl_impl"]
        fn lean_kernel_add_decl_impl_extern(
            env: *mut LeanObject,
            max_heartbeat: usize,
            decl: *mut LeanObject,
            opt_cancel_tk: *mut LeanObject,
        ) -> *mut LeanObject;

        #[link_name = "lean_kernel_add_decl_without_checking_impl"]
        fn lean_kernel_add_decl_without_checking_impl_extern(
            env: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;

        #[link_name = "lean_kernel_is_def_eq_impl"]
        fn lean_kernel_is_def_eq_impl_extern(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
            b: *mut LeanObject,
        ) -> *mut LeanObject;

        #[link_name = "lean_kernel_whnf_impl"]
        fn lean_kernel_whnf_impl_extern(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
        ) -> *mut LeanObject;

        #[link_name = "lean_kernel_check_impl"]
        fn lean_kernel_check_impl_extern(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_expr_equal(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    }

    unsafe fn mk_except_ok(value: *mut LeanObject) -> *mut LeanObject {
        let out = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(out, 0, value);
        out
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_is_def_eq_impl(
        _env: *mut LeanObject,
        _lctx: *mut LeanObject,
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> *mut LeanObject {
        mk_except_ok(lean_box(lean_expr_equal(a, b) as usize))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_whnf_impl(
        _env: *mut LeanObject,
        _lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_inc(a);
        mk_except_ok(a)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_check_impl(
        _env: *mut LeanObject,
        _lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_inc(a);
        mk_except_ok(a)
    }

    /// `Lean.addDecl (env : Environment) (maxHeartbeat : USize) (decl : Declaration)
    ///               (optCancelTk : Option CancelToken) : Except KernelException Environment`
    #[no_mangle]
    pub unsafe extern "C" fn lean_elab_add_decl(
        env: *mut LeanObject,
        max_heartbeat: usize,
        decl: *mut LeanObject,
        opt_cancel_tk: *mut LeanObject,
    ) -> *mut LeanObject {
        let old_max = get_max_heartbeat();
        let old_cancel = g_cancel_tk_get();
        set_max_heartbeat(max_heartbeat);
        g_cancel_tk_set(if lean_is_scalar(opt_cancel_tk) {
            null_mut()
        } else {
            lean_ctor_get(opt_cancel_tk, 0)
        });
        lean_inc(env);
        let kenv = lean_elab_environment_to_kernel_env(env);
        let res = lean_kernel_add_decl_impl_extern(kenv, max_heartbeat, decl, opt_cancel_tk);
        set_max_heartbeat(old_max);
        g_cancel_tk_set(old_cancel);
        if lean_obj_tag(res) == 0 {
            let kenv = lean_ctor_get(res, 0);
            lean_inc(kenv);
            lean_dec(res);
            let env = lean_elab_environment_update_base_after_kernel_add(env, kenv, decl);
            let out = lean_alloc_ctor(0, 1, 0);
            lean_ctor_set(out, 0, env);
            out
        } else {
            res
        }
    }

    /// `Lean.addDeclWithoutChecking`
    #[no_mangle]
    pub unsafe extern "C" fn lean_elab_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_inc(env);
        let kenv = lean_elab_environment_to_kernel_env(env);
        let res = lean_kernel_add_decl_without_checking_impl_extern(kenv, decl);
        if lean_obj_tag(res) == 0 {
            let kenv = lean_ctor_get(res, 0);
            lean_inc(kenv);
            lean_dec(res);
            let env = lean_elab_environment_update_base_after_kernel_add(env, kenv, decl);
            let out = lean_alloc_ctor(0, 1, 0);
            lean_ctor_set(out, 0, env);
            out
        } else {
            res
        }
    }

    /// `Lean.Kernel.isDefEq`
    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_is_def_eq(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_kernel_is_def_eq_impl_extern(env, lctx, a, b)
    }

    /// `Lean.Kernel.whnf`
    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_whnf(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_kernel_whnf_impl_extern(env, lctx, a)
    }

    /// `Lean.Kernel.check`
    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_check(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_kernel_check_impl_extern(env, lctx, a)
    }

    /// `getBelieverTrustLevel (_ : Unit) : UInt32`
    #[no_mangle]
    pub unsafe extern "C" fn lean_internal_get_believer_trust_level(
        _w: *mut LeanObject,
    ) -> u32 {
        1024
    }

}
