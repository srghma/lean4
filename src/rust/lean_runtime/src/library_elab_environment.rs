// Port of src/library/elab_environment.cpp to Rust.
//
// elab_environment.cpp exports five LEAN_EXPORT extern "C" functions.
// All operate on opaque Lean object pointers and call through to C++ class
// methods (elab_environment::add, type_checker::is_def_eq / whnf / check).
// Rust owns the exported symbols and delegates to C++ shims.

mod library_elab_environment_impl {
    use super::*;
    use core::ffi::c_void;

    extern "C" {
        fn lean_cxx_elab_add_decl(
            env: *mut LeanObject,
            max_heartbeat: usize,
            decl: *mut LeanObject,
            opt_cancel_tk: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_cxx_elab_add_decl_without_checking(
            env: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_cxx_kernel_is_def_eq(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
            b: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_cxx_kernel_whnf(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_cxx_kernel_check(
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            a: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_cxx_internal_get_believer_trust_level(w: *mut LeanObject) -> u32;
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
        lean_cxx_elab_add_decl(env, max_heartbeat, decl, opt_cancel_tk)
    }

    /// `Lean.addDeclWithoutChecking`
    #[no_mangle]
    pub unsafe extern "C" fn lean_elab_add_decl_without_checking(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_elab_add_decl_without_checking(env, decl)
    }

    /// `Lean.Kernel.isDefEq`
    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_is_def_eq(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_kernel_is_def_eq(env, lctx, a, b)
    }

    /// `Lean.Kernel.whnf`
    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_whnf(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_kernel_whnf(env, lctx, a)
    }

    /// `Lean.Kernel.check`
    #[no_mangle]
    pub unsafe extern "C" fn lean_kernel_check(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_kernel_check(env, lctx, a)
    }

    /// `getBelieverTrustLevel (_ : Unit) : UInt32`
    #[no_mangle]
    pub unsafe extern "C" fn lean_internal_get_believer_trust_level(
        w: *mut LeanObject,
    ) -> u32 {
        lean_cxx_internal_get_believer_trust_level(w)
    }
}
