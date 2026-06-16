/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_ir_interpreter_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_eval_main(
            env: *mut LeanObject,
            opts: *mut LeanObject,
            args: *mut LeanObject,
        ) -> u32;
        fn lean_cxx_eval_const(
            env: *mut LeanObject,
            opts: *mut LeanObject,
            c: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_cxx_run_mod_init_core(sym: *mut LeanObject) -> *mut LeanObject;
        fn lean_cxx_run_init(
            env: *mut LeanObject,
            opts: *mut LeanObject,
            decl: *mut LeanObject,
            init_decl: *mut LeanObject,
            io: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_eval_main(
        env: *mut LeanObject,
        opts: *mut LeanObject,
        args: *mut LeanObject,
    ) -> u32 {
        lean_cxx_eval_main(env, opts, args)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_eval_const(
        env: *mut LeanObject,
        opts: *mut LeanObject,
        c: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_eval_const(env, opts, c)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_run_mod_init_core(sym: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_run_mod_init_core(sym)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_run_init(
        env: *mut LeanObject,
        opts: *mut LeanObject,
        decl: *mut LeanObject,
        init_decl: *mut LeanObject,
        io: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_run_init(env, opts, decl, init_decl, io)
    }
}
