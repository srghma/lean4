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
        #[cfg(not(unix))]
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

    /// runModInitCore (sym : @& String) : IO Bool
    ///
    /// Looks up `sym` in the current executable and, if found, calls it as a
    /// module-init function with signature `fn(builtin: u8) -> *mut LeanObject`
    /// where `builtin = 0` (user module, not a builtin/preloaded module).
    /// Returns IO.ok true on success, IO.ok false if the symbol is absent,
    /// or the IO error object if the init function itself returned an error.
    ///
    /// On Unix we use dlsym(RTLD_DEFAULT, ...) directly.
    /// On Windows we keep calling lean_cxx_run_mod_init_core (C++) which uses
    /// EnumProcessModules/GetProcAddress to enumerate all loaded DLLs.
    #[no_mangle]
    pub unsafe extern "C" fn lean_run_mod_init_core(sym: *mut LeanObject) -> *mut LeanObject {
        #[cfg(unix)]
        {
            let sym_cstr = lean_string_cstr(sym);
            let init = libc::dlsym(libc::RTLD_DEFAULT, sym_cstr);
            if init.is_null() {
                lean_io_result_mk_ok(lean_box(0)) // Bool.false: symbol not found
            } else {
                let init_fn: unsafe extern "C" fn(u8) -> *mut LeanObject =
                    core::mem::transmute(init);
                let builtin: u8 = 0;
                let r = init_fn(builtin);
                if lean_io_result_is_ok(r) {
                    lean_dec_ref(r);
                    lean_io_result_mk_ok(lean_box(1)) // Bool.true: init succeeded
                } else {
                    r // propagate IO error from the init function
                }
            }
        }
        #[cfg(not(unix))]
        {
            lean_cxx_run_mod_init_core(sym)
        }
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
