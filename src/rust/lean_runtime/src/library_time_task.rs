/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_time_task_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_display_cumulative_profiling_times() -> *mut LeanObject;
        fn lean_cxx_profileit(
            category: *mut LeanObject,
            opts: *mut LeanObject,
            func: *mut LeanObject,
            decl: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_display_cumulative_profiling_times() -> *mut LeanObject {
        lean_cxx_display_cumulative_profiling_times()
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_profileit(
        category: *mut LeanObject,
        opts: *mut LeanObject,
        func: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_profileit(category, opts, func, decl)
    }
}
