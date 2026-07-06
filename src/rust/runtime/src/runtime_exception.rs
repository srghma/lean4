/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_exception_impl {
    use core::ffi::c_char;

    const LAKE_CONFIG_MANUAL_SECTION: &str =
        "find/?domain=Verso.Genre.Manual.section&name=lake-config-toml";

    unsafe fn cstr_to_string(value: *const c_char) -> String {
        if value.is_null() {
            return String::new();
        }
        std::ffi::CStr::from_ptr(value)
            .to_string_lossy()
            .into_owned()
    }

    fn abort_with_message(msg: &str) -> ! {
        eprintln!("{msg}");
        std::process::abort();
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn throw_get_stack_size_failed() -> ! {
        abort_with_message("failed to retrieve thread stack size")
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn throw_stack_space_exception(component_name: *const c_char) -> ! {
        let component_name = cstr_to_string(component_name);
        abort_with_message(&format!(
            "deep recursion was detected at '{component_name}' (potential solution: increase elaboration stack size using the `lean --tstack` flag). This flag can be set in the `weakLeanArgs` field of the Lake configuration. Further details are available in the Lean reference manual at {}{LAKE_CONFIG_MANUAL_SECTION}",
            env!("LEAN_RUST_MANUAL_ROOT")
        ))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn throw_heartbeat_exception() -> ! {
        abort_with_message("(deterministic) timeout")
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn throw_memory_exception(component_name: *const c_char) -> ! {
        let component_name = cstr_to_string(component_name);
        abort_with_message(&format!(
            "excessive memory consumption detected at '{component_name}' (potential solution: increase memory consumption threshold)"
        ))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_throw_interrupted() -> ! {
        abort_with_message("interrupted")
    }

    // TODO: is this correct? this is not present in cpp
    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uncaught_exceptions() -> bool {
        false
    }
}
pub use runtime_exception_impl::*;
