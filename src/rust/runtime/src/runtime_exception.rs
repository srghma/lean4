/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_exception_impl {
    use core::ffi::c_char;



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
}
pub use runtime_exception_impl::*;
