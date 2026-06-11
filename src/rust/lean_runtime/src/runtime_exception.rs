// Port of src/runtime/exception.cpp to Rust.
// Exception *types* remain C++ classes (throwable, exception, interrupted, etc.)
// because the rest of the codebase catches them with `catch (lean::exception &)`.
// The exported `throw_*` / `lean_throw_*` functions delegate to thin C++ shims
// (exception_shims.cpp) that do the actual `throw`.



// ── C++ shims that actually throw the C++ exception objects ──────────────────

extern "C" {
    /// Throws `lean::exception("failed to retrieve thread stack size")`
    #[link_name = "lean_cxx_throw_get_stack_size_failed"]
    fn cxx_throw_get_stack_size_failed() -> !;

    /// Throws `lean::stack_space_exception(component_name)`
    #[link_name = "lean_cxx_throw_stack_space_exception"]
    fn cxx_throw_stack_space_exception(component_name: *const c_char) -> !;

    /// Throws `lean::heartbeat_exception()`
    #[link_name = "lean_cxx_throw_heartbeat_exception"]
    fn cxx_throw_heartbeat_exception() -> !;

    /// Throws `lean::memory_exception(component_name)`
    #[link_name = "lean_cxx_throw_memory_exception"]
    fn cxx_throw_memory_exception(component_name: *const c_char) -> !;

    /// Throws `lean::interrupted()`
    #[link_name = "lean_cxx_throw_interrupted"]
    fn cxx_throw_interrupted() -> !;

    /// Returns `std::uncaught_exceptions() > 0`
    #[link_name = "lean_cxx_uncaught_exceptions"]
    fn cxx_uncaught_exceptions() -> c_int;
}

// ── Exported FFI functions ───────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn throw_get_stack_size_failed() -> ! {
    unsafe { cxx_throw_get_stack_size_failed() }
}

#[no_mangle]
pub extern "C" fn throw_stack_space_exception(component_name: *const c_char) -> ! {
    unsafe { cxx_throw_stack_space_exception(component_name) }
}

#[no_mangle]
pub extern "C" fn throw_heartbeat_exception() -> ! {
    unsafe { cxx_throw_heartbeat_exception() }
}

#[no_mangle]
pub extern "C" fn throw_memory_exception(component_name: *const c_char) -> ! {
    unsafe { cxx_throw_memory_exception(component_name) }
}

#[no_mangle]
pub extern "C" fn lean_throw_interrupted() -> ! {
    unsafe { cxx_throw_interrupted() }
}

#[no_mangle]
pub extern "C" fn lean_uncaught_exceptions() -> bool {
    unsafe { cxx_uncaught_exceptions() > 0 }
}
