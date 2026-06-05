# `runtime/debug` (`runtime/debug.h` and `runtime/debug.cpp`)

## Location of corresponding Rust implementation
The corresponding Rust implementation is located in `src/rust/lean_runtime/src/runtime_debug.rs`. 

## Discrepancies and issues
1. **Macros and Helper functions:**
   - C++ uses macros like `lean_assert`, `lean_verify`, `lean_unreachable`, etc., that rely on preprocessor (`#ifdef LEAN_DEBUG`). 
   - In Rust, these are replaced by native Rust macros (`debug_assert!`, `unreachable!`) for standard code, and runtime assertions are exported via FFI (e.g., `lean_notify_assert`).
2. **Global State:**
   - C++ uses static variables/globals inside `debug.cpp` to store debug tags. 
   - Rust uses `AtomicBool` for flags like `HAS_VIOLATIONS`, `ASSERTIONS_ENABLED`, and `DEBUG_DIALOG`. Debug tags are stored in a `OnceLock<Mutex<HashSet<String>>>`.
3. **Debugger invocation:**
   - Rust replicates the `invoke_debugger` behavior (reading stdin to decide whether to continue, abort, or trap/stop) using `std::io::stdin().read_exact`.
4. **Exceptions:**
   - C++ defined a class `unreachable_reached` which inherited from `lean::exception`. Rust doesn't use C++ exceptions and relies on `process::abort()` or panics for unreachable code paths or assertions failure.

The transition nicely utilizes standard Rust atomics and standard library I/O, eliminating the need for some manual C++ memory management and custom exception classes.
