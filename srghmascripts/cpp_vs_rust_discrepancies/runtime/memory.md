# `runtime/memory` (`runtime/memory.h` and `runtime/memory.cpp`)

## Location of corresponding Rust implementation
The implementation is in `src/rust/lean_runtime/src/runtime_memory.rs`.

## Discrepancies and issues
- **Algorithm & Approach**: The C++ code checked the process memory usage periodically (`LEAN_CHECK_MEM_THRESHOLD`) against a max threshold using OS-specific functions like `getrusage`, `GetProcessMemoryInfo`, or reading `/proc/self/statm`. If the threshold was exceeded, it threw `memory_exception`.
- **Rust Port**: The Rust port (`runtime_memory.rs`) does exactly the same thing. It uses conditional compilation (`#[cfg(target_os = "...")]`) to invoke the correct underlying OS APIs (via `libc`, `mach2`, or `windows_sys`).
- **Exceptions**: Instead of throwing a C++ `memory_exception`, the Rust code calls `throw_memory_exception` from `runtime_exception.rs`, which aborts the process with an error message.
- **Third Party Libs**: The port natively uses Rust crates (`libc`, `mach2`, `windows_sys`) instead of the C/C++ system headers.
