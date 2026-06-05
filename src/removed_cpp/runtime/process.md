# `runtime/process` (`runtime/process.h` and `runtime/process.cpp`)

## Location of corresponding Rust implementation
The implementation corresponds to `src/rust/lean_runtime/src/runtime_process.rs`.

## Discrepancies and issues
- **Algorithm & Approach**: The C++ implementation manages `IO.Process` primitives such as spawning children with redirected standard streams, waiting, killing, and fetching environment/directory info. It contains two entirely disjoint implementations: one for Windows (using `CreateProcess`, `CreatePipe`, etc.) and one for Unix (using `fork`, `execvp`, `pipe`).
- **Rust Port Status**: The Rust file (`runtime_process.rs`) faithfully ports the Unix implementation using raw `libc` bindings (`fork`, `execvp`, `pipe2`, `dup2`). However, the Windows implementation is **not ported to Rust**; on Windows builds, the C++ file `process.cpp` is still compiled and used directly.
- **Memory Model**: The Rust implementation carefully mimics the C++ memory management constraints. Specifically, it pre-allocates strings via `strdup` prior to calling `fork` and builds `execvp` arguments to avoid making calls to the system allocator (or Lean's allocator) between `fork` and `execvp`, which is crucial for compatibility with ASAN and to avoid deadlocks.
- **Third Party Libs**: The Rust code uses `libc` directly instead of Rust's `std::process::Command`, since it must interface perfectly with Lean's `IO.Process.Child` layout (extracting raw FDs and `pid_t`).
