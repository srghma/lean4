# `runtime/thread` (`runtime/thread.h` and `runtime/thread.cpp`)

## Location of corresponding Rust implementation
The implementation is in `src/rust/lean_runtime/src/runtime_thread.rs`.

## Discrepancies and issues
- **Algorithm & Approach**: The C++ implementation defined `lean::lthread` (a thread with a configurable stack size, spawning via `pthread_create` or `CreateThread`), `lean_run_main` to handle `LEAN_STACK_SIZE_KB` parsing, and a thread-local finalization queue mechanism for thread shutdown (mostly for garbage collecting the thread's memory allocator).
- **Rust Port**: `runtime_thread.rs` accurately ports this functionality. It uses `libc` bindings (`pthread_create`) on Unix and `windows_sys` bindings on Windows to spawn threads, rather than `std::thread`, purely to support the custom stack sizes required by Lean's deep recursion. 
- **Memory Model**: The thread-local finalizer queues in C++ (`__thread` or `__declspec(thread)`) have been ported to Rust `thread_local!` using `Cell<*mut FinalizerList>`. The overall lifecycle semantics remain identical.
- **Third Party Libs**: Native `libc` / `windows_sys` crates are used in Rust to spawn threads, replacing direct `<pthread.h>` / `<windows.h>` includes.
