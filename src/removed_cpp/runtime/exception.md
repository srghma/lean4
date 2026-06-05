# `runtime/exception` (`runtime/exception.h` and `runtime/exception.cpp`)

## Location of corresponding Rust implementation
The implementation corresponds to `src/rust/lean_runtime/src/runtime_exception.rs`.

## Discrepancies and issues
- **Algorithm & Approach**: The C++ code defined custom C++ exceptions (`lean::throwable`, `lean::stack_space_exception`, `lean::memory_exception`, etc.) that were thrown when resource limits were exceeded. Lean 4 generally uses unrecoverable panics or aborts for things like stack overflow or out of memory. 
- **Memory Model**: The Rust implementation exports C ABI functions like `throw_stack_space_exception` which, instead of throwing a catchable C++ exception, simply print an error message to stderr and call `std::process::abort()`. 
- **Porting Status**: Exceptions are effectively converted into fatal aborts, maintaining compatibility with the C API but deliberately removing the ability to catch these specific resource exhaustion errors (which were rarely caught cleanly anyway).
