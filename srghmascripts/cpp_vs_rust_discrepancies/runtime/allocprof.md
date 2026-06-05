# `runtime/allocprof` (`runtime/allocprof.h` and `runtime/allocprof.cpp`)

## Location of corresponding Rust implementation
The implementation corresponds to the Rust file `src/rust/lean_runtime/src/lib.rs` (specifically the function `lean_io_allocprof`).

## Discrepancies and issues
- **Algorithm**: The C++ code provided a RAII class `allocprof` that would snapshot global allocation counters (`g_num_ctor`, `g_num_closure`, etc.) upon construction, and then print the delta upon destruction if the runtime was compiled with `-D RUNTIME_STATS=ON`.
- **Rust Implementation**: In Rust, `lean_io_allocprof` evaluates the IO action and currently hardcodes a warning that `Allocation profiling data is not available, compile lean using -D RUNTIME_STATS=ON`. The Rust runtime currently does not maintain the global allocation statistic counters (`g_num_ctor`, etc.) internally, or they have not been ported/exposed to `lean_io_allocprof` yet.
- **Fix**: To fully port this, the Rust object allocator would need to be instrumented to maintain thread-safe (or thread-local) allocation statistics, and `lean_io_allocprof` would need to be updated to compute the diff and print it instead of hardcoding the unavailability message.
