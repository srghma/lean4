# `runtime/alloc` (`runtime/alloc.h` and `runtime/alloc.cpp`)

## Location of corresponding Rust implementation
The custom small allocator and heartbeat logic are fully ported in `src/rust/lean_runtime/src/runtime_alloc.rs`.

## Discrepancies and issues
- **Algorithm & Approach**: The C++ code implemented a thread-local, slab-based custom allocator for small objects, grouping allocations into 8 KB pages and 8 MB segments to bypass the system allocator (`malloc`) overhead. It also incremented a heartbeat counter on every small allocation to support deterministic timeouts. 
- **Rust Port**: `runtime_alloc.rs` provides an exact 1:1 translation of this logic when compiled with `cfg(feature = "small_allocator")`. It replicates the page/segment structure, the thread-local caching, and the export/import protocols for cross-thread deallocation. When the feature is disabled, it transparently falls back to `libc::malloc` and `libc::free` (or `mimalloc` wrappers) and disables the heartbeat tracking.
- **Memory Model**: Identical. Uses `std::alloc::alloc_zeroed` to grab large chunks of memory for segments instead of `mmap`/`VirtualAlloc`, but otherwise identical.
