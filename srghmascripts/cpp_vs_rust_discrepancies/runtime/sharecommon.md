# Comparison: sharecommon

## Files

- C++ Implementation: `sharecommon.cpp`
- C++ Header: `sharecommon.h`
- Rust Implementation: `src/rust/lean_runtime/src/runtime_sharecommon.rs`

## Overview of C++ Implementation

Implements "hash-consing" or "maximal sharing" for Lean objects to save memory. Contains functions like `lean_sharecommon_eq`, `lean_sharecommon_hash`, and a few variations of the sharecommon state/function like `sharecommon_quick_fn` and `sharecommon_persistent_fn` to traverse an object graph and deduplicate its components via sets and maps.

## Corresponding Rust Implementation

The Rust implementation is contained in a single file `src/rust/lean_runtime/src/runtime_sharecommon.rs`. It faithfully ports the C++ API with identical FFI functions (`lean_sharecommon_eq`, `lean_sharecommon_hash`, `lean_state_sharecommon`, `lean_sharecommon_quick`, etc.).

## Discrepancies and Issues

### Memory Model

- The Rust version performs raw pointer manipulation and directly writes into array memory slots via `libc::memcpy` and `array_data_ptr.add(i).write(child)` similar to the C++ code, matching the exact required `lean_object` layout.
- The C++ class `sharecommon_persistent_fn` is replaced by an opaque `RustShareCommonPersistent` struct passed over FFI as `*mut c_void`. The lifecycle of this struct is managed explicitly via exported functions (`lean_sharecommon_persistent_create`, `_free`, `_run`, etc.).
- The stateful `lean_state_sharecommon` uses a Rust structure `ShareCommonFn` that handles the depth-first traversal of the object graph.

### Dependencies (Third-party vs Native Rust)

- The C++ code uses `lean::unordered_map` and `lean::unordered_set` (which often have custom allocators or characteristics).
- The Rust code uses the standard library `std::collections::HashMap` and `HashSet`.
- The Rust code uses a custom `IdentityHasher` alongside `BuildHasherDefault`. This is because the keys are `ShareConsNode` pointers that compute their hashes externally using `lean_sharecommon_hash()`. The `IdentityHasher` prevents Rust's default SipHash from double-hashing the pre-computed 64-bit integer, optimizing performance.

### Other Issues / How to fix them

- **MPZ Allocation**: In `visit_mpz`, the C++ code called `alloc_mpz(mpz_value(a))` directly. The Rust code relies on a C++ FFI helper `lean_alloc_mpz_from_mpz` (likely defined in `object.cpp`) since it cannot directly invoke the GMP `mpz` constructors without bridging.
