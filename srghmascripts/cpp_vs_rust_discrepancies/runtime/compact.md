# `runtime/compact` (`runtime/compact.h` and `runtime/compact.cpp`)

## Location of corresponding Rust implementation
A minimal stub exists in `src/rust/lean_runtime/src/runtime_compact.rs`.

## Discrepancies and issues
- **Algorithm & Approach**: The C++ implementation contains the `lean::object_compactor` and `lean::compacted_region`, the complex core of Lean's object serialization system (used for creating `.olean` files). It walks an object graph, deep-copies objects into a contiguous buffer, creates relative cross-region and internal pointers, and handles the relocation of closure function pointers across dynamic libraries.
- **Rust Port Status**: The Rust codebase **does not** contain a full port of `object_compactor`. `runtime_compact.rs` only defines a dummy `RustCompactedRegion` struct and simple shims for `lean_compacted_region_is_memory_mapped`, `lean_compacted_region_size`, and `lean_compacted_region_free`.
- **Reasoning**: The core compactor logic was either left in C++ or moved up the stack into Lean code itself (or perhaps handled by Lake/another mechanism for the new Rust runtime). The existing Rust stub merely ensures that the FFI boundaries that accept a `compacted_region` can safely deallocate it.
