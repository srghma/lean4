# Comparison: platform

## Files

- C++ Implementation: `runtime/platform.cpp`
- C++ Header: `runtime/platform.h`
- Rust Implementation: `src/rust/lean_runtime/src/lib.rs`

## Overview of C++ Implementation

Exposes system platform metrics and build-time configurations to the Lean runtime/compiler through FFI. It includes checks for pointer sizes (`lean_system_platform_nbits`), OS (`lean_system_platform_windows`, `lean_system_platform_osx`, `lean_system_platform_emscripten`), git hash (`lean_get_githash`), and various build configuration flags (LLVM backend, ASAN, multi-threading, debug, build type) heavily relying on C preprocessor macros (`#if defined(...)`).

## Corresponding Rust Implementation

These functions were directly ported to `src/rust/lean_runtime/src/lib.rs` (around line 2388).

- OS checks utilize native Rust configuration flags, e.g., `cfg!(target_os = "windows")`.
- Pointer size is determined dynamically via `core::mem::size_of::<*const u8>() * 8`.
- Build configurations and git hash are injected using the compile-time `env!` macro, reading variables set by the Cargo `build.rs` script.
- `lean_system_platform_emscripten` was dropped in favor of a `lean_system_platform_target` that returns the explicit target triple string.

### Dependencies (Third-party vs Native Rust)

- Cleanly replaces C++ preprocessor directives (`#if defined`) with Cargo environment variables and Rust `cfg!` macros.

### Other Issues / How to fix them

- `lean_system_platform_emscripten` is no longer provided. this is good because we dont want to support emscripten at this stage
