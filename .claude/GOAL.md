# Cargo-Only Lean Runtime and Generated Code

## Summary

Move Lean to a Rust/Cargo distribution model: no source .h/C++ compatibility surface, no .a/.o/.dynlib Lean module pipeline, and no direct extern "C" imports in Lean-owned Rust crates. Toolchains (next toolchain will be /home/srghma/.elan/toolchains/leanprover--lean4---v5.0.0) ship Rust crates/rlibs, and users must have Cargo installed.

## Key Changes

- Repair the current compile break first by reverting invalid use crate::lean_... imports where the target symbol is generated Lean code, but only as a short-lived bootstrap step.
  - Do not keep this as the final architecture.
  - Restore buildability, remove duplicate/broken edits, and compare behavior with origin-master-src when runtime semantics are unclear.

- Split crates so Rust dependencies are acyclic:
  - lean_runtime_core: pure Rust runtime/kernel primitives, object model, alloc/refcount/task logic.
  - lean_runtime_sysdeps: wrappers around Cargo system crates such as libuv-sys and gmp-mpfr-sys; Lean-owned crates do not declare raw foreign imports.
  - lean_generated_abi: shared object/layout/helper API used by EmitRust output.
  - Generated crates: lean_init, lean_std, lean_lean, lean_lake.
  - lean_shell / executables depend on generated crates plus runtime core.

- Replace remaining C dependency imports:
  - GMP direct extern "C" declarations become calls through gmp-mpfr-sys.
  - libuv direct declarations become calls through libuv-sys.
  - Platform C APIs are migrated later to Rust crates or std APIs; while migrating, isolate them in lean_runtime_sysdeps.
  - No Lean-owned module should manually declare third-party symbols.

- Change EmitRust output:
  - Emit package modules into Cargo crate source trees instead of standalone Rust files linked like C outputs.
  - Cross-module calls become normal Rust imports between generated crates.
  - Generated code imports runtime helpers through lean_runtime_core / lean_generated_abi, not extern "C".
  - Initializers/finalizers become normal Rust functions and registry calls, not exported C symbols.

- Replace Lake/leanc build flow:
  - Lake invokes Cargo for Lean packages targeting Rust.
  - Toolchain install includes crate sources or prebuilt rlibs under the elan toolchain directory.
  - leanc Rust mode becomes a Cargo/rustc wrapper only for compatibility; it should not produce C objects or static archives.
  - Remove generated lean.h from the final target; tests that include it must be rewritten to Rust FFI/package examples or removed.

## Test Plan

- Bootstrap repair:
  - cargo check --manifest-path src/rust/Cargo.toml --package lean_runtime
  - make -C build/release lean_runtime_rust lean -j"$(nproc)"
  - Run 3-5 focused tests covering shell startup, kernel/type-checker, IO/task/libuv, and generated Rust execution.

- Migration validation:
  - Build lean_init, lean_std, lean_lean, lean_lake with Cargo.
  - Assert no Lean-owned .rs file contains direct third-party extern "C" import blocks.
  - Assert fd "\\.h$" ./src is empty and Lean stdlib build emits no .o, .a, or shared module artifacts in the Rust path.
  - Run focused Lake/package tests using Cargo-backed builds.

## Assumptions

- Users installing future Lean toolchains are allowed to require Cargo.
- extern "C" inside upstream crates like libuv-sys and gmp-mpfr-sys is acceptable; Lean-owned code should not declare those imports manually.
- Public C/C++ compatibility is intentionally dropped for this Rust-only backend.
- Any semantic porting ambiguity must be checked against origin-master-src.
