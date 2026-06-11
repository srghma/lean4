# Comparison: lean_js

## Files

- C++ Implementation: `shell/lean_js.cpp`
- Rust Implementation: N/A

## Overview of C++ Implementation

Contains bindings for compiling the Lean 3/4 frontend to JavaScript via Emscripten (`initialize_emscripten`, `emscripten_process_request`). It sets up an environment, IO state, and an in-memory language server for processing requests from JS.

## Corresponding Rust Implementation

No direct Rust port exists in `lean_runtime`. Emscripten bindings for the language server and parser are largely deprecated or replaced by modern WebAssembly targets and Lean's own language server implementation in Lean code.
