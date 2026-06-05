# Comparison: kernel_exception

## Files

- C++ Header: `kernel/kernel_exception.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Defines a hierarchy of C++ exception classes representing various Lean kernel errors (e.g., `unknown_constant_exception`, `definition_type_mismatch_exception`, `type_expected_exception`). It includes a critical helper function, `catch_kernel_exceptions`, which catches these C++ exceptions and translates them into Lean's `Except Kernel.Exception T` inductive datatype format using Lean runtime constructor macros (`mk_cnstr`).

## Corresponding Rust Implementation

No direct Rust translation. The C++ `catch_kernel_exceptions` helper is heavily used by the FFI boundary to ensure that any C++ exceptions thrown by the legacy kernel are correctly boxed and safely returned to Lean code as `Except.error`. Rust does not use C++ exceptions, and operations ported to Rust return standard `Result` types instead.
