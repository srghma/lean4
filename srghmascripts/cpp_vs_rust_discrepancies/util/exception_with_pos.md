# Comparison: exception_with_pos

## Files

- C++ Header: `util/exception_with_pos.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Defines a C++ interface (`exception_with_pos`) extending the base `lean::exception` class with an abstract method `get_pos()` to optionally attach source code position information to exceptions.

## Corresponding Rust Implementation

Rust does not use inheritance for error handling. Lean 4 runtime panics are caught and tracked using `runtime_object_panic.rs`, and language-level exceptions are handled purely in Lean as monadic values (`Except` or `EIO`). Positional information for errors is attached to diagnostic messages directly in the Lean compiler logic.
