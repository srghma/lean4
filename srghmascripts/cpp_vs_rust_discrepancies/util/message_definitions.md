# Comparison: message_definitions

## Files

- C++ Header: `util/message_definitions.h`
- Rust Implementation: None

## Overview of C++ Implementation

Defines simple struct types (`pos_info`, `pos_range`, `location`) used by the C++ frontend and exception mechanisms to track file lines, columns, and ranges for error reporting.

## Corresponding Rust Implementation

These structs have not been explicitly ported to Rust. File location tracking and error messaging in the Rust bootstrap/FFI layers use standard Rust string formatting and the core `LeanObject` structs where required.

### Dependencies (Third-party vs Native Rust)

- Relied on C++ `std::string` and `std::pair`.
