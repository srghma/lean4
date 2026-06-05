# Comparison: null_ostream

## Files

- C++ Header: `util/null_ostream.h`
- Rust Implementation: None

## Overview of C++ Implementation

Defines a `lean::null_streambuf` inheriting from `std::streambuf` that simply drops all characters written to it (like `/dev/null`).

## Corresponding Rust Implementation

There is no Rust equivalent because Rust natively provides `std::io::sink()` for this exact purpose within the standard library.

### Dependencies (Third-party vs Native Rust)

- `std::io::sink()` replaces `null_streambuf`.
