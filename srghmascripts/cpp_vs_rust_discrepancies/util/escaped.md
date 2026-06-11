# Comparison: escaped

## Files

- C++ Implementation: `util/escaped.cpp`
- C++ Header: `util/escaped.h`
- Rust Implementation: None

## Overview of C++ Implementation

Provides a small `lean::escaped` helper class overloading `std::ostream::operator<<`. It aids in formatting and printing strings by escaping double quotes (`"`) and optionally removing trailing newlines and indenting embedded newlines.

## Corresponding Rust Implementation

This file has no corresponding Rust implementation. Formatting and escaping are typically handled natively in Rust using `std::fmt` traits (e.g., `Debug` format `{:?}` automatically escapes strings) or standard string manipulation functions, making this C++ specific abstraction unnecessary.

### Dependencies (Third-party vs Native Rust)

- Rust uses its native `std::fmt` ecosystem instead of C++ `<iostream>`.
