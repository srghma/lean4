# Comparison: sstream

## Files

- C++ Header: `runtime/sstream.h`
- Rust Implementation: N/A

## Overview of C++ Implementation

Provides a simple `lean::sstream` class that wraps `std::ostringstream`. It exposes a convenient `operator<<` template and a `str()` method to retrieve the accumulated `std::string`. It was used for string formatting throughout the C++ codebase.

## Corresponding Rust Implementation

There is no direct Rust translation for `sstream`. In the Rust codebase, standard Rust string formatting (`format!`, `write!`, `String::push_str`) is used natively, eliminating the need for a C++-style stream wrapper.

### Dependencies (Third-party vs Native Rust)

- Rust uses its native `std::fmt` and `String` libraries.
