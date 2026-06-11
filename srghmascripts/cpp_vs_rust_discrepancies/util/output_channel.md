# Comparison: output_channel

## Files

- C++ Header: `util/output_channel.h`
- Rust Implementation: None

## Overview of C++ Implementation

Defines a class hierarchy `output_channel` wrapping `std::ostream` to allow dynamic reassignment of output streams (e.g., standard output, standard error, files, strings, and a `/dev/null` equivalent).

## Corresponding Rust Implementation

No direct Rust equivalent exists as this is a C++ specific abstraction. In Rust, dynamic dispatch over output streams is natively handled via `Box<dyn std::io::Write>` or `&mut dyn std::fmt::Write`. The standard library provides `std::io::stdout()`, `std::io::stderr()`, `std::fs::File`, and `std::io::sink()` for `/dev/null`, which fulfill all these use-cases organically.

### Dependencies (Third-party vs Native Rust)

- Rust uses its native `std::io` and `std::fmt` ecosystem instead of C++ `<iostream>`.
