# `runtime/optional` (`runtime/optional.h`)

## Location of corresponding Rust implementation
No corresponding Rust file exists. The C++ `lean::optional` was a custom polyfill for `std::optional` (as C++14 didn't have it) and included optimizations to reuse the null state of smart pointers to save space.

## Discrepancies and issues
In Rust, this concept is completely replaced by the standard library's `Option<T>`. Rust's `Option` natively includes the "null pointer optimization" so that `Option<Box<T>>`, `Option<&T>`, and `Option<NonNull<T>>` are guaranteed to have the exact same size as the underlying pointer, providing the exact same memory-saving behavior natively without macro hacks. No bespoke optional implementation is required.
