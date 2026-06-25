// Port of src/library/max_sharing.cpp to Rust.
//
// max_sharing_fn operates on C++ lean::expr / lean::level value types with
// identity-based caching (is_eqp).  The logic stays in C++; Rust owns the
// module init pair and exposes it for completeness.  No LEAN_EXPORT symbols
// live in max_sharing.cpp itself, so this file is intentionally minimal.

mod library_max_sharing_impl {
    // No exported extern "C" symbols in the original file.
    // initialize/finalize are not present either; the type is header-only from
    // the Lean module system's perspective.
    //
    // If callers ever need `lean_max_sharing` as a C symbol, add a shim here.
}
