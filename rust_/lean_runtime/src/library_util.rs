// Port of src/library/util.cpp to Rust.
//
// util.cpp owns two LEAN_EXPORT init/finalize pairs:
//   - initialize_library_util / finalize_library_util  (the main pair)
//   - initialize_bool / finalize_bool                  (sub-pair, called internally)
//
// All other functions operate on C++ lean::expr / lean::name / lean::environment
// value types and are called from C++ submodules — they stay in C++.
// When libleancpp.a is linked (lean_use_libleancpp), all four symbols are provided
// by C++ directly; otherwise the no-op stubs in lib.rs satisfy the extern block.
mod library_util_impl {}
