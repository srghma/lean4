// Port of src/library/num.cpp to Rust.
//
// num.cpp operates on C++ lean::expr / lean::mpz / lean::name types and has
// exactly two LEAN_EXPORT symbols: initialize_num / finalize_num (both no-ops
// in the original).  All other functions are internal C++ helpers called from
// C++ submodules.
// When libleancpp.a is linked (lean_use_libleancpp), those symbols are provided
// by C++ directly; otherwise the no-op stubs in lib.rs satisfy the extern block.
mod library_num_impl {}
