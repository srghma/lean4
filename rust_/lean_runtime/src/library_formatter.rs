// Port of src/library/formatter.cpp to Rust.
//
// formatter.cpp has two responsibilities:
//   1. A global `g_print` function pointer (set_print_fn / operator<<)
//      — this is a C++ std::function capturing a Rust-inaccessible C++ expr&
//      reference, so we delegate to a C++ shim.
//   2. initialize_formatter / finalize_formatter — when libleancpp.a is linked
//      (lean_use_libleancpp) those symbols are provided by C++ directly;
//      otherwise the no-op stubs in lib.rs satisfy the extern block.
mod runtime_formatter_impl {}
