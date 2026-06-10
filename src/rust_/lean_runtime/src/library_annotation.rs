// Port of src/library/annotation.cpp to Rust.
//
// annotation.cpp operates on C++ `lean::name`, `lean::expr`, `lean::kvmap` types
// which are complex C++ value types.  The Rust port delegates all operations
// to thin C++ shims (annotation_shims.cpp) and exposes the same `extern "C"
// LEAN_EXPORT` surface as the original.
// When libleancpp.a is linked (lean_use_libleancpp), initialize_annotation /
// finalize_annotation are provided by C++ directly; otherwise the no-op stubs
// in lib.rs satisfy the extern block in lib.rs.
mod runtime_annotation_impl {}
