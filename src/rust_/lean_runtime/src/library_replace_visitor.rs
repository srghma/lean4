// Port of src/library/replace_visitor.cpp to Rust.
//
// replace_visitor is an abstract C++ base class with virtual methods.
// Its entire surface is intra-C++ (subclasses override visit_* methods);
// there are no LEAN_EXPORT extern "C" symbols.  Subclasses (eta_beta_reduce_fn,
// etc.) live in util.cpp and other library files that also stay in C++.
//
// Nothing to export from Rust for this file.  The entry is kept so the
// module graph stays complete.

mod library_replace_visitor_impl {
    // No exported extern "C" symbols.
}
