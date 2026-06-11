// Port of src/library/annotation.cpp to Rust.
//
// annotation.cpp operates on C++ `lean::name`, `lean::expr`, `lean::kvmap` types
// which are complex C++ value types.  The Rust port delegates all operations
// to thin C++ shims (annotation_shims.cpp) and exposes the same `extern "C"
// LEAN_EXPORT` surface as the original.

mod runtime_annotation_impl {
    use super::*;
    use core::ffi::c_void;

    // All annotation operations are implemented in C++ and called from Lean-generated code
    // through the lean_object ABI.  We forward the init/finalize pair and let the C++ side
    // own the global state (g_annotation_maps, g_have, g_show, etc.).

    extern "C" {
        fn lean_cxx_initialize_annotation();
        fn lean_cxx_finalize_annotation();
    }

    #[export_name = "_ZN4lean21initialize_annotationEv"]
    pub extern "C" fn initialize_annotation() {
        unsafe { lean_cxx_initialize_annotation() }
    }

    #[export_name = "_ZN4lean19finalize_annotationEv"]
    pub extern "C" fn finalize_annotation() {
        unsafe { lean_cxx_finalize_annotation() }
    }
}
