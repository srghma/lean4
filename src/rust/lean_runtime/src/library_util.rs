// Port of src/library/util.cpp to Rust.
//
// util.cpp owns two LEAN_EXPORT init/finalize pairs:
//   - initialize_library_util / finalize_library_util  (the main pair)
//   - initialize_bool / finalize_bool                  (sub-pair, called internally)
//
// All other functions operate on C++ lean::expr / lean::name / lean::environment
// value types and are called from C++ submodules — they stay in C++.
// Rust owns the exported init/finalize symbols and delegates to C++ shims.

mod library_util_impl {
    extern "C" {
        fn lean_cxx_initialize_library_util();
        fn lean_cxx_finalize_library_util();
        fn lean_cxx_initialize_bool();
        fn lean_cxx_finalize_bool();
    }

    #[export_name = "_ZN4lean23initialize_library_utilEv"]
    pub extern "C" fn initialize_library_util() {
        unsafe { lean_cxx_initialize_library_util() }
    }

    #[export_name = "_ZN4lean21finalize_library_utilEv"]
    pub extern "C" fn finalize_library_util() {
        unsafe { lean_cxx_finalize_library_util() }
    }

    /// Called internally by initialize_library_util; also exported so any
    /// direct callers can link without changes.
    #[export_name = "_ZN4lean15initialize_boolEv"]
    pub extern "C" fn initialize_bool() {
        unsafe { lean_cxx_initialize_bool() }
    }

    #[export_name = "_ZN4lean13finalize_boolEv"]
    pub extern "C" fn finalize_bool() {
        unsafe { lean_cxx_finalize_bool() }
    }
}
