// Port of src/library/num.cpp to Rust.
//
// num.cpp operates on C++ lean::expr / lean::mpz / lean::name types and has
// exactly two LEAN_EXPORT symbols: initialize_num / finalize_num (both no-ops
// in the original).  All other functions are internal C++ helpers called from
// C++ submodules.

mod library_num_impl {
    extern "C" {
        fn lean_cxx_initialize_num();
        fn lean_cxx_finalize_num();
    }

    #[export_name = "_ZN4lean14initialize_numEv"]
    pub extern "C" fn initialize_num() {
        unsafe { lean_cxx_initialize_num() }
    }

    #[export_name = "_ZN4lean12finalize_numEv"]
    pub extern "C" fn finalize_num() {
        unsafe { lean_cxx_finalize_num() }
    }
}
