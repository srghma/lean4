// Port of src/library/formatter.cpp to Rust.
//
// formatter.cpp has two responsibilities:
//   1. A global `g_print` function pointer (set_print_fn / operator<<)
//      — this is a C++ std::function capturing a Rust-inaccessible C++ expr&
//      reference, so we delegate to a C++ shim.
//   2. initialize_formatter / finalize_formatter — trivial; we own them.

mod runtime_formatter_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_initialize_formatter();
        fn lean_cxx_finalize_formatter();
    }

    #[export_name = "_ZN4lean20initialize_formatterEv"]
    pub extern "C" fn initialize_formatter() {
        unsafe { lean_cxx_initialize_formatter() }
    }

    #[export_name = "_ZN4lean18finalize_formatterEv"]
    pub extern "C" fn finalize_formatter() {
        unsafe { lean_cxx_finalize_formatter() }
    }
}
