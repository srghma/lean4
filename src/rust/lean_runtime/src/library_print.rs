// Port of src/library/print.cpp to Rust.
//
// print.cpp exports two LEAN_EXPORT symbols (initialize_print / finalize_print),
// one extern "C" LEAN_EXPORT function (lean_expr_dbg_to_string), and one
// non-exported function called from C++ (init_default_print_fn).
//
// The print_expr_fn struct and all helpers operate on C++ lean::expr / lean::name
// value types and stay in C++.  Rust owns the three exported symbols.

mod library_print_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_initialize_print();
        fn lean_cxx_finalize_print();
        fn lean_cxx_expr_dbg_to_string(e: *mut LeanObject) -> *mut LeanObject;
    }

    #[export_name = "_ZN4lean16initialize_printEv"]
    pub extern "C" fn initialize_print() {
        unsafe { lean_cxx_initialize_print() }
    }

    #[export_name = "_ZN4lean14finalize_printEv"]
    pub extern "C" fn finalize_print() {
        unsafe { lean_cxx_finalize_print() }
    }

    /// `lean_expr_dbg_to_string (e : @& Expr) : String`
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_dbg_to_string(e: *mut LeanObject) -> *mut LeanObject {
        lean_cxx_expr_dbg_to_string(e)
    }

}
