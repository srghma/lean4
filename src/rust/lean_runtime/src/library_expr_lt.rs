// Port of src/library/expr_lt.cpp to Rust.
//
// `is_lt` and `is_lt_no_level_params` operate on opaque C++ `lean::expr` /
// `lean::level` value types.  We port the two exported `extern "C"` functions
// (`lean_expr_quick_lt` and `lean_expr_lt`) by delegating to C++ shims, and
// expose clean Rust wrappers.  The internal `is_lt` / `is_lt_no_level_params`
// logic stays in C++ because it pattern-matches on C++ sum types.

mod runtime_expr_lt_impl {
    use super::*;

    extern "C" {
        /// C++ `lean_expr_quick_lt` — uses hash for fast ordering.
        fn lean_cxx_expr_quick_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8;
        /// C++ `lean_expr_lt` — full ordering without hash shortcuts.
        fn lean_cxx_expr_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_quick_lt(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        lean_cxx_expr_quick_lt(a, b)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_lt(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        lean_cxx_expr_lt(a, b)
    }
}
