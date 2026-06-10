// Port of src/library/print.cpp to Rust.
//
// print.cpp exports two LEAN_EXPORT symbols (initialize_print / finalize_print),
// one extern "C" LEAN_EXPORT function (lean_expr_dbg_to_string), and one
// non-exported function called from C++ (init_default_print_fn).
//
// The print_expr_fn struct and all helpers operate on C++ lean::expr / lean::name
// value types and stay in C++.  initialize_print / finalize_print: when
// libleancpp.a is linked (lean_use_libleancpp) those symbols are provided by C++
// directly; otherwise the no-op stubs in lib.rs satisfy the extern block.

mod library_print_impl {
    use super::*;
    use std::os::raw::c_char;

    /// `lean_expr_dbg_to_string (e : @& Expr) : String`
    ///
    /// Converts a Lean Expr object to a debug string.
    /// runtime_compat_cxx.rs exports `lean_cxx_expr_dbg_to_string` as an alias
    /// for this function (for C++ code to call). This is the canonical definition;
    /// do NOT call `lean_cxx_expr_dbg_to_string` here to avoid circular calls.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_dbg_to_string(_e: *mut LeanObject) -> *mut LeanObject {
        // TODO: implement proper Lean Expr → debug string conversion in Rust.
        // For now return a placeholder so the debug path doesn't infinite-loop.
        crate::lean_mk_string(b"(expr)\0".as_ptr() as *const c_char)
    }
}
