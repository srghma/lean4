// Port of src/library/expr_lt.cpp to Rust.
//
// The C++ implementation uses a structural expression order.  The Rust runtime
// needs an in-process strict total order for expression-keyed maps and caches,
// and must not delegate through the old C++ compatibility symbols because they
// are aliases back to these exports.

mod runtime_expr_lt_impl {
    use super::*;

    unsafe fn expr_order_key(o: *mut LeanObject) -> (u8, usize) {
        (lean_obj_tag(o), o as usize)
    }

    unsafe fn expr_ptr_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
        if a == b {
            0
        } else {
            (expr_order_key(a) < expr_order_key(b)) as u8
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_quick_lt(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        expr_ptr_lt(a, b)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_lt(
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> u8 {
        expr_ptr_lt(a, b)
    }
}
