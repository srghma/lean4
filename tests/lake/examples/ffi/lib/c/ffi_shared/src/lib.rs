use core::ffi::{c_char, c_void};

type LeanObj = *mut c_void;

extern "C" {
    fn lean_mk_string(s: *const c_char) -> LeanObj;
    fn lean_io_result_mk_ok(a: LeanObj) -> LeanObj;
}

#[no_mangle]
pub unsafe extern "C" fn my_lean_fun() -> LeanObj {
    let result = lean_mk_string(b"hi\0".as_ptr().cast());
    lean_io_result_mk_ok(result)
}
