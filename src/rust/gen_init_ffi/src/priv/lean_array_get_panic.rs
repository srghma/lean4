use leanh_l1::datatypes::LeanObject;

use crate::r#priv::{
    lean_mk_ascii_string_unchecked::lean_mk_ascii_string_unchecked, lean_panic_fn::lean_panic_fn,
};

pub unsafe fn lean_array_get_panic(def_val: *mut LeanObject) -> *mut LeanObject {
    lean_panic_fn(
        def_val,
        lean_mk_ascii_string_unchecked(c"Error: index out of bounds".as_ptr()),
    )
}
