use leanh_l1::{
    datatypes::LeanObject,
    emitted::lean_dec::lean_dec,
    r#priv::{lean_string_cstr::lean_string_cstr, lean_string_size::lean_string_size},
    runtime_object_panic::lean_panic::lean_panic_impl,
};

pub unsafe fn lean_panic_fn(default_val: *mut LeanObject, msg: *mut LeanObject) -> *mut LeanObject {
    let size = lean_string_size(msg).saturating_sub(1);
    let bytes = core::slice::from_raw_parts(lean_string_cstr(msg).cast::<u8>(), size);
    lean_panic_impl(bytes, false);
    lean_dec(msg);
    default_val
}
