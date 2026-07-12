use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_ctor_get_uint64::lean_ctor_get_uint64, lean_obj_tag::lean_obj_tag},
};

#[inline]
pub unsafe fn expr_data(expr: *const LeanObject) -> u64 {
    let num_fields = match lean_obj_tag(expr) {
        0 | 1 | 2 | 3 | 9 => 1,
        4 | 5 | 10 => 2,
        6 | 7 | 11 => 3,
        8 => 4,
        _ => 1,
    };
    lean_ctor_get_uint64(
        expr,
        (core::mem::size_of::<*mut LeanObject>() * num_fields) as u32,
    )
}
