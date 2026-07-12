use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_ctor_get_uint64::lean_ctor_get_uint64, lean_is_scalar::lean_is_scalar,
        lean_obj_tag::lean_obj_tag,
    },
};

#[inline]
pub unsafe fn level_data(level: *const LeanObject) -> u64 {
    if lean_is_scalar(level) {
        return 2221u64;
    }
    let num_fields = match lean_obj_tag(level) {
        1 | 4 | 5 => 1,
        2 | 3 => 2,
        _ => 1,
    };
    lean_ctor_get_uint64(
        level,
        (core::mem::size_of::<*mut LeanObject>() * num_fields) as u32,
    )
}
