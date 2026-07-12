use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::level_data::level_data;

const LEVEL_DATA_HAS_PARAM_SHIFT: u32 = 33;

#[inline]
pub unsafe fn lean_level_has_param(level: *const LeanObject) -> bool {
    if leanh_l1::emitted::lean_is_scalar::lean_is_scalar(level) {
        false
    } else {
        ((level_data(level) >> LEVEL_DATA_HAS_PARAM_SHIFT) & 1) != 0
    }
}

pub use lean_level_has_param as level_has_param;
