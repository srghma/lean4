use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::level_data::level_data;

const LEVEL_DATA_DEPTH_SHIFT: u32 = 40;

#[inline]
pub unsafe fn lean_level_depth(level: *const LeanObject) -> u32 {
    (level_data(level) >> LEVEL_DATA_DEPTH_SHIFT) as u32
}
