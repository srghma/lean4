use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::level_data::level_data;

const LEVEL_ZERO_HASH: u64 = 2221;

#[inline]
pub unsafe fn lean_level_hash(level: *const LeanObject) -> u32 {
    if leanh_l1::emitted::lean_is_scalar::lean_is_scalar(level) {
        LEVEL_ZERO_HASH as u32
    } else {
        level_data(level) as u32
    }
}

pub use lean_level_hash as level_hash;
