use leanh_l1::{datatypes::LeanObject, emitted::lean_ctor_get_uint64::lean_ctor_get_uint64};

// Reads the cached hash u64 stored after the 2 lean_object* fields.
// Layout (64-bit): [LeanObject header (8)] [field0 ptr (8)] [field1 ptr (8)] [hash u64 (8)]
#[inline]
pub(crate) unsafe fn lean_name_hash_ptr(n: *mut LeanObject) -> u64 {
    lean_ctor_get_uint64(n, (core::mem::size_of::<*mut LeanObject>() * 2) as u32)
}
