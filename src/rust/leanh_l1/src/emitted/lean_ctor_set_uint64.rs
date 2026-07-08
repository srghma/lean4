use crate::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_ctor_set_uint64(obj: *mut LeanObject, offset: usize, value: u64) {
    (obj.add(1) as *mut u8)
        .add(offset)
        .cast::<u64>()
        .write(value);
}
