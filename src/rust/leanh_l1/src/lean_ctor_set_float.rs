use crate::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_ctor_set_float(obj: *mut LeanObject, byte_offset: usize, value: f64) {
    (obj.add(1) as *mut u8)
        .add(byte_offset)
        .cast::<f64>()
        .write_unaligned(value);

    // unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *mut f64) = value }
}
