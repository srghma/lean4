use crate::datatypes::LeanObject;

#[inline(always)]
pub unsafe fn lean_ctor_set_usize(obj: *mut LeanObject, idx: usize, v: usize) {
    let byte_offset = idx * core::mem::size_of::<*mut LeanObject>();
    // (obj.add(1) as *mut u8)
    //     .add(byte_offset)
    //     .cast::<usize>()
    //     .write_unaligned(v); // more safe, but wont throw, so for maximum safety I use the one below
    let ptr = (obj.add(1) as *mut u8).add(byte_offset).cast::<usize>();
    assert_eq!((ptr as usize) % core::mem::align_of::<usize>(), 0);
    ptr.write(v);
}

// #[inline]
// pub unsafe fn lean_ctor_set_usize(obj: *mut LeanObject, idx: usize, value: usize) {
//     unsafe { *((lean_ctor_obj_cptr(obj).add(idx)) as *mut usize) = value } // like in cpp, but
//     not safe
// }
