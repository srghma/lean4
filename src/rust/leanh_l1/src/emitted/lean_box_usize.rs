use crate::{
    datatypes::LeanObject, emitted::lean_alloc_ctor::lean_alloc_ctor,
    emitted::lean_ctor_set_usize::lean_ctor_set_usize,
};

// NOT IN EmitRust; here because it is used in `lean_box_float`, `lean_box_float32`, `lean_box_uint32`, `lean_box_uint64`, and 18 more EmitRust functions.
// #[inline]
// pub unsafe fn lean_ctor_scalar_cptr(obj: *mut LeanObject, offset: usize) -> *mut u8 {
//     unsafe { lean_ctor_obj_cptr(obj).cast::<u8>().add(offset) }
// }
/// Box a `usize` value as a Lean `USize` (= `CompactedRegion`) object.
/// Matches C++ `box_size_t(v)` = `alloc_cnstr(0, 0, sizeof(usize))` + set scalar.
#[inline]
pub unsafe fn lean_box_usize(value: usize) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<usize>() as u32);
        lean_ctor_set_usize(obj, 0, value);
        // ptr::copy_nonoverlapping(
        //     &value as *const usize as *const u8,
        //     lean_ctor_scalar_cptr(obj, 0),
        //     core::mem::size_of::<usize>(),
        // );
        obj
    }
}
