// lean_box_float32
// lean_box_uint32
// lean_box_uint64
// lean_box_usize

use crate::{
    datatypes::{LEAN_MAX_CTOR_TAG, LeanObject},
    lean_is_scalar::lean_is_scalar_bool,
    lean_unbox::lean_unbox,
    runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic_out_of_memory,
};
use libmimalloc_sys as mi;

// NOT IN EmitRust; here because it is used in `lean_alloc_ctor`, `lean_box_float`, `lean_box_float32`, `lean_box_uint32`, and 3 more EmitRust functions.
#[inline]
pub unsafe fn lean_alloc_small_object(sz: usize) -> *mut LeanObject {
    unsafe {
        let sz = sz.div_ceil(8) * 8;
        let mem = mi::mi_malloc_small(sz);
        if mem.is_null() {
            lean_internal_panic_out_of_memory();
        }
        let o = mem as *mut LeanObject;
        (*o).cs_size = sz as u16;
        o
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_ctor`, `lean_box_float`, `lean_box_float32`, `lean_box_uint32`, and 3 more EmitRust functions.
#[inline]
pub unsafe fn lean_alloc_ctor_memory(sz: usize) -> *mut LeanObject {
    let sz1 = sz.div_ceil(8) * 8;
    let r = unsafe { lean_alloc_small_object(sz1) };
    if sz1 > sz {
        let end = unsafe { (r as *mut u8).add(sz1) as *mut usize };
        unsafe { end.sub(1).write(0) };
    }
    r
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_box_float`, `lean_box_float32`, and 37 more EmitRust functions.
#[inline]
pub unsafe fn lean_ptr_tag(obj: *mut LeanObject) -> u8 {
    if lean_is_scalar_bool(obj) {
        lean_unbox(obj) as u8
    } else {
        (*obj).tag
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_box_float`, `lean_box_float32`, and 32 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_obj_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe {
        debug_assert!(lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG);
        (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut *mut LeanObject
    }
}
