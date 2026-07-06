/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the object size helpers from src/runtime/object.cpp.

mod runtime_object_size_impl {
    use crate::*;

    const LEAN_ARRAY_TAG: u8 = 246; // duplicate in src/rust/leanh/src/datatypes.rs at line 157 (🔁)
    const LEAN_SCALAR_ARRAY_TAG: u8 = 248; // duplicate in src/rust/leanh/src/datatypes.rs at line 159 (🔁)
    const LEAN_STRING_TAG: u8 = 249; // duplicate in src/rust/leanh/src/datatypes.rs at line 160 (🔁)
    const LEAN_CLOSURE_TAG: u8 = 245; // duplicate in src/rust/leanh/src/datatypes.rs at line 156 (🔁)

    #[inline]
    unsafe fn lean_small_object_size(o: *mut LeanObject) -> usize {
        (*o).cs_size as usize
    }

    #[inline]
    unsafe fn lean_array_byte_size(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 36 (🔁)
        let array = o as *const LeanArrayObject;
        core::mem::size_of::<LeanArrayObject>()
            + core::mem::size_of::<*mut LeanObject>() * (*array).capacity
    }

    #[inline]
    unsafe fn lean_array_data_byte_size(o: *mut LeanObject) -> usize {
        let array = o as *const LeanArrayObject;
        core::mem::size_of::<LeanArrayObject>()
            + core::mem::size_of::<*mut LeanObject>() * (*array).size
    }

    #[inline]
    unsafe fn lean_sarray_byte_size(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 197 (🔁)
        let array = o as *const LeanScalarArray;
        core::mem::size_of::<LeanScalarArray>() + (*o).other as usize * (*array).capacity
    }

    #[inline]
    unsafe fn lean_sarray_data_byte_size(o: *mut LeanObject) -> usize {
        let array = o as *const LeanScalarArray;
        core::mem::size_of::<LeanScalarArray>() + (*o).other as usize * (*array).size
    }

    #[inline]
    unsafe fn lean_string_byte_size(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 206 (🔁)
        let string = o as *const LeanStringObject;
        core::mem::size_of::<LeanStringObject>() + (*string).capacity
    }

    #[inline]
    unsafe fn lean_string_data_byte_size(o: *mut LeanObject) -> usize {
        let string = o as *const LeanStringObject;
        core::mem::size_of::<LeanStringObject>() + (*string).size
    }

    #[inline]
    unsafe fn lean_closure_byte_size(o: *mut LeanObject) -> usize { // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 70 (🔁)
        let closure = o as *const LeanClosureObject;
        core::mem::size_of::<LeanClosureObject>()
            + core::mem::size_of::<*mut LeanObject>() * (*closure).num_fixed as usize
    }

    pub unsafe fn lean_object_byte_size(o: *mut LeanObject) -> usize {
        match lean_ptr_tag(o) {
            LEAN_ARRAY_TAG => lean_array_byte_size(o),
            LEAN_SCALAR_ARRAY_TAG => lean_sarray_byte_size(o),
            LEAN_STRING_TAG => lean_string_byte_size(o),
            LEAN_CLOSURE_TAG => lean_closure_byte_size(o),
            _ => {
                if (*o).cs_size == 0 {
                    lean_small_object_size(o)
                } else {
                    (*o).cs_size as usize
                }
            }
        }
    }

    pub unsafe fn lean_object_data_byte_size(o: *mut LeanObject) -> usize {
        match lean_ptr_tag(o) {
            LEAN_ARRAY_TAG => lean_array_data_byte_size(o),
            LEAN_SCALAR_ARRAY_TAG => lean_sarray_data_byte_size(o),
            LEAN_STRING_TAG => lean_string_data_byte_size(o),
            LEAN_CLOSURE_TAG => lean_closure_byte_size(o),
            _ => {
                if (*o).cs_size == 0 {
                    lean_small_object_size(o)
                } else {
                    (*o).cs_size as usize
                }
            }
        }
    }
}
