/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the object size helpers from src/runtime/object.cpp.

mod runtime_object_size_impl {
    use crate::datatypes::LeanObject;
    use crate::{
        lean_array_byte_size, lean_closure_byte_size, lean_ptr_tag, lean_sarray_byte_size,
        lean_small_object_size, lean_string_byte_size,
    };
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use leanh::datatypes::LeanObjectTag;

    pub unsafe fn lean_object_byte_size(o: *const LeanObject) -> usize {
        match LeanObjectTag::from_u8(lean_ptr_tag(o)) {
            LeanObjectTag::Array => lean_array_byte_size(o),
            LeanObjectTag::ScalarArray => lean_sarray_byte_size(o),
            LeanObjectTag::String => lean_string_byte_size(o),
            LeanObjectTag::Closure => lean_closure_byte_size(o),
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
