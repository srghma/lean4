use leanh_l1::{
    datatypes::{
        LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LeanObject,
    },
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

use crate::r#priv::{
    lean_array_data_byte_size::lean_array_data_byte_size,
    lean_closure_data_byte_size::lean_closure_data_byte_size,
    lean_sarray_data_byte_size::lean_sarray_data_byte_size,
    lean_string_data_byte_size::lean_string_data_byte_size,
};

pub unsafe fn lean_object_data_byte_size(o: *const LeanObject) -> usize {
    match lean_ptr_tag(o) {
        LEAN_ARRAY_TAG => lean_array_data_byte_size(o),
        LEAN_SCALAR_ARRAY_TAG => lean_sarray_data_byte_size(o),
        LEAN_STRING_TAG => lean_string_data_byte_size(o),
        LEAN_CLOSURE_TAG => lean_closure_data_byte_size(o),
        _ => (*o).cs_size as usize,
    }
}
