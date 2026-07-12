use leanh_l1::{
    datatypes::{LeanObject, LeanObjectTag},
    emitted::lean_object_tag::lean_object_tag,
};

use crate::r#priv::{
    lean_array_data_byte_size::lean_array_data_byte_size,
    lean_closure_data_byte_size::lean_closure_data_byte_size,
    lean_sarray_data_byte_size::lean_sarray_data_byte_size,
    lean_string_data_byte_size::lean_string_data_byte_size,
};

pub unsafe fn lean_object_data_byte_size(o: *const LeanObject) -> usize {
    match lean_object_tag(o) {
        LeanObjectTag::Array => lean_array_data_byte_size(o),
        LeanObjectTag::ScalarArray => lean_sarray_data_byte_size(o),
        LeanObjectTag::String => lean_string_data_byte_size(o),
        LeanObjectTag::Closure => lean_closure_data_byte_size(o),
        LeanObjectTag::Ctor(_) | LeanObjectTag::StructArray => (*o).cs_size as usize,
        tag => panic!("unexpected LeanObjectTag in lean_object_data_byte_size: {tag:?}"),
    }
}
