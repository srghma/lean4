use crate::{
    datatypes::{LeanMpzObject, LeanObject, LeanObjectTag},
    emitted::lean_object_tag::lean_object_tag,
    r#priv::{
        lean_array_byte_size::lean_array_byte_size, lean_closure_byte_size::lean_closure_byte_size,
        lean_dealloc::lean_dealloc, lean_free_small_object::lean_free_small_object,
        lean_sarray_byte_size::lean_sarray_byte_size, lean_string_byte_size::lean_string_byte_size,
    },
};

pub unsafe fn lean_free_object(o: *mut LeanObject) {
    match lean_object_tag(o) {
        LeanObjectTag::Array => lean_dealloc(o, lean_array_byte_size(o)),
        LeanObjectTag::ScalarArray => lean_dealloc(o, lean_sarray_byte_size(o)),
        LeanObjectTag::String => lean_dealloc(o, lean_string_byte_size(o)),
        LeanObjectTag::Closure => lean_dealloc(o, lean_closure_byte_size(o)),
        LeanObjectTag::Mpz => {
            let mpz = core::ptr::addr_of_mut!((*(o as *mut LeanMpzObject)).m_value);
            gmp_mpfr_sys::gmp::mpz_clear(mpz);
            lean_free_small_object(o);
        }
        _ => lean_free_small_object(o),
    }
}
