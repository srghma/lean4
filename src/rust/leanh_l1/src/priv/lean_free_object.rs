use crate::{
    datatypes::{
        LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_MPZ_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG,
        LeanMpzObject, LeanObject,
    },
    r#priv::{
        lean_array_byte_size::lean_array_byte_size, lean_closure_byte_size::lean_closure_byte_size,
        lean_dealloc::lean_dealloc, lean_free_small_object::lean_free_small_object,
        lean_ptr_tag::lean_ptr_tag, lean_sarray_byte_size::lean_sarray_byte_size,
        lean_string_byte_size::lean_string_byte_size,
    },
};

pub unsafe fn lean_free_object(o: *mut LeanObject) {
    match lean_ptr_tag(o) {
        LEAN_ARRAY_TAG => lean_dealloc(o, lean_array_byte_size(o)),
        LEAN_SCALAR_ARRAY_TAG => lean_dealloc(o, lean_sarray_byte_size(o)),
        LEAN_STRING_TAG => lean_dealloc(o, lean_string_byte_size(o)),
        LEAN_CLOSURE_TAG => lean_dealloc(o, lean_closure_byte_size(o)),
        LEAN_MPZ_TAG => {
            let mpz = core::ptr::addr_of_mut!((*(o as *mut LeanMpzObject)).m_value);
            gmp_mpfr_sys::gmp::mpz_clear(mpz);
            lean_free_small_object(o);
        }
        _ => lean_free_small_object(o),
    }
}
