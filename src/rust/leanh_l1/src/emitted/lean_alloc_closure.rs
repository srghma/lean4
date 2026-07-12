use std::ffi::c_void;

use crate::{
    datatypes::{LeanClosureObject, LeanObject, LeanObjectTag},
    r#priv::lean_alloc_object::lean_alloc_object,
};

#[inline(always)]
pub unsafe fn lean_alloc_closure(fun: *mut c_void, arity: u32, num_fixed: u32) -> *mut LeanObject {
    debug_assert!(arity > 0);
    debug_assert!(num_fixed < arity);
    let byte_size = core::mem::size_of::<LeanClosureObject<0>>()
        .checked_add(
            core::mem::size_of::<*mut LeanObject>()
                .checked_mul(num_fixed as usize)
                .expect("closure allocation overflow"),
        )
        .expect("closure allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanClosureObject<0>;
    (*obj).m_header.rc = 1;
    (*obj).m_header.other = 0;
    (*obj).m_header.set_tag(LeanObjectTag::Closure);
    // (*obj).m_header.cs_size = 0;
    (*obj).m_fun = fun;
    (*obj).m_arity = arity as u16;
    (*obj).m_num_fixed = num_fixed as u16;
    obj as *mut LeanObject
}
