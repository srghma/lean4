use leanh_l1::{
    datatypes::{LeanObject, LeanObjectTag},
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_get::lean_ctor_get,
        lean_ctor_set::lean_ctor_set,
    },
    emitted::lean_object_tag::lean_object_tag,
};

use crate::r#priv::{
    lean_object_byte_size::lean_object_byte_size,
    sharecommon_quick_check_cache::sharecommon_quick_check_cache,
    sharecommon_quick_data::RustShareCommonQuick, sharecommon_quick_save::sharecommon_quick_save,
    sharecommon_quick_visit::sharecommon_quick_visit,
};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:94-123

pub(crate) unsafe fn sharecommon_quick_visit_ctor(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let r = sharecommon_quick_check_cache(this, a);
    if !r.is_null() {
        return r;
    }
    let num_objs = (*a).other as usize;
    let tag = match lean_object_tag(a) {
        LeanObjectTag::Ctor(tag) => tag as u32,
        other => panic!("unexpected LeanObjectTag in sharecommon_quick_visit_ctor: {other:?}"),
    };
    let sz = lean_object_byte_size(a);
    let scalar_offset =
        core::mem::size_of::<LeanObject>() + num_objs * core::mem::size_of::<*mut LeanObject>();
    let scalar_sz = sz.saturating_sub(scalar_offset);
    let new_a = lean_alloc_ctor(tag, num_objs as u32, scalar_sz as u32);
    for i in 0..num_objs {
        lean_ctor_set(
            new_a,
            i as u32,
            sharecommon_quick_visit(this, lean_ctor_get(a, i as u32)),
        );
    }
    if scalar_sz > 0 {
        let dest = (new_a as *mut u8).add(scalar_offset);
        let src = (a as *const u8).add(scalar_offset);
        libc::memcpy(dest.cast(), src.cast(), scalar_sz);
    }
    sharecommon_quick_save(this, a, new_a)
}
