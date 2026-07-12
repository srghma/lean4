use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_get::lean_ctor_get,
        lean_ctor_set::lean_ctor_set, lean_inc::lean_inc,
        lean_object_tag::lean_object_tag,
    },
};

use crate::r#priv::{
    lean_object_byte_size::lean_object_byte_size, sharecommon_data::ShareCommonFn,
    sharecommon_fn_push_child::sharecommon_fn_push_child, sharecommon_fn_save::sharecommon_fn_save,
};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:75-108

pub(crate) unsafe fn sharecommon_fn_visit_ctor(this: &mut ShareCommonFn, a: *mut LeanObject) {
    this.children.clear();
    let num_objs = (*a).other as usize;
    let mut missing_child = false;
    for i in 0..num_objs {
        if !sharecommon_fn_push_child(this, lean_ctor_get(a, i as u32)) {
            missing_child = true;
        }
    }
    if missing_child {
        return;
    }
    let tag = match lean_object_tag(a) {
        leanh_l1::datatypes::LeanObjectTag::Ctor(tag) => tag,
        other => panic!("unexpected LeanObjectTag in sharecommon_fn_visit_ctor: {other:?}"),
    };
    let sz = lean_object_byte_size(a);
    let scalar_offset =
        core::mem::size_of::<LeanObject>() + num_objs * core::mem::size_of::<*mut LeanObject>();
    let scalar_sz = sz.saturating_sub(scalar_offset);
    let new_a = lean_alloc_ctor(tag, num_objs as u32, scalar_sz as u32);
    for i in 0..num_objs {
        let child = this.children[i];
        lean_inc(child);
        lean_ctor_set(new_a, i as u32, child);
    }
    if scalar_sz > 0 {
        let dest = (new_a as *mut u8).add(scalar_offset);
        let src = (a as *const u8).add(scalar_offset);
        libc::memcpy(dest.cast(), src.cast(), scalar_sz);
    }
    sharecommon_fn_save(this, a, new_a);
}
