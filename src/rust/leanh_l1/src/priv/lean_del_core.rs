use crate::{
    datatypes::{LeanObject, LeanObjectTag},
    r#priv::{
        dec_for_del::dec_for_del, lean_ctor_num_objs::lean_ctor_num_objs,
        lean_ctor_obj_cptr::lean_ctor_obj_cptr, lean_del_core_other::lean_del_core_other,
        lean_free_small_object::lean_free_small_object, lean_ptr_tag::lean_ptr_tag,
    },
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_del_core(obj: *mut LeanObject, todo: &mut *mut LeanObject) {
    unsafe {
        let tag = lean_ptr_tag(obj);
        if matches!(LeanObjectTag::from_u8(tag), LeanObjectTag::Ctor(_)) {
            let fields = lean_ctor_obj_cptr(obj);
            for i in 0..lean_ctor_num_objs(obj) {
                dec_for_del(*fields.add(i), todo);
            }
            lean_free_small_object(obj);
        } else {
            lean_del_core_other(obj, tag, todo);
        }
    }
}
