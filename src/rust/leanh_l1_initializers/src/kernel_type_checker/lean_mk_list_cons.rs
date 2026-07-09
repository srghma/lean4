use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set},
};

// List.cons ignores its erased element-type argument and consumes head/tail.
pub unsafe fn lean_mk_list_cons(
    _ty: *mut LeanObject,
    h: *mut LeanObject,
    t: *mut LeanObject,
) -> *mut LeanObject {
    let r = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(r, 0, h);
    lean_ctor_set(r, 1, t);
    r
}
