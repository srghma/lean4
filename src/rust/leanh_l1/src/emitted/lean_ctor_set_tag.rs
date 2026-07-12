use crate::{
    datatypes::{LeanObject, LeanObjectTag},
    r#priv::lean_is_ctor::lean_is_ctor,
};

// Mirrors origin-master-src/include/lean/lean.h:708-711 (`lean_ctor_set_tag`).
#[inline]
pub unsafe fn lean_ctor_set_tag<T: Into<LeanObjectTag>>(obj: *mut LeanObject, new_tag: T) {
    debug_assert!(lean_is_ctor(obj));
    let new_tag = new_tag.into();
    debug_assert!(matches!(
        new_tag,
        LeanObjectTag::Ctor(_)
    ));
    (*obj).set_tag(new_tag);
}
