use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_ctor_get_uint8::lean_ctor_get_uint8, lean_obj_tag::lean_obj_tag},
};

#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanBinderInfo {
    Default = 0,
    Implicit = 1,
    StrictImplicit = 2,
    InstImplicit = 3,
}

#[inline]
pub unsafe fn lean_expr_binder_info(e: *const LeanObject) -> LeanBinderInfo {
    match lean_obj_tag(e) {
        6 | 7 => {
            match lean_ctor_get_uint8(e, (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32) {
                0 => LeanBinderInfo::Default,
                1 => LeanBinderInfo::Implicit,
                2 => LeanBinderInfo::StrictImplicit,
                3 => LeanBinderInfo::InstImplicit,
                _ => LeanBinderInfo::Default,
            }
        }
        _ => LeanBinderInfo::Default,
    }
}
