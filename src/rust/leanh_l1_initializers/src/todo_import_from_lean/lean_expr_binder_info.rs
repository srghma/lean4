use crate::todo_import_from_lean::lean_expr_tag::LeanExprTag;
use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_ctor_get_uint8::lean_ctor_get_uint8, lean_obj_tag::lean_obj_tag},
};

#[inline]
unsafe fn lean_expr_tag(e: *const LeanObject) -> LeanExprTag {
    LeanExprTag::from_u8(lean_obj_tag(e))
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanBinderInfo {
    Default = 0,
    Implicit = 1,
    StrictImplicit = 2,
    InstImplicit = 3,
}

impl LeanBinderInfo {
    #[inline]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanBinderInfo::Default,
            1 => LeanBinderInfo::Implicit,
            2 => LeanBinderInfo::StrictImplicit,
            3 => LeanBinderInfo::InstImplicit,
            n => panic!("invalid LeanBinderInfo tag {n}"),
        }
    }
}

#[inline]
pub unsafe fn lean_expr_binder_info(e: *const LeanObject) -> LeanBinderInfo {
    match lean_expr_tag(e) {
        LeanExprTag::Lambda | LeanExprTag::Pi => LeanBinderInfo::from_u8(lean_ctor_get_uint8(
            e,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        )),
        _ => LeanBinderInfo::Default,
    }
}
