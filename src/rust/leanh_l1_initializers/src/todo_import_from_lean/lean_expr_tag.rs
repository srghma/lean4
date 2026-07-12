use leanh_l1::{
    datatypes::{LeanObject, LeanObjectTag},
    emitted::lean_obj_tag::lean_obj_tag,
};

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LeanExprTag {
    BVar = 0,
    FVar = 1,
    MVar = 2,
    Sort = 3,
    Const = 4,
    App = 5,
    Lambda = 6,
    Pi = 7,
    Let = 8,
    Lit = 9,
    MData = 10,
    Proj = 11,
}

impl LeanExprTag {
    #[inline]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanExprTag::BVar,
            1 => LeanExprTag::FVar,
            2 => LeanExprTag::MVar,
            3 => LeanExprTag::Sort,
            4 => LeanExprTag::Const,
            5 => LeanExprTag::App,
            6 => LeanExprTag::Lambda,
            7 => LeanExprTag::Pi,
            8 => LeanExprTag::Let,
            9 => LeanExprTag::Lit,
            10 => LeanExprTag::MData,
            11 => LeanExprTag::Proj,
            n => panic!("invalid LeanExprTag {n}"),
        }
    }
}

#[inline]
pub unsafe fn lean_expr_tag(expr: *const LeanObject) -> LeanExprTag {
    match lean_obj_tag(expr) {
        LeanObjectTag::Ctor(tag) => LeanExprTag::from_u8(tag),
        tag => panic!("invalid LeanExprTag {tag:?}"),
    }
}
