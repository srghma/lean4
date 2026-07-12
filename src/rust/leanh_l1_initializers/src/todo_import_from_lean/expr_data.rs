use leanh_l1::{
    datatypes::LeanObject,
    emitted::lean_ctor_get_uint64::lean_ctor_get_uint64,
};

use crate::todo_import_from_lean::lean_expr_tag::{lean_expr_tag, LeanExprTag};

#[inline]
pub unsafe fn expr_data(expr: *const LeanObject) -> u64 {
    let num_fields = match unsafe { lean_expr_tag(expr) } {
        LeanExprTag::BVar
        | LeanExprTag::FVar
        | LeanExprTag::MVar
        | LeanExprTag::Sort
        | LeanExprTag::Lit => 1,
        LeanExprTag::Const | LeanExprTag::App | LeanExprTag::MData => 2,
        LeanExprTag::Lambda | LeanExprTag::Pi | LeanExprTag::Proj => 3,
        LeanExprTag::Let => 4,
    };
    lean_ctor_get_uint64(
        expr,
        (core::mem::size_of::<*mut LeanObject>() * num_fields) as u32,
    )
}
