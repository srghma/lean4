use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set,
        lean_ctor_set_uint64::lean_ctor_set_uint64,
    },
};

use crate::r#priv::lean_expr_mk_app_data::lean_expr_mk_app_data;
use crate::todo_import_from_lean::expr_data::expr_data;
use crate::todo_import_from_lean::lean_expr_mk_const::EXPR_DATA_OFFSET;
use crate::todo_import_from_lean::lean_expr_tag::LeanExprTag;

const EXPR_APP_FIELDS: u32 = 2;
const EXPR_APP_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;

#[inline]
pub unsafe fn lean_expr_mk_app(
    fn_expr: *mut LeanObject,
    arg_expr: *mut LeanObject,
) -> *mut LeanObject {
    let data = lean_expr_mk_app_data(expr_data(fn_expr), expr_data(arg_expr));
    let expr = lean_alloc_ctor(
        LeanExprTag::App as u32,
        EXPR_APP_FIELDS,
        EXPR_APP_SCALAR_SIZE,
    );
    lean_ctor_set(expr, 0, fn_expr);
    lean_ctor_set(expr, 1, arg_expr);
    lean_ctor_set_uint64(expr, EXPR_DATA_OFFSET, data);
    expr
}
