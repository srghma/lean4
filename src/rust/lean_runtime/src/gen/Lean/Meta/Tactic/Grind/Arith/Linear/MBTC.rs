// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.MBTC
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.MBTC Lean.Meta.Tactic.Grind.Arith.ModelUtil Lean.Meta.Tactic.Grind.Arith.Linear.Model Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
use crate::r#gen::Init::Data::Rat::Basic::{
    l_Rat_div, l_Rat_neg, l_Rat_ofInt, l_instDecidableEqRat_decEq, l_mkRat,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
    l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Model::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model,
    l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::{
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default,
    l_Lean_Meta_Grind_Arith_Linear_linearExt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::ModelUtil::{
    initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil, l_Lean_Meta_Grind_Arith_isInterpretedTerm,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MBTC::{
    initialize_Lean_Meta_Tactic_Grind_MBTC, l_Lean_Meta_Grind_mbtc,
    runtime_initialize_Lean_Meta_Tactic_Grind_MBTC,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types,
    l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_sub, lean_usize_to_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_nat_add, lean_nat_dec_lt, lean_nat_sub,
};
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [90, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0_value) as *mut crate::leanh::LeanObject,18263865437487147968 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1_value) as *mut crate::leanh::LeanObject,2651253468108498348 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [79, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3_value) as *mut crate::leanh::LeanObject,1389984430658442515 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4_value) as *mut crate::leanh::LeanObject,9294582609080780319 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12_value) as *mut crate::leanh::LeanObject,11858238400308895562 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13_value) as *mut crate::leanh::LeanObject,6100819061652633370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0_value) as *mut crate::leanh::LeanObject,8347582161988589016 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7316284823769321069 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3_value) as *mut crate::leanh::LeanObject,17878876274162330439 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11833570877100518198 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 118, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 118, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6_value) as *mut crate::leanh::LeanObject,4493959381811283967 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7_value) as *mut crate::leanh::LeanObject,1297950917268934889 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__0(
    mut v_a_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = lean_nat_to_int(v_a_470_);
    return v___x_471_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(
    mut v_a_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = lean_nat_to_int(v_a_472_);
    v___x_474_ = l_Rat_ofInt(v___x_473_);
    return v___x_474_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_500_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_501_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(v___x_500_);
    return v___x_501_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_502_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15);
    v___x_503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_503_, 0, v___x_502_);
    return v___x_503_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_504_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_505_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(v___x_504_);
    return v___x_505_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17);
    v___x_507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_507_, 0, v___x_506_);
    return v___x_507_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(
    mut v_a_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: u8 = 0;
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u8 = 0;
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: u8 = 0;
    let mut v_a_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_526_: u8 = 0;
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_533_: u8 = 0;
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_545_: u8 = 0;
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_550_: u8 = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_509_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2;
                v___x_510_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_511_ = l_Lean_Expr_isAppOfArity(v_a_508_, v___x_509_, v___x_510_);
                if v___x_511_ == 0 {
                    v___x_512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5;
                    v___x_513_ = l_Lean_Expr_isAppOfArity(v_a_508_, v___x_512_, v___x_510_);
                    if v___x_513_ == 0 {
                        v___x_514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8;
                        v___x_515_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_516_ = l_Lean_Expr_isAppOfArity(v_a_508_, v___x_514_, v___x_515_);
                        if v___x_516_ == 0 {
                            v___x_517_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11;
                            v___x_518_ = l_Lean_Expr_isAppOfArity(v_a_508_, v___x_517_, v___x_515_);
                            if v___x_518_ == 0 {
                                v___x_519_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14;
                                v___x_520_ = crate::leanh::lean_unsigned_to_nat(6);
                                v___x_521_ =
                                    l_Lean_Expr_isAppOfArity(v_a_508_, v___x_519_, v___x_520_);
                                if v___x_521_ == 0 {
                                    if crate::leanh::lean_obj_tag(v_a_508_) == 9 {
                                        v_a_522_ = crate::leanh::lean_ctor_get(v_a_508_, 0);
                                        crate::leanh::lean_inc_ref(v_a_522_);
                                        crate::leanh::lean_dec_ref_known(v_a_508_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_522_) == 0 {
                                            v_val_523_ = crate::leanh::lean_ctor_get(v_a_522_, 0);
                                            v_isSharedCheck_533_ =
                                                (!crate::leanh::lean_is_exclusive(v_a_522_)) as u8;
                                            if v_isSharedCheck_533_ == 0 {
                                                v___x_525_ = v_a_522_;
                                                v_isShared_526_ = v_isSharedCheck_533_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_val_523_);
                                                crate::leanh::lean_dec(v_a_522_);
                                                v___x_525_ = crate::leanh::lean_box(0);
                                                v_isShared_526_ = v_isSharedCheck_533_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_a_522_);
                                            v___x_534_ = crate::leanh::lean_box(0);
                                            return v___x_534_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_a_508_);
                                        v___x_535_ = crate::leanh::lean_box(0);
                                        return v___x_535_;
                                    }
                                } else {
                                    v___x_536_ = l_Lean_Expr_appFn_x21(v_a_508_);
                                    v___x_537_ = l_Lean_Expr_appArg_x21(v___x_536_);
                                    crate::leanh::lean_dec_ref(v___x_536_);
                                    v___x_538_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v___x_537_);
                                    if crate::leanh::lean_obj_tag(v___x_538_) == 0 {
                                        crate::leanh::lean_dec_ref(v_a_508_);
                                        return v___x_538_;
                                    } else {
                                        v_val_539_ = crate::leanh::lean_ctor_get(v___x_538_, 0);
                                        crate::leanh::lean_inc(v_val_539_);
                                        crate::leanh::lean_dec_ref_known(v___x_538_, 1);
                                        v___x_540_ = l_Lean_Expr_appArg_x21(v_a_508_);
                                        crate::leanh::lean_dec_ref(v_a_508_);
                                        v___x_541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v___x_540_);
                                        if crate::leanh::lean_obj_tag(v___x_541_) == 0 {
                                            crate::leanh::lean_dec(v_val_539_);
                                            return v___x_541_;
                                        } else {
                                            v_val_542_ = crate::leanh::lean_ctor_get(v___x_541_, 0);
                                            v_isSharedCheck_550_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_541_))
                                                    as u8;
                                            if v_isSharedCheck_550_ == 0 {
                                                v___x_544_ = v___x_541_;
                                                v_isShared_545_ = v_isSharedCheck_550_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_val_542_);
                                                crate::leanh::lean_dec(v___x_541_);
                                                v___x_544_ = crate::leanh::lean_box(0);
                                                v_isShared_545_ = v_isSharedCheck_550_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_551_ = l_Lean_Expr_appArg_x21(v_a_508_);
                                crate::leanh::lean_dec_ref(v_a_508_);
                                v___x_552_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v___x_551_);
                                if crate::leanh::lean_obj_tag(v___x_552_) == 0 {
                                    return v___x_552_;
                                } else {
                                    v_val_553_ = crate::leanh::lean_ctor_get(v___x_552_, 0);
                                    v_isSharedCheck_561_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_552_)) as u8;
                                    if v_isSharedCheck_561_ == 0 {
                                        v___x_555_ = v___x_552_;
                                        v_isShared_556_ = v_isSharedCheck_561_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_553_);
                                        crate::leanh::lean_dec(v___x_552_);
                                        v___x_555_ = crate::leanh::lean_box(0);
                                        v_isShared_556_ = v_isSharedCheck_561_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_562_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_563_ = l_Lean_Expr_getAppNumArgs(v_a_508_);
                            v___x_564_ = lean_nat_sub(v___x_563_, v___x_562_);
                            crate::leanh::lean_dec(v___x_563_);
                            v___x_565_ = lean_nat_sub(v___x_564_, v___x_562_);
                            crate::leanh::lean_dec(v___x_564_);
                            v___x_566_ = l_Lean_Expr_getRevArg_x21(v_a_508_, v___x_565_);
                            crate::leanh::lean_dec_ref(v_a_508_);
                            v_a_508_ = v___x_566_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_508_);
                        v___x_568_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16);
                        return v___x_568_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_508_);
                    v___x_569_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18);
                    return v___x_569_;
                }
            }
            1 => {
                v___x_527_ = lean_nat_to_int(v_val_523_);
                v___x_528_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_529_ = l_mkRat(v___x_527_, v___x_528_);
                if v_isShared_526_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_525_, 1);
                    crate::leanh::lean_ctor_set(v___x_525_, 0, v___x_529_);
                    v___x_531_ = v___x_525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
                    v___x_531_ = v_reuseFailAlloc_532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_531_;
            }
            3 => {
                v___x_546_ = l_Rat_div(v_val_539_, v_val_542_);
                crate::leanh::lean_dec(v_val_539_);
                if v_isShared_545_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_544_, 0, v___x_546_);
                    v___x_548_ = v___x_544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
                    v___x_548_ = v_reuseFailAlloc_549_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_548_;
            }
            5 => {
                v___x_557_ = l_Rat_neg(v_val_553_);
                if v_isShared_556_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_555_, 0, v___x_557_);
                    v___x_559_ = v___x_555_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
                    v___x_559_ = v_reuseFailAlloc_560_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(
    mut v_s_570_: *mut crate::leanh::LeanObject,
    mut v_a_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v_s_570_, v_a_571_);
    if crate::leanh::lean_obj_tag(v___x_572_) == 1 {
        crate::leanh::lean_dec_ref(v_a_571_);
        return v___x_572_;
    } else {
        let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_572_);
        v___x_573_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v_a_571_);
        return v___x_573_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f___boxed(
    mut v_s_574_: *mut crate::leanh::LeanObject,
    mut v_a_575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_576_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v_s_574_, v_a_575_);
    crate::leanh::lean_dec_ref(v_s_574_);
    return v_res_576_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(
    mut v_e_577_: *mut crate::leanh::LeanObject,
    mut v_a_578_: *mut crate::leanh::LeanObject,
    mut v_a_579_: *mut crate::leanh::LeanObject,
    mut v_a_580_: *mut crate::leanh::LeanObject,
    mut v_a_581_: *mut crate::leanh::LeanObject,
    mut v_a_582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_591_: u8 = 0;
    let mut v___x_592_: u8 = 0;
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut v_unused_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_584_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                crate::leanh::lean_inc_ref(v_e_577_);
                v___x_585_ = l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(
                    v___x_584_, v_e_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_,
                );
                if crate::leanh::lean_obj_tag(v___x_585_) == 0 {
                    v_a_586_ = crate::leanh::lean_ctor_get(v___x_585_, 0);
                    crate::leanh::lean_inc(v_a_586_);
                    v___x_587_ = (crate::leanh::lean_unbox(v_a_586_) as u8);
                    crate::leanh::lean_dec(v_a_586_);
                    if v___x_587_ == 0 {
                        v___x_588_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v_e_577_);
                        if crate::leanh::lean_obj_tag(v___x_588_) == 0 {
                            return v___x_585_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_588_, 1);
                            v_isSharedCheck_597_ =
                                (!crate::leanh::lean_is_exclusive(v___x_585_)) as u8;
                            if v_isSharedCheck_597_ == 0 {
                                v_unused_598_ = crate::leanh::lean_ctor_get(v___x_585_, 0);
                                crate::leanh::lean_dec(v_unused_598_);
                                v___x_590_ = v___x_585_;
                                v_isShared_591_ = v_isSharedCheck_597_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_585_);
                                v___x_590_ = crate::leanh::lean_box(0);
                                v_isShared_591_ = v_isSharedCheck_597_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_577_);
                        return v___x_585_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_577_);
                    return v___x_585_;
                }
            }
            1 => {
                v___x_592_ = 1;
                v___x_593_ = crate::leanh::lean_box((v___x_592_) as usize);
                if v_isShared_591_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_590_, 0, v___x_593_);
                    v___x_595_ = v___x_590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
                    v___x_595_ = v_reuseFailAlloc_596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg___boxed(
    mut v_e_599_: *mut crate::leanh::LeanObject,
    mut v_a_600_: *mut crate::leanh::LeanObject,
    mut v_a_601_: *mut crate::leanh::LeanObject,
    mut v_a_602_: *mut crate::leanh::LeanObject,
    mut v_a_603_: *mut crate::leanh::LeanObject,
    mut v_a_604_: *mut crate::leanh::LeanObject,
    mut v_a_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_606_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(v_e_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
    crate::leanh::lean_dec(v_a_604_);
    crate::leanh::lean_dec_ref(v_a_603_);
    crate::leanh::lean_dec(v_a_602_);
    crate::leanh::lean_dec_ref(v_a_601_);
    crate::leanh::lean_dec(v_a_600_);
    return v_res_606_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar(
    mut v_e_607_: *mut crate::leanh::LeanObject,
    mut v_a_608_: *mut crate::leanh::LeanObject,
    mut v_a_609_: *mut crate::leanh::LeanObject,
    mut v_a_610_: *mut crate::leanh::LeanObject,
    mut v_a_611_: *mut crate::leanh::LeanObject,
    mut v_a_612_: *mut crate::leanh::LeanObject,
    mut v_a_613_: *mut crate::leanh::LeanObject,
    mut v_a_614_: *mut crate::leanh::LeanObject,
    mut v_a_615_: *mut crate::leanh::LeanObject,
    mut v_a_616_: *mut crate::leanh::LeanObject,
    mut v_a_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_619_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(v_e_607_, v_a_608_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
    return v___x_619_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___boxed(
    mut v_e_620_: *mut crate::leanh::LeanObject,
    mut v_a_621_: *mut crate::leanh::LeanObject,
    mut v_a_622_: *mut crate::leanh::LeanObject,
    mut v_a_623_: *mut crate::leanh::LeanObject,
    mut v_a_624_: *mut crate::leanh::LeanObject,
    mut v_a_625_: *mut crate::leanh::LeanObject,
    mut v_a_626_: *mut crate::leanh::LeanObject,
    mut v_a_627_: *mut crate::leanh::LeanObject,
    mut v_a_628_: *mut crate::leanh::LeanObject,
    mut v_a_629_: *mut crate::leanh::LeanObject,
    mut v_a_630_: *mut crate::leanh::LeanObject,
    mut v_a_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_632_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar(v_e_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
    crate::leanh::lean_dec(v_a_630_);
    crate::leanh::lean_dec_ref(v_a_629_);
    crate::leanh::lean_dec(v_a_628_);
    crate::leanh::lean_dec_ref(v_a_627_);
    crate::leanh::lean_dec(v_a_626_);
    crate::leanh::lean_dec_ref(v_a_625_);
    crate::leanh::lean_dec(v_a_624_);
    crate::leanh::lean_dec_ref(v_a_623_);
    crate::leanh::lean_dec(v_a_622_);
    crate::leanh::lean_dec(v_a_621_);
    return v_res_632_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(
    mut v_e_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: u8 = 0;
    crate::leanh::lean_inc_ref(v_e_648_);
    v___x_650_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_648_);
    v___x_651_ = 1;
    if v___x_650_ == 0 {
        let mut v_f_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_654_: u8 = 0;
        v_f_652_ = l_Lean_Expr_getAppFn(v_e_648_);
        crate::leanh::lean_dec_ref(v_e_648_);
        v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2;
        v___x_654_ = l_Lean_Expr_isConstOf(v_f_652_, v___x_653_);
        if v___x_654_ == 0 {
            let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_656_: u8 = 0;
            v___x_655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5;
            v___x_656_ = l_Lean_Expr_isConstOf(v_f_652_, v___x_655_);
            if v___x_656_ == 0 {
                let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_658_: u8 = 0;
                let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8;
                v___x_658_ = l_Lean_Expr_isConstOf(v_f_652_, v___x_657_);
                crate::leanh::lean_dec_ref(v_f_652_);
                v___x_659_ = crate::leanh::lean_box((v___x_658_) as usize);
                v___x_660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_660_, 0, v___x_659_);
                return v___x_660_;
            } else {
                let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_f_652_);
                v___x_661_ = crate::leanh::lean_box((v___x_651_) as usize);
                v___x_662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_662_, 0, v___x_661_);
                return v___x_662_;
            }
        } else {
            let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_f_652_);
            v___x_663_ = crate::leanh::lean_box((v___x_651_) as usize);
            v___x_664_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_664_, 0, v___x_663_);
            return v___x_664_;
        }
    } else {
        let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_648_);
        v___x_665_ = crate::leanh::lean_box((v___x_651_) as usize);
        v___x_666_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_666_, 0, v___x_665_);
        return v___x_666_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___boxed(
    mut v_e_667_: *mut crate::leanh::LeanObject,
    mut v_a_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(v_e_667_);
    return v_res_669_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted(
    mut v_e_670_: *mut crate::leanh::LeanObject,
    mut v_a_671_: *mut crate::leanh::LeanObject,
    mut v_a_672_: *mut crate::leanh::LeanObject,
    mut v_a_673_: *mut crate::leanh::LeanObject,
    mut v_a_674_: *mut crate::leanh::LeanObject,
    mut v_a_675_: *mut crate::leanh::LeanObject,
    mut v_a_676_: *mut crate::leanh::LeanObject,
    mut v_a_677_: *mut crate::leanh::LeanObject,
    mut v_a_678_: *mut crate::leanh::LeanObject,
    mut v_a_679_: *mut crate::leanh::LeanObject,
    mut v_a_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(v_e_670_);
    return v___x_682_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___boxed(
    mut v_e_683_: *mut crate::leanh::LeanObject,
    mut v_a_684_: *mut crate::leanh::LeanObject,
    mut v_a_685_: *mut crate::leanh::LeanObject,
    mut v_a_686_: *mut crate::leanh::LeanObject,
    mut v_a_687_: *mut crate::leanh::LeanObject,
    mut v_a_688_: *mut crate::leanh::LeanObject,
    mut v_a_689_: *mut crate::leanh::LeanObject,
    mut v_a_690_: *mut crate::leanh::LeanObject,
    mut v_a_691_: *mut crate::leanh::LeanObject,
    mut v_a_692_: *mut crate::leanh::LeanObject,
    mut v_a_693_: *mut crate::leanh::LeanObject,
    mut v_a_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_695_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted(v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
    crate::leanh::lean_dec(v_a_693_);
    crate::leanh::lean_dec_ref(v_a_692_);
    crate::leanh::lean_dec(v_a_691_);
    crate::leanh::lean_dec_ref(v_a_690_);
    crate::leanh::lean_dec(v_a_689_);
    crate::leanh::lean_dec_ref(v_a_688_);
    crate::leanh::lean_dec(v_a_687_);
    crate::leanh::lean_dec_ref(v_a_686_);
    crate::leanh::lean_dec(v_a_685_);
    crate::leanh::lean_dec(v_a_684_);
    return v_res_695_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(
    mut v_keys_696_: *mut crate::leanh::LeanObject,
    mut v_vals_697_: *mut crate::leanh::LeanObject,
    mut v_i_698_: *mut crate::leanh::LeanObject,
    mut v_k_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_700_ = lean_array_get_size(v_keys_696_);
                v___x_701_ = lean_nat_dec_lt(v_i_698_, v___x_700_);
                if v___x_701_ == 0 {
                    crate::leanh::lean_dec(v_i_698_);
                    v___x_702_ = crate::leanh::lean_box(0);
                    return v___x_702_;
                } else {
                    v_k_x27_703_ = lean_array_fget_borrowed(v_keys_696_, v_i_698_);
                    v___x_704_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_699_,
                            v_k_x27_703_,
                        );
                    if v___x_704_ == 0 {
                        v___x_705_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_706_ = lean_nat_add(v_i_698_, v___x_705_);
                        crate::leanh::lean_dec(v_i_698_);
                        v_i_698_ = v___x_706_;
                        state = 0;
                        continue;
                    } else {
                        v___x_708_ = lean_array_fget_borrowed(v_vals_697_, v_i_698_);
                        crate::leanh::lean_dec(v_i_698_);
                        crate::leanh::lean_inc(v___x_708_);
                        v___x_709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_709_, 0, v___x_708_);
                        return v___x_709_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_710_: *mut crate::leanh::LeanObject,
    mut v_vals_711_: *mut crate::leanh::LeanObject,
    mut v_i_712_: *mut crate::leanh::LeanObject,
    mut v_k_713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_714_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_keys_710_, v_vals_711_, v_i_712_, v_k_713_);
    crate::leanh::lean_dec_ref(v_k_713_);
    crate::leanh::lean_dec_ref(v_vals_711_);
    crate::leanh::lean_dec_ref(v_keys_710_);
    return v_res_714_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_715_: usize = 0;
    let mut v___x_716_: usize = 0;
    let mut v___x_717_: usize = 0;
    v___x_715_ = 5usize;
    v___x_716_ = 1usize;
    v___x_717_ = lean_usize_shift_left(v___x_716_, v___x_715_);
    return v___x_717_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_718_: usize = 0;
    let mut v___x_719_: usize = 0;
    let mut v___x_720_: usize = 0;
    v___x_718_ = 1usize;
    v___x_719_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0);
    v___x_720_ = lean_usize_sub(v___x_719_, v___x_718_);
    return v___x_720_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(
    mut v_x_721_: *mut crate::leanh::LeanObject,
    mut v_x_722_: usize,
    mut v_x_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: usize = 0;
    let mut v___x_727_: usize = 0;
    let mut v___x_728_: usize = 0;
    let mut v_j_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: usize = 0;
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_721_) == 0 {
                    v_es_724_ = crate::leanh::lean_ctor_get(v_x_721_, 0);
                    v___x_725_ = crate::leanh::lean_box(2);
                    v___x_726_ = 5usize;
                    v___x_727_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1);
                    v___x_728_ = lean_usize_land(v_x_722_, v___x_727_);
                    v_j_729_ = lean_usize_to_nat(v___x_728_);
                    v___x_730_ = lean_array_get_borrowed(v___x_725_, v_es_724_, v_j_729_);
                    crate::leanh::lean_dec(v_j_729_);
                    match crate::leanh::lean_obj_tag(v___x_730_) {
                        0 => {
                            v_key_731_ = crate::leanh::lean_ctor_get(v___x_730_, 0);
                            v_val_732_ = crate::leanh::lean_ctor_get(v___x_730_, 1);
                            v___x_733_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_723_, v_key_731_);
                            if v___x_733_ == 0 {
                                v___x_734_ = crate::leanh::lean_box(0);
                                return v___x_734_;
                            } else {
                                crate::leanh::lean_inc(v_val_732_);
                                v___x_735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_735_, 0, v_val_732_);
                                return v___x_735_;
                            }
                        }
                        1 => {
                            v_node_736_ = crate::leanh::lean_ctor_get(v___x_730_, 0);
                            v___x_737_ = lean_usize_shift_right(v_x_722_, v___x_726_);
                            v_x_721_ = v_node_736_;
                            v_x_722_ = v___x_737_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_739_ = crate::leanh::lean_box(0);
                            return v___x_739_;
                        }
                    }
                } else {
                    v_ks_740_ = crate::leanh::lean_ctor_get(v_x_721_, 0);
                    v_vs_741_ = crate::leanh::lean_ctor_get(v_x_721_, 1);
                    v___x_742_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_743_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_ks_740_, v_vs_741_, v___x_742_, v_x_723_);
                    return v___x_743_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___boxed(
    mut v_x_744_: *mut crate::leanh::LeanObject,
    mut v_x_745_: *mut crate::leanh::LeanObject,
    mut v_x_746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6397__boxed_747_: usize = 0;
    let mut v_res_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6397__boxed_747_ = crate::leanh::lean_unbox_usize(v_x_745_);
    crate::leanh::lean_dec(v_x_745_);
    v_res_748_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_744_, v_x_6397__boxed_747_, v_x_746_);
    crate::leanh::lean_dec_ref(v_x_746_);
    crate::leanh::lean_dec_ref(v_x_744_);
    return v_res_748_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(
    mut v_x_749_: *mut crate::leanh::LeanObject,
    mut v_x_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_751_: u64 = 0;
    let mut v___x_752_: usize = 0;
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_751_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_750_);
    v___x_752_ = lean_uint64_to_usize(v___x_751_);
    v___x_753_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_749_, v___x_752_, v_x_750_);
    return v___x_753_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg___boxed(
    mut v_x_754_: *mut crate::leanh::LeanObject,
    mut v_x_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_x_754_, v_x_755_);
    crate::leanh::lean_dec_ref(v_x_755_);
    crate::leanh::lean_dec_ref(v_x_754_);
    return v_res_756_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(
    mut v_a_757_: *mut crate::leanh::LeanObject,
    mut v_b_758_: *mut crate::leanh::LeanObject,
    mut v_a_759_: *mut crate::leanh::LeanObject,
    mut v_a_760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v_exprToStructId_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_778_: u8 = 0;
    let mut v_structs_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: u8 = 0;
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: u8 = 0;
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: u8 = 0;
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u8 = 0;
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_806_: u8 = 0;
    let mut v_a_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_814_: u8 = 0;
    let mut v___x_815_: u8 = 0;
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_823_: u8 = 0;
    let mut v_a_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_827_: u8 = 0;
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_831_: u8 = 0;
    let mut v_a_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_835_: u8 = 0;
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_762_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_759_, v_a_760_);
                if crate::leanh::lean_obj_tag(v___x_762_) == 0 {
                    v_a_763_ = crate::leanh::lean_ctor_get(v___x_762_, 0);
                    crate::leanh::lean_inc(v_a_763_);
                    crate::leanh::lean_dec_ref_known(v___x_762_, 1);
                    v___x_764_ =
                        l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_759_, v_a_760_);
                    if crate::leanh::lean_obj_tag(v___x_764_) == 0 {
                        v_a_765_ = crate::leanh::lean_ctor_get(v___x_764_, 0);
                        v_isSharedCheck_823_ = (!crate::leanh::lean_is_exclusive(v___x_764_)) as u8;
                        if v_isSharedCheck_823_ == 0 {
                            v___x_767_ = v___x_764_;
                            v_isShared_768_ = v_isSharedCheck_823_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_765_);
                            crate::leanh::lean_dec(v___x_764_);
                            v___x_767_ = crate::leanh::lean_box(0);
                            v_isShared_768_ = v_isSharedCheck_823_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_763_);
                        crate::leanh::lean_dec_ref(v_b_758_);
                        crate::leanh::lean_dec_ref(v_a_757_);
                        v_a_824_ = crate::leanh::lean_ctor_get(v___x_764_, 0);
                        v_isSharedCheck_831_ = (!crate::leanh::lean_is_exclusive(v___x_764_)) as u8;
                        if v_isSharedCheck_831_ == 0 {
                            v___x_826_ = v___x_764_;
                            v_isShared_827_ = v_isSharedCheck_831_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_824_);
                            crate::leanh::lean_dec(v___x_764_);
                            v___x_826_ = crate::leanh::lean_box(0);
                            v_isShared_827_ = v_isSharedCheck_831_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_758_);
                    crate::leanh::lean_dec_ref(v_a_757_);
                    v_a_832_ = crate::leanh::lean_ctor_get(v___x_762_, 0);
                    v_isSharedCheck_839_ = (!crate::leanh::lean_is_exclusive(v___x_762_)) as u8;
                    if v_isSharedCheck_839_ == 0 {
                        v___x_834_ = v___x_762_;
                        v_isShared_835_ = v_isSharedCheck_839_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_832_);
                        crate::leanh::lean_dec(v___x_762_);
                        v___x_834_ = crate::leanh::lean_box(0);
                        v_isShared_835_ = v_isSharedCheck_839_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToStructId_769_ = crate::leanh::lean_ctor_get(v_a_763_, 2);
                crate::leanh::lean_inc_ref(v_exprToStructId_769_);
                crate::leanh::lean_dec(v_a_763_);
                v___x_770_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
                v___x_820_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_exprToStructId_769_, v_a_757_);
                crate::leanh::lean_dec_ref(v_exprToStructId_769_);
                if crate::leanh::lean_obj_tag(v___x_820_) == 0 {
                    v_exprToStructId_821_ = crate::leanh::lean_ctor_get(v_a_765_, 2);
                    crate::leanh::lean_inc_ref(v_exprToStructId_821_);
                    crate::leanh::lean_dec(v_a_765_);
                    v___x_822_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_exprToStructId_821_, v_b_758_);
                    crate::leanh::lean_dec_ref(v_exprToStructId_821_);
                    v___y_772_ = v___x_822_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_765_);
                    v___y_772_ = v___x_820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_772_) == 1 {
                    crate::leanh::lean_del_object(v___x_767_);
                    v_val_773_ = crate::leanh::lean_ctor_get(v___y_772_, 0);
                    crate::leanh::lean_inc(v_val_773_);
                    crate::leanh::lean_dec_ref_known(v___y_772_, 1);
                    v___x_774_ =
                        l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_759_, v_a_760_);
                    if crate::leanh::lean_obj_tag(v___x_774_) == 0 {
                        v_a_775_ = crate::leanh::lean_ctor_get(v___x_774_, 0);
                        v_isSharedCheck_806_ = (!crate::leanh::lean_is_exclusive(v___x_774_)) as u8;
                        if v_isSharedCheck_806_ == 0 {
                            v___x_777_ = v___x_774_;
                            v_isShared_778_ = v_isSharedCheck_806_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_775_);
                            crate::leanh::lean_dec(v___x_774_);
                            v___x_777_ = crate::leanh::lean_box(0);
                            v_isShared_778_ = v_isSharedCheck_806_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_773_);
                        crate::leanh::lean_dec_ref(v_b_758_);
                        crate::leanh::lean_dec_ref(v_a_757_);
                        v_a_807_ = crate::leanh::lean_ctor_get(v___x_774_, 0);
                        v_isSharedCheck_814_ = (!crate::leanh::lean_is_exclusive(v___x_774_)) as u8;
                        if v_isSharedCheck_814_ == 0 {
                            v___x_809_ = v___x_774_;
                            v_isShared_810_ = v_isSharedCheck_814_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_807_);
                            crate::leanh::lean_dec(v___x_774_);
                            v___x_809_ = crate::leanh::lean_box(0);
                            v_isShared_810_ = v_isSharedCheck_814_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_772_);
                    crate::leanh::lean_dec_ref(v_b_758_);
                    crate::leanh::lean_dec_ref(v_a_757_);
                    v___x_815_ = 0;
                    v___x_816_ = crate::leanh::lean_box((v___x_815_) as usize);
                    if v_isShared_768_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_767_, 0, v___x_816_);
                        v___x_818_ = v___x_767_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
                        v___x_818_ = v_reuseFailAlloc_819_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v_structs_779_ = crate::leanh::lean_ctor_get(v_a_775_, 0);
                crate::leanh::lean_inc_ref(v_structs_779_);
                crate::leanh::lean_dec(v_a_775_);
                v___x_780_ = lean_array_get(v___x_770_, v_structs_779_, v_val_773_);
                crate::leanh::lean_dec(v_val_773_);
                crate::leanh::lean_dec_ref(v_structs_779_);
                v_isLinearInst_x3f_781_ = crate::leanh::lean_ctor_get(v___x_780_, 10);
                if crate::leanh::lean_obj_tag(v_isLinearInst_x3f_781_) == 0 {
                    crate::leanh::lean_dec(v___x_780_);
                    crate::leanh::lean_dec_ref(v_b_758_);
                    crate::leanh::lean_dec_ref(v_a_757_);
                    v___x_782_ = 0;
                    v___x_783_ = crate::leanh::lean_box((v___x_782_) as usize);
                    if v_isShared_778_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_777_, 0, v___x_783_);
                        v___x_785_ = v___x_777_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
                        v___x_785_ = v_reuseFailAlloc_786_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v___x_780_, v_a_757_);
                    if crate::leanh::lean_obj_tag(v___x_787_) == 1 {
                        v_val_788_ = crate::leanh::lean_ctor_get(v___x_787_, 0);
                        crate::leanh::lean_inc(v_val_788_);
                        crate::leanh::lean_dec_ref_known(v___x_787_, 1);
                        v___x_789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v___x_780_, v_b_758_);
                        crate::leanh::lean_dec(v___x_780_);
                        if crate::leanh::lean_obj_tag(v___x_789_) == 1 {
                            v_val_790_ = crate::leanh::lean_ctor_get(v___x_789_, 0);
                            crate::leanh::lean_inc(v_val_790_);
                            crate::leanh::lean_dec_ref_known(v___x_789_, 1);
                            v___x_791_ = l_instDecidableEqRat_decEq(v_val_788_, v_val_790_);
                            crate::leanh::lean_dec(v_val_790_);
                            crate::leanh::lean_dec(v_val_788_);
                            v___x_792_ = crate::leanh::lean_box((v___x_791_) as usize);
                            if v_isShared_778_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_777_, 0, v___x_792_);
                                v___x_794_ = v___x_777_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_795_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
                                v___x_794_ = v_reuseFailAlloc_795_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_789_);
                            crate::leanh::lean_dec(v_val_788_);
                            v___x_796_ = 0;
                            v___x_797_ = crate::leanh::lean_box((v___x_796_) as usize);
                            if v_isShared_778_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_777_, 0, v___x_797_);
                                v___x_799_ = v___x_777_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_800_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
                                v___x_799_ = v_reuseFailAlloc_800_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_787_);
                        crate::leanh::lean_dec(v___x_780_);
                        crate::leanh::lean_dec_ref(v_b_758_);
                        v___x_801_ = 0;
                        v___x_802_ = crate::leanh::lean_box((v___x_801_) as usize);
                        if v_isShared_778_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_777_, 0, v___x_802_);
                            v___x_804_ = v___x_777_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
                            v___x_804_ = v_reuseFailAlloc_805_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_785_;
            }
            5 => {
                return v___x_794_;
            }
            6 => {
                return v___x_799_;
            }
            7 => {
                return v___x_804_;
            }
            8 => {
                if v_isShared_810_ == 0 {
                    v___x_812_ = v___x_809_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
                    v___x_812_ = v_reuseFailAlloc_813_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_812_;
            }
            10 => {
                return v___x_818_;
            }
            11 => {
                if v_isShared_827_ == 0 {
                    v___x_829_ = v___x_826_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
                    v___x_829_ = v_reuseFailAlloc_830_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_829_;
            }
            13 => {
                if v_isShared_835_ == 0 {
                    v___x_837_ = v___x_834_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
                    v___x_837_ = v_reuseFailAlloc_838_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg___boxed(
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_b_841_: *mut crate::leanh::LeanObject,
    mut v_a_842_: *mut crate::leanh::LeanObject,
    mut v_a_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_845_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(v_a_840_, v_b_841_, v_a_842_, v_a_843_);
    crate::leanh::lean_dec_ref(v_a_843_);
    crate::leanh::lean_dec(v_a_842_);
    return v_res_845_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment(
    mut v_a_846_: *mut crate::leanh::LeanObject,
    mut v_b_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
    mut v_a_849_: *mut crate::leanh::LeanObject,
    mut v_a_850_: *mut crate::leanh::LeanObject,
    mut v_a_851_: *mut crate::leanh::LeanObject,
    mut v_a_852_: *mut crate::leanh::LeanObject,
    mut v_a_853_: *mut crate::leanh::LeanObject,
    mut v_a_854_: *mut crate::leanh::LeanObject,
    mut v_a_855_: *mut crate::leanh::LeanObject,
    mut v_a_856_: *mut crate::leanh::LeanObject,
    mut v_a_857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(v_a_846_, v_b_847_, v_a_848_, v_a_856_);
    return v___x_859_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___boxed(
    mut v_a_860_: *mut crate::leanh::LeanObject,
    mut v_b_861_: *mut crate::leanh::LeanObject,
    mut v_a_862_: *mut crate::leanh::LeanObject,
    mut v_a_863_: *mut crate::leanh::LeanObject,
    mut v_a_864_: *mut crate::leanh::LeanObject,
    mut v_a_865_: *mut crate::leanh::LeanObject,
    mut v_a_866_: *mut crate::leanh::LeanObject,
    mut v_a_867_: *mut crate::leanh::LeanObject,
    mut v_a_868_: *mut crate::leanh::LeanObject,
    mut v_a_869_: *mut crate::leanh::LeanObject,
    mut v_a_870_: *mut crate::leanh::LeanObject,
    mut v_a_871_: *mut crate::leanh::LeanObject,
    mut v_a_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment(v_a_860_, v_b_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
    crate::leanh::lean_dec(v_a_871_);
    crate::leanh::lean_dec_ref(v_a_870_);
    crate::leanh::lean_dec(v_a_869_);
    crate::leanh::lean_dec_ref(v_a_868_);
    crate::leanh::lean_dec(v_a_867_);
    crate::leanh::lean_dec_ref(v_a_866_);
    crate::leanh::lean_dec(v_a_865_);
    crate::leanh::lean_dec_ref(v_a_864_);
    crate::leanh::lean_dec(v_a_863_);
    crate::leanh::lean_dec(v_a_862_);
    return v_res_873_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0(
    mut v_00_u03b2_874_: *mut crate::leanh::LeanObject,
    mut v_x_875_: *mut crate::leanh::LeanObject,
    mut v_x_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_x_875_, v_x_876_);
    return v___x_877_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___boxed(
    mut v_00_u03b2_878_: *mut crate::leanh::LeanObject,
    mut v_x_879_: *mut crate::leanh::LeanObject,
    mut v_x_880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_881_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0(v_00_u03b2_878_, v_x_879_, v_x_880_);
    crate::leanh::lean_dec_ref(v_x_880_);
    crate::leanh::lean_dec_ref(v_x_879_);
    return v_res_881_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0(
    mut v_00_u03b2_882_: *mut crate::leanh::LeanObject,
    mut v_x_883_: *mut crate::leanh::LeanObject,
    mut v_x_884_: usize,
    mut v_x_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_883_, v_x_884_, v_x_885_);
    return v___x_886_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___boxed(
    mut v_00_u03b2_887_: *mut crate::leanh::LeanObject,
    mut v_x_888_: *mut crate::leanh::LeanObject,
    mut v_x_889_: *mut crate::leanh::LeanObject,
    mut v_x_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6628__boxed_891_: usize = 0;
    let mut v_res_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6628__boxed_891_ = crate::leanh::lean_unbox_usize(v_x_889_);
    crate::leanh::lean_dec(v_x_889_);
    v_res_892_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0(v_00_u03b2_887_, v_x_888_, v_x_6628__boxed_891_, v_x_890_);
    crate::leanh::lean_dec_ref(v_x_890_);
    crate::leanh::lean_dec_ref(v_x_888_);
    return v_res_892_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1(
    mut v_00_u03b2_893_: *mut crate::leanh::LeanObject,
    mut v_keys_894_: *mut crate::leanh::LeanObject,
    mut v_vals_895_: *mut crate::leanh::LeanObject,
    mut v_heq_896_: *mut crate::leanh::LeanObject,
    mut v_i_897_: *mut crate::leanh::LeanObject,
    mut v_k_898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_keys_894_, v_vals_895_, v_i_897_, v_k_898_);
    return v___x_899_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_900_: *mut crate::leanh::LeanObject,
    mut v_keys_901_: *mut crate::leanh::LeanObject,
    mut v_vals_902_: *mut crate::leanh::LeanObject,
    mut v_heq_903_: *mut crate::leanh::LeanObject,
    mut v_i_904_: *mut crate::leanh::LeanObject,
    mut v_k_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1(v_00_u03b2_900_, v_keys_901_, v_vals_902_, v_heq_903_, v_i_904_, v_k_905_);
    crate::leanh::lean_dec_ref(v_k_905_);
    crate::leanh::lean_dec_ref(v_vals_902_);
    crate::leanh::lean_dec_ref(v_keys_901_);
    return v_res_906_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mbtc(
    mut v_a_914_: *mut crate::leanh::LeanObject,
    mut v_a_915_: *mut crate::leanh::LeanObject,
    mut v_a_916_: *mut crate::leanh::LeanObject,
    mut v_a_917_: *mut crate::leanh::LeanObject,
    mut v_a_918_: *mut crate::leanh::LeanObject,
    mut v_a_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
    mut v_a_921_: *mut crate::leanh::LeanObject,
    mut v_a_922_: *mut crate::leanh::LeanObject,
    mut v_a_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ = l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3;
    v___x_926_ = l_Lean_Meta_Grind_mbtc(
        v___x_925_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_,
        v_a_922_, v_a_923_,
    );
    return v___x_926_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mbtc___boxed(
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_a_928_: *mut crate::leanh::LeanObject,
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
    mut v_a_932_: *mut crate::leanh::LeanObject,
    mut v_a_933_: *mut crate::leanh::LeanObject,
    mut v_a_934_: *mut crate::leanh::LeanObject,
    mut v_a_935_: *mut crate::leanh::LeanObject,
    mut v_a_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_Meta_Grind_Arith_Linear_mbtc(
        v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_,
        v_a_936_,
    );
    crate::leanh::lean_dec(v_a_936_);
    crate::leanh::lean_dec_ref(v_a_935_);
    crate::leanh::lean_dec(v_a_934_);
    crate::leanh::lean_dec_ref(v_a_933_);
    crate::leanh::lean_dec(v_a_932_);
    crate::leanh::lean_dec_ref(v_a_931_);
    crate::leanh::lean_dec(v_a_930_);
    crate::leanh::lean_dec_ref(v_a_929_);
    crate::leanh::lean_dec(v_a_928_);
    crate::leanh::lean_dec(v_a_927_);
    return v_res_938_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
}
