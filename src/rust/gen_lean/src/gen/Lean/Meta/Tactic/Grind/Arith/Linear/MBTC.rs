// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.MBTC
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.MBTC Lean.Meta.Tactic.Grind.Arith.ModelUtil Lean.Meta.Tactic.Grind.Arith.Linear.Model Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_nat_add, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int, lean_uint64_to_usize,
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Rat::Basic::{
    l_Rat_div, l_Rat_neg, l_Rat_ofInt, l_instDecidableEqRat_decEq, l_mkRat,
};
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
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [90, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__0_value) as *mut leanh::LeanObject,18263865437487147968 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__1_value) as *mut leanh::LeanObject,2651253468108498348 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [79, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__3_value) as *mut leanh::LeanObject,1389984430658442515 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__4_value) as *mut leanh::LeanObject,9294582609080780319 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__6_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__7_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__9_value) as *mut leanh::LeanObject,9626815015619986526 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__10_value) as *mut leanh::LeanObject,17185717442815859305 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__12_value) as *mut leanh::LeanObject,11858238400308895562 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__13_value) as *mut leanh::LeanObject,6100819061652633370 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__0_value) as *mut leanh::LeanObject,8347582161988589016 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__1_value) as *mut leanh::LeanObject,7316284823769321069 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__3_value) as *mut leanh::LeanObject,17878876274162330439 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__4_value) as *mut leanh::LeanObject,11833570877100518198 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 118, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 118, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__6_value) as *mut leanh::LeanObject,4493959381811283967 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__7_value) as *mut leanh::LeanObject,1297950917268934889 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__0(
    mut v_a_470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = lean_nat_to_int(v_a_470_);
    return v___x_471_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(
    mut v_a_472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = lean_nat_to_int(v_a_472_);
    v___x_474_ = l_Rat_ofInt(v___x_473_);
    return v___x_474_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_500_ = leanh::lean_unsigned_to_nat(1);
    v___x_501_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(v___x_500_);
    return v___x_501_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_502_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__15);
    v___x_503_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_503_, 0, v___x_502_);
    return v___x_503_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_504_ = leanh::lean_unsigned_to_nat(0);
    v___x_505_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f_spec__1(v___x_504_);
    return v___x_505_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__17);
    v___x_507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_507_, 0, v___x_506_);
    return v___x_507_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(
    mut v_a_508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: u8 = 0;
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u8 = 0;
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: u8 = 0;
    let mut v_a_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_526_: u8 = 0;
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_533_: u8 = 0;
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_545_: u8 = 0;
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_550_: u8 = 0;
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_509_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__2;
                v___x_510_ = leanh::lean_unsigned_to_nat(2);
                v___x_511_ = l_Lean_Expr_isAppOfArity(v_a_508_, v___x_509_, v___x_510_);
                if v___x_511_ == 0 {
                    v___x_512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__5;
                    v___x_513_ = l_Lean_Expr_isAppOfArity(v_a_508_, v___x_512_, v___x_510_);
                    if v___x_513_ == 0 {
                        v___x_514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__8;
                        v___x_515_ = leanh::lean_unsigned_to_nat(3);
                        v___x_516_ = l_Lean_Expr_isAppOfArity(v_a_508_, v___x_514_, v___x_515_);
                        if v___x_516_ == 0 {
                            v___x_517_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__11;
                            v___x_518_ = l_Lean_Expr_isAppOfArity(v_a_508_, v___x_517_, v___x_515_);
                            if v___x_518_ == 0 {
                                v___x_519_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__14;
                                v___x_520_ = leanh::lean_unsigned_to_nat(6);
                                v___x_521_ =
                                    l_Lean_Expr_isAppOfArity(v_a_508_, v___x_519_, v___x_520_);
                                if v___x_521_ == 0 {
                                    if leanh::lean_obj_tag(v_a_508_) == 9 {
                                        v_a_522_ = leanh::lean_ctor_get(v_a_508_, 0);
                                        leanh::lean_inc_ref(v_a_522_);
                                        leanh::lean_dec_ref_known(v_a_508_, 1);
                                        if leanh::lean_obj_tag(v_a_522_) == 0 {
                                            v_val_523_ = leanh::lean_ctor_get(v_a_522_, 0);
                                            v_isSharedCheck_533_ =
                                                (!leanh::lean_is_exclusive(v_a_522_)) as u8;
                                            if v_isSharedCheck_533_ == 0 {
                                                v___x_525_ = v_a_522_;
                                                v_isShared_526_ = v_isSharedCheck_533_;
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_val_523_);
                                                leanh::lean_dec(v_a_522_);
                                                v___x_525_ = leanh::lean_box(0);
                                                v_isShared_526_ = v_isSharedCheck_533_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_a_522_);
                                            v___x_534_ = leanh::lean_box(0);
                                            return v___x_534_;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_a_508_);
                                        v___x_535_ = leanh::lean_box(0);
                                        return v___x_535_;
                                    }
                                } else {
                                    v___x_536_ = l_Lean_Expr_appFn_x21(v_a_508_);
                                    v___x_537_ = l_Lean_Expr_appArg_x21(v___x_536_);
                                    leanh::lean_dec_ref(v___x_536_);
                                    v___x_538_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v___x_537_);
                                    if leanh::lean_obj_tag(v___x_538_) == 0 {
                                        leanh::lean_dec_ref(v_a_508_);
                                        return v___x_538_;
                                    } else {
                                        v_val_539_ = leanh::lean_ctor_get(v___x_538_, 0);
                                        leanh::lean_inc(v_val_539_);
                                        leanh::lean_dec_ref_known(v___x_538_, 1);
                                        v___x_540_ = l_Lean_Expr_appArg_x21(v_a_508_);
                                        leanh::lean_dec_ref(v_a_508_);
                                        v___x_541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v___x_540_);
                                        if leanh::lean_obj_tag(v___x_541_) == 0 {
                                            leanh::lean_dec(v_val_539_);
                                            return v___x_541_;
                                        } else {
                                            v_val_542_ = leanh::lean_ctor_get(v___x_541_, 0);
                                            v_isSharedCheck_550_ =
                                                (!leanh::lean_is_exclusive(v___x_541_))
                                                    as u8;
                                            if v_isSharedCheck_550_ == 0 {
                                                v___x_544_ = v___x_541_;
                                                v_isShared_545_ = v_isSharedCheck_550_;
                                                state = 3;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_val_542_);
                                                leanh::lean_dec(v___x_541_);
                                                v___x_544_ = leanh::lean_box(0);
                                                v_isShared_545_ = v_isSharedCheck_550_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_551_ = l_Lean_Expr_appArg_x21(v_a_508_);
                                leanh::lean_dec_ref(v_a_508_);
                                v___x_552_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v___x_551_);
                                if leanh::lean_obj_tag(v___x_552_) == 0 {
                                    return v___x_552_;
                                } else {
                                    v_val_553_ = leanh::lean_ctor_get(v___x_552_, 0);
                                    v_isSharedCheck_561_ =
                                        (!leanh::lean_is_exclusive(v___x_552_)) as u8;
                                    if v_isSharedCheck_561_ == 0 {
                                        v___x_555_ = v___x_552_;
                                        v_isShared_556_ = v_isSharedCheck_561_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_553_);
                                        leanh::lean_dec(v___x_552_);
                                        v___x_555_ = leanh::lean_box(0);
                                        v_isShared_556_ = v_isSharedCheck_561_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_562_ = leanh::lean_unsigned_to_nat(1);
                            v___x_563_ = l_Lean_Expr_getAppNumArgs(v_a_508_);
                            v___x_564_ = lean_nat_sub(v___x_563_, v___x_562_);
                            leanh::lean_dec(v___x_563_);
                            v___x_565_ = lean_nat_sub(v___x_564_, v___x_562_);
                            leanh::lean_dec(v___x_564_);
                            v___x_566_ = l_Lean_Expr_getRevArg_x21(v_a_508_, v___x_565_);
                            leanh::lean_dec_ref(v_a_508_);
                            v_a_508_ = v___x_566_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_508_);
                        v___x_568_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__16);
                        return v___x_568_;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_508_);
                    v___x_569_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f___closed__18);
                    return v___x_569_;
                }
            }
            1 => {
                v___x_527_ = lean_nat_to_int(v_val_523_);
                v___x_528_ = leanh::lean_unsigned_to_nat(1);
                v___x_529_ = l_mkRat(v___x_527_, v___x_528_);
                if v_isShared_526_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_525_, 1);
                    leanh::lean_ctor_set(v___x_525_, 0, v___x_529_);
                    v___x_531_ = v___x_525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
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
                leanh::lean_dec(v_val_539_);
                if v_isShared_545_ == 0 {
                    leanh::lean_ctor_set(v___x_544_, 0, v___x_546_);
                    v___x_548_ = v___x_544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_549_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
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
                    leanh::lean_ctor_set(v___x_555_, 0, v___x_557_);
                    v___x_559_ = v___x_555_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
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
    mut v_s_570_: *mut leanh::LeanObject,
    mut v_a_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v_s_570_, v_a_571_);
    if leanh::lean_obj_tag(v___x_572_) == 1 {
        leanh::lean_dec_ref(v_a_571_);
        return v___x_572_;
    } else {
        let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_572_);
        v___x_573_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v_a_571_);
        return v___x_573_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f___boxed(
    mut v_s_574_: *mut leanh::LeanObject,
    mut v_a_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_576_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v_s_574_, v_a_575_);
    leanh::lean_dec_ref(v_s_574_);
    return v_res_576_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(
    mut v_e_577_: *mut leanh::LeanObject,
    mut v_a_578_: *mut leanh::LeanObject,
    mut v_a_579_: *mut leanh::LeanObject,
    mut v_a_580_: *mut leanh::LeanObject,
    mut v_a_581_: *mut leanh::LeanObject,
    mut v_a_582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_591_: u8 = 0;
    let mut v___x_592_: u8 = 0;
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut v_unused_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_584_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                leanh::lean_inc_ref(v_e_577_);
                v___x_585_ = l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(
                    v___x_584_, v_e_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_,
                );
                if leanh::lean_obj_tag(v___x_585_) == 0 {
                    v_a_586_ = leanh::lean_ctor_get(v___x_585_, 0);
                    leanh::lean_inc(v_a_586_);
                    v___x_587_ = (leanh::lean_unbox(v_a_586_) as u8);
                    leanh::lean_dec(v_a_586_);
                    if v___x_587_ == 0 {
                        v___x_588_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_toRatValue_x3f(v_e_577_);
                        if leanh::lean_obj_tag(v___x_588_) == 0 {
                            return v___x_585_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_588_, 1);
                            v_isSharedCheck_597_ =
                                (!leanh::lean_is_exclusive(v___x_585_)) as u8;
                            if v_isSharedCheck_597_ == 0 {
                                v_unused_598_ = leanh::lean_ctor_get(v___x_585_, 0);
                                leanh::lean_dec(v_unused_598_);
                                v___x_590_ = v___x_585_;
                                v_isShared_591_ = v_isSharedCheck_597_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_585_);
                                v___x_590_ = leanh::lean_box(0);
                                v_isShared_591_ = v_isSharedCheck_597_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_577_);
                        return v___x_585_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_577_);
                    return v___x_585_;
                }
            }
            1 => {
                v___x_592_ = 1;
                v___x_593_ = leanh::lean_box((v___x_592_) as usize);
                if v_isShared_591_ == 0 {
                    leanh::lean_ctor_set(v___x_590_, 0, v___x_593_);
                    v___x_595_ = v___x_590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
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
    mut v_e_599_: *mut leanh::LeanObject,
    mut v_a_600_: *mut leanh::LeanObject,
    mut v_a_601_: *mut leanh::LeanObject,
    mut v_a_602_: *mut leanh::LeanObject,
    mut v_a_603_: *mut leanh::LeanObject,
    mut v_a_604_: *mut leanh::LeanObject,
    mut v_a_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_606_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(v_e_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
    leanh::lean_dec(v_a_604_);
    leanh::lean_dec_ref(v_a_603_);
    leanh::lean_dec(v_a_602_);
    leanh::lean_dec_ref(v_a_601_);
    leanh::lean_dec(v_a_600_);
    return v_res_606_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar(
    mut v_e_607_: *mut leanh::LeanObject,
    mut v_a_608_: *mut leanh::LeanObject,
    mut v_a_609_: *mut leanh::LeanObject,
    mut v_a_610_: *mut leanh::LeanObject,
    mut v_a_611_: *mut leanh::LeanObject,
    mut v_a_612_: *mut leanh::LeanObject,
    mut v_a_613_: *mut leanh::LeanObject,
    mut v_a_614_: *mut leanh::LeanObject,
    mut v_a_615_: *mut leanh::LeanObject,
    mut v_a_616_: *mut leanh::LeanObject,
    mut v_a_617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_619_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___redArg(v_e_607_, v_a_608_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
    return v___x_619_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar___boxed(
    mut v_e_620_: *mut leanh::LeanObject,
    mut v_a_621_: *mut leanh::LeanObject,
    mut v_a_622_: *mut leanh::LeanObject,
    mut v_a_623_: *mut leanh::LeanObject,
    mut v_a_624_: *mut leanh::LeanObject,
    mut v_a_625_: *mut leanh::LeanObject,
    mut v_a_626_: *mut leanh::LeanObject,
    mut v_a_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
    mut v_a_629_: *mut leanh::LeanObject,
    mut v_a_630_: *mut leanh::LeanObject,
    mut v_a_631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_632_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_hasTheoryVar(v_e_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
    leanh::lean_dec(v_a_630_);
    leanh::lean_dec_ref(v_a_629_);
    leanh::lean_dec(v_a_628_);
    leanh::lean_dec_ref(v_a_627_);
    leanh::lean_dec(v_a_626_);
    leanh::lean_dec_ref(v_a_625_);
    leanh::lean_dec(v_a_624_);
    leanh::lean_dec_ref(v_a_623_);
    leanh::lean_dec(v_a_622_);
    leanh::lean_dec(v_a_621_);
    return v_res_632_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(
    mut v_e_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: u8 = 0;
    leanh::lean_inc_ref(v_e_648_);
    v___x_650_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_648_);
    v___x_651_ = 1;
    if v___x_650_ == 0 {
        let mut v_f_652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_654_: u8 = 0;
        v_f_652_ = l_Lean_Expr_getAppFn(v_e_648_);
        leanh::lean_dec_ref(v_e_648_);
        v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__2;
        v___x_654_ = l_Lean_Expr_isConstOf(v_f_652_, v___x_653_);
        if v___x_654_ == 0 {
            let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_656_: u8 = 0;
            v___x_655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__5;
            v___x_656_ = l_Lean_Expr_isConstOf(v_f_652_, v___x_655_);
            if v___x_656_ == 0 {
                let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_658_: u8 = 0;
                let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___closed__8;
                v___x_658_ = l_Lean_Expr_isConstOf(v_f_652_, v___x_657_);
                leanh::lean_dec_ref(v_f_652_);
                v___x_659_ = leanh::lean_box((v___x_658_) as usize);
                v___x_660_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_660_, 0, v___x_659_);
                return v___x_660_;
            } else {
                let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_f_652_);
                v___x_661_ = leanh::lean_box((v___x_651_) as usize);
                v___x_662_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_662_, 0, v___x_661_);
                return v___x_662_;
            }
        } else {
            let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_f_652_);
            v___x_663_ = leanh::lean_box((v___x_651_) as usize);
            v___x_664_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_664_, 0, v___x_663_);
            return v___x_664_;
        }
    } else {
        let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_648_);
        v___x_665_ = leanh::lean_box((v___x_651_) as usize);
        v___x_666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_666_, 0, v___x_665_);
        return v___x_666_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg___boxed(
    mut v_e_667_: *mut leanh::LeanObject,
    mut v_a_668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(v_e_667_);
    return v_res_669_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted(
    mut v_e_670_: *mut leanh::LeanObject,
    mut v_a_671_: *mut leanh::LeanObject,
    mut v_a_672_: *mut leanh::LeanObject,
    mut v_a_673_: *mut leanh::LeanObject,
    mut v_a_674_: *mut leanh::LeanObject,
    mut v_a_675_: *mut leanh::LeanObject,
    mut v_a_676_: *mut leanh::LeanObject,
    mut v_a_677_: *mut leanh::LeanObject,
    mut v_a_678_: *mut leanh::LeanObject,
    mut v_a_679_: *mut leanh::LeanObject,
    mut v_a_680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___redArg(v_e_670_);
    return v___x_682_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted___boxed(
    mut v_e_683_: *mut leanh::LeanObject,
    mut v_a_684_: *mut leanh::LeanObject,
    mut v_a_685_: *mut leanh::LeanObject,
    mut v_a_686_: *mut leanh::LeanObject,
    mut v_a_687_: *mut leanh::LeanObject,
    mut v_a_688_: *mut leanh::LeanObject,
    mut v_a_689_: *mut leanh::LeanObject,
    mut v_a_690_: *mut leanh::LeanObject,
    mut v_a_691_: *mut leanh::LeanObject,
    mut v_a_692_: *mut leanh::LeanObject,
    mut v_a_693_: *mut leanh::LeanObject,
    mut v_a_694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_695_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_isInterpreted(v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
    leanh::lean_dec(v_a_693_);
    leanh::lean_dec_ref(v_a_692_);
    leanh::lean_dec(v_a_691_);
    leanh::lean_dec_ref(v_a_690_);
    leanh::lean_dec(v_a_689_);
    leanh::lean_dec_ref(v_a_688_);
    leanh::lean_dec(v_a_687_);
    leanh::lean_dec_ref(v_a_686_);
    leanh::lean_dec(v_a_685_);
    leanh::lean_dec(v_a_684_);
    return v_res_695_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(
    mut v_keys_696_: *mut leanh::LeanObject,
    mut v_vals_697_: *mut leanh::LeanObject,
    mut v_i_698_: *mut leanh::LeanObject,
    mut v_k_699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_700_ = lean_array_get_size(v_keys_696_);
                v___x_701_ = lean_nat_dec_lt(v_i_698_, v___x_700_);
                if v___x_701_ == 0 {
                    leanh::lean_dec(v_i_698_);
                    v___x_702_ = leanh::lean_box(0);
                    return v___x_702_;
                } else {
                    v_k_x27_703_ = lean_array_fget_borrowed(v_keys_696_, v_i_698_);
                    v___x_704_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_699_,
                            v_k_x27_703_,
                        );
                    if v___x_704_ == 0 {
                        v___x_705_ = leanh::lean_unsigned_to_nat(1);
                        v___x_706_ = lean_nat_add(v_i_698_, v___x_705_);
                        leanh::lean_dec(v_i_698_);
                        v_i_698_ = v___x_706_;
                        state = 0;
                        continue;
                    } else {
                        v___x_708_ = lean_array_fget_borrowed(v_vals_697_, v_i_698_);
                        leanh::lean_dec(v_i_698_);
                        leanh::lean_inc(v___x_708_);
                        v___x_709_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_709_, 0, v___x_708_);
                        return v___x_709_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_710_: *mut leanh::LeanObject,
    mut v_vals_711_: *mut leanh::LeanObject,
    mut v_i_712_: *mut leanh::LeanObject,
    mut v_k_713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_714_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_keys_710_, v_vals_711_, v_i_712_, v_k_713_);
    leanh::lean_dec_ref(v_k_713_);
    leanh::lean_dec_ref(v_vals_711_);
    leanh::lean_dec_ref(v_keys_710_);
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
    v___x_719_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__0);
    v___x_720_ = lean_usize_sub(v___x_719_, v___x_718_);
    return v___x_720_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(
    mut v_x_721_: *mut leanh::LeanObject,
    mut v_x_722_: usize,
    mut v_x_723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: usize = 0;
    let mut v___x_727_: usize = 0;
    let mut v___x_728_: usize = 0;
    let mut v_j_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: usize = 0;
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_721_) == 0 {
                    v_es_724_ = leanh::lean_ctor_get(v_x_721_, 0);
                    v___x_725_ = leanh::lean_box(2);
                    v___x_726_ = 5usize;
                    v___x_727_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___closed__1);
                    v___x_728_ = lean_usize_land(v_x_722_, v___x_727_);
                    v_j_729_ = lean_usize_to_nat(v___x_728_);
                    v___x_730_ = lean_array_get_borrowed(v___x_725_, v_es_724_, v_j_729_);
                    leanh::lean_dec(v_j_729_);
                    match leanh::lean_obj_tag(v___x_730_) {
                        0 => {
                            v_key_731_ = leanh::lean_ctor_get(v___x_730_, 0);
                            v_val_732_ = leanh::lean_ctor_get(v___x_730_, 1);
                            v___x_733_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_723_, v_key_731_);
                            if v___x_733_ == 0 {
                                v___x_734_ = leanh::lean_box(0);
                                return v___x_734_;
                            } else {
                                leanh::lean_inc(v_val_732_);
                                v___x_735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_735_, 0, v_val_732_);
                                return v___x_735_;
                            }
                        }
                        1 => {
                            v_node_736_ = leanh::lean_ctor_get(v___x_730_, 0);
                            v___x_737_ = lean_usize_shift_right(v_x_722_, v___x_726_);
                            v_x_721_ = v_node_736_;
                            v_x_722_ = v___x_737_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_739_ = leanh::lean_box(0);
                            return v___x_739_;
                        }
                    }
                } else {
                    v_ks_740_ = leanh::lean_ctor_get(v_x_721_, 0);
                    v_vs_741_ = leanh::lean_ctor_get(v_x_721_, 1);
                    v___x_742_ = leanh::lean_unsigned_to_nat(0);
                    v___x_743_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_ks_740_, v_vs_741_, v___x_742_, v_x_723_);
                    return v___x_743_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg___boxed(
    mut v_x_744_: *mut leanh::LeanObject,
    mut v_x_745_: *mut leanh::LeanObject,
    mut v_x_746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_6397__boxed_747_: usize = 0;
    let mut v_res_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_6397__boxed_747_ = leanh::lean_unbox_usize(v_x_745_);
    leanh::lean_dec(v_x_745_);
    v_res_748_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_744_, v_x_6397__boxed_747_, v_x_746_);
    leanh::lean_dec_ref(v_x_746_);
    leanh::lean_dec_ref(v_x_744_);
    return v_res_748_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(
    mut v_x_749_: *mut leanh::LeanObject,
    mut v_x_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_751_: u64 = 0;
    let mut v___x_752_: usize = 0;
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_751_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_750_);
    v___x_752_ = lean_uint64_to_usize(v___x_751_);
    v___x_753_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_749_, v___x_752_, v_x_750_);
    return v___x_753_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg___boxed(
    mut v_x_754_: *mut leanh::LeanObject,
    mut v_x_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_x_754_, v_x_755_);
    leanh::lean_dec_ref(v_x_755_);
    leanh::lean_dec_ref(v_x_754_);
    return v_res_756_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(
    mut v_a_757_: *mut leanh::LeanObject,
    mut v_b_758_: *mut leanh::LeanObject,
    mut v_a_759_: *mut leanh::LeanObject,
    mut v_a_760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v_exprToStructId_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_778_: u8 = 0;
    let mut v_structs_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: u8 = 0;
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: u8 = 0;
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: u8 = 0;
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u8 = 0;
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_806_: u8 = 0;
    let mut v_a_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_814_: u8 = 0;
    let mut v___x_815_: u8 = 0;
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_823_: u8 = 0;
    let mut v_a_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_827_: u8 = 0;
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_831_: u8 = 0;
    let mut v_a_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_835_: u8 = 0;
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_762_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_759_, v_a_760_);
                if leanh::lean_obj_tag(v___x_762_) == 0 {
                    v_a_763_ = leanh::lean_ctor_get(v___x_762_, 0);
                    leanh::lean_inc(v_a_763_);
                    leanh::lean_dec_ref_known(v___x_762_, 1);
                    v___x_764_ =
                        l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_759_, v_a_760_);
                    if leanh::lean_obj_tag(v___x_764_) == 0 {
                        v_a_765_ = leanh::lean_ctor_get(v___x_764_, 0);
                        v_isSharedCheck_823_ = (!leanh::lean_is_exclusive(v___x_764_)) as u8;
                        if v_isSharedCheck_823_ == 0 {
                            v___x_767_ = v___x_764_;
                            v_isShared_768_ = v_isSharedCheck_823_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_765_);
                            leanh::lean_dec(v___x_764_);
                            v___x_767_ = leanh::lean_box(0);
                            v_isShared_768_ = v_isSharedCheck_823_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_763_);
                        leanh::lean_dec_ref(v_b_758_);
                        leanh::lean_dec_ref(v_a_757_);
                        v_a_824_ = leanh::lean_ctor_get(v___x_764_, 0);
                        v_isSharedCheck_831_ = (!leanh::lean_is_exclusive(v___x_764_)) as u8;
                        if v_isSharedCheck_831_ == 0 {
                            v___x_826_ = v___x_764_;
                            v_isShared_827_ = v_isSharedCheck_831_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_824_);
                            leanh::lean_dec(v___x_764_);
                            v___x_826_ = leanh::lean_box(0);
                            v_isShared_827_ = v_isSharedCheck_831_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_758_);
                    leanh::lean_dec_ref(v_a_757_);
                    v_a_832_ = leanh::lean_ctor_get(v___x_762_, 0);
                    v_isSharedCheck_839_ = (!leanh::lean_is_exclusive(v___x_762_)) as u8;
                    if v_isSharedCheck_839_ == 0 {
                        v___x_834_ = v___x_762_;
                        v_isShared_835_ = v_isSharedCheck_839_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_832_);
                        leanh::lean_dec(v___x_762_);
                        v___x_834_ = leanh::lean_box(0);
                        v_isShared_835_ = v_isSharedCheck_839_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToStructId_769_ = leanh::lean_ctor_get(v_a_763_, 2);
                leanh::lean_inc_ref(v_exprToStructId_769_);
                leanh::lean_dec(v_a_763_);
                v___x_770_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
                v___x_820_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_exprToStructId_769_, v_a_757_);
                leanh::lean_dec_ref(v_exprToStructId_769_);
                if leanh::lean_obj_tag(v___x_820_) == 0 {
                    v_exprToStructId_821_ = leanh::lean_ctor_get(v_a_765_, 2);
                    leanh::lean_inc_ref(v_exprToStructId_821_);
                    leanh::lean_dec(v_a_765_);
                    v___x_822_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_exprToStructId_821_, v_b_758_);
                    leanh::lean_dec_ref(v_exprToStructId_821_);
                    v___y_772_ = v___x_822_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_a_765_);
                    v___y_772_ = v___x_820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v___y_772_) == 1 {
                    leanh::lean_del_object(v___x_767_);
                    v_val_773_ = leanh::lean_ctor_get(v___y_772_, 0);
                    leanh::lean_inc(v_val_773_);
                    leanh::lean_dec_ref_known(v___y_772_, 1);
                    v___x_774_ =
                        l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_759_, v_a_760_);
                    if leanh::lean_obj_tag(v___x_774_) == 0 {
                        v_a_775_ = leanh::lean_ctor_get(v___x_774_, 0);
                        v_isSharedCheck_806_ = (!leanh::lean_is_exclusive(v___x_774_)) as u8;
                        if v_isSharedCheck_806_ == 0 {
                            v___x_777_ = v___x_774_;
                            v_isShared_778_ = v_isSharedCheck_806_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_775_);
                            leanh::lean_dec(v___x_774_);
                            v___x_777_ = leanh::lean_box(0);
                            v_isShared_778_ = v_isSharedCheck_806_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_773_);
                        leanh::lean_dec_ref(v_b_758_);
                        leanh::lean_dec_ref(v_a_757_);
                        v_a_807_ = leanh::lean_ctor_get(v___x_774_, 0);
                        v_isSharedCheck_814_ = (!leanh::lean_is_exclusive(v___x_774_)) as u8;
                        if v_isSharedCheck_814_ == 0 {
                            v___x_809_ = v___x_774_;
                            v_isShared_810_ = v_isSharedCheck_814_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_807_);
                            leanh::lean_dec(v___x_774_);
                            v___x_809_ = leanh::lean_box(0);
                            v_isShared_810_ = v_isSharedCheck_814_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_772_);
                    leanh::lean_dec_ref(v_b_758_);
                    leanh::lean_dec_ref(v_a_757_);
                    v___x_815_ = 0;
                    v___x_816_ = leanh::lean_box((v___x_815_) as usize);
                    if v_isShared_768_ == 0 {
                        leanh::lean_ctor_set(v___x_767_, 0, v___x_816_);
                        v___x_818_ = v___x_767_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
                        v___x_818_ = v_reuseFailAlloc_819_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v_structs_779_ = leanh::lean_ctor_get(v_a_775_, 0);
                leanh::lean_inc_ref(v_structs_779_);
                leanh::lean_dec(v_a_775_);
                v___x_780_ = lean_array_get(v___x_770_, v_structs_779_, v_val_773_);
                leanh::lean_dec(v_val_773_);
                leanh::lean_dec_ref(v_structs_779_);
                v_isLinearInst_x3f_781_ = leanh::lean_ctor_get(v___x_780_, 10);
                if leanh::lean_obj_tag(v_isLinearInst_x3f_781_) == 0 {
                    leanh::lean_dec(v___x_780_);
                    leanh::lean_dec_ref(v_b_758_);
                    leanh::lean_dec_ref(v_a_757_);
                    v___x_782_ = 0;
                    v___x_783_ = leanh::lean_box((v___x_782_) as usize);
                    if v_isShared_778_ == 0 {
                        leanh::lean_ctor_set(v___x_777_, 0, v___x_783_);
                        v___x_785_ = v___x_777_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_786_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
                        v___x_785_ = v_reuseFailAlloc_786_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v___x_780_, v_a_757_);
                    if leanh::lean_obj_tag(v___x_787_) == 1 {
                        v_val_788_ = leanh::lean_ctor_get(v___x_787_, 0);
                        leanh::lean_inc(v_val_788_);
                        leanh::lean_dec_ref_known(v___x_787_, 1);
                        v___x_789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_getAssignmentExt_x3f(v___x_780_, v_b_758_);
                        leanh::lean_dec(v___x_780_);
                        if leanh::lean_obj_tag(v___x_789_) == 1 {
                            v_val_790_ = leanh::lean_ctor_get(v___x_789_, 0);
                            leanh::lean_inc(v_val_790_);
                            leanh::lean_dec_ref_known(v___x_789_, 1);
                            v___x_791_ = l_instDecidableEqRat_decEq(v_val_788_, v_val_790_);
                            leanh::lean_dec(v_val_790_);
                            leanh::lean_dec(v_val_788_);
                            v___x_792_ = leanh::lean_box((v___x_791_) as usize);
                            if v_isShared_778_ == 0 {
                                leanh::lean_ctor_set(v___x_777_, 0, v___x_792_);
                                v___x_794_ = v___x_777_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_795_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
                                v___x_794_ = v_reuseFailAlloc_795_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_789_);
                            leanh::lean_dec(v_val_788_);
                            v___x_796_ = 0;
                            v___x_797_ = leanh::lean_box((v___x_796_) as usize);
                            if v_isShared_778_ == 0 {
                                leanh::lean_ctor_set(v___x_777_, 0, v___x_797_);
                                v___x_799_ = v___x_777_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_800_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
                                v___x_799_ = v_reuseFailAlloc_800_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_787_);
                        leanh::lean_dec(v___x_780_);
                        leanh::lean_dec_ref(v_b_758_);
                        v___x_801_ = 0;
                        v___x_802_ = leanh::lean_box((v___x_801_) as usize);
                        if v_isShared_778_ == 0 {
                            leanh::lean_ctor_set(v___x_777_, 0, v___x_802_);
                            v___x_804_ = v___x_777_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
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
                    v_reuseFailAlloc_813_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
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
                    v_reuseFailAlloc_830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
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
                    v_reuseFailAlloc_838_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
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
    mut v_a_840_: *mut leanh::LeanObject,
    mut v_b_841_: *mut leanh::LeanObject,
    mut v_a_842_: *mut leanh::LeanObject,
    mut v_a_843_: *mut leanh::LeanObject,
    mut v_a_844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_845_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(v_a_840_, v_b_841_, v_a_842_, v_a_843_);
    leanh::lean_dec_ref(v_a_843_);
    leanh::lean_dec(v_a_842_);
    return v_res_845_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment(
    mut v_a_846_: *mut leanh::LeanObject,
    mut v_b_847_: *mut leanh::LeanObject,
    mut v_a_848_: *mut leanh::LeanObject,
    mut v_a_849_: *mut leanh::LeanObject,
    mut v_a_850_: *mut leanh::LeanObject,
    mut v_a_851_: *mut leanh::LeanObject,
    mut v_a_852_: *mut leanh::LeanObject,
    mut v_a_853_: *mut leanh::LeanObject,
    mut v_a_854_: *mut leanh::LeanObject,
    mut v_a_855_: *mut leanh::LeanObject,
    mut v_a_856_: *mut leanh::LeanObject,
    mut v_a_857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___redArg(v_a_846_, v_b_847_, v_a_848_, v_a_856_);
    return v___x_859_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment___boxed(
    mut v_a_860_: *mut leanh::LeanObject,
    mut v_b_861_: *mut leanh::LeanObject,
    mut v_a_862_: *mut leanh::LeanObject,
    mut v_a_863_: *mut leanh::LeanObject,
    mut v_a_864_: *mut leanh::LeanObject,
    mut v_a_865_: *mut leanh::LeanObject,
    mut v_a_866_: *mut leanh::LeanObject,
    mut v_a_867_: *mut leanh::LeanObject,
    mut v_a_868_: *mut leanh::LeanObject,
    mut v_a_869_: *mut leanh::LeanObject,
    mut v_a_870_: *mut leanh::LeanObject,
    mut v_a_871_: *mut leanh::LeanObject,
    mut v_a_872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment(v_a_860_, v_b_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
    leanh::lean_dec(v_a_871_);
    leanh::lean_dec_ref(v_a_870_);
    leanh::lean_dec(v_a_869_);
    leanh::lean_dec_ref(v_a_868_);
    leanh::lean_dec(v_a_867_);
    leanh::lean_dec_ref(v_a_866_);
    leanh::lean_dec(v_a_865_);
    leanh::lean_dec_ref(v_a_864_);
    leanh::lean_dec(v_a_863_);
    leanh::lean_dec(v_a_862_);
    return v_res_873_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0(
    mut v_00_u03b2_874_: *mut leanh::LeanObject,
    mut v_x_875_: *mut leanh::LeanObject,
    mut v_x_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___redArg(v_x_875_, v_x_876_);
    return v___x_877_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0___boxed(
    mut v_00_u03b2_878_: *mut leanh::LeanObject,
    mut v_x_879_: *mut leanh::LeanObject,
    mut v_x_880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_881_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0(v_00_u03b2_878_, v_x_879_, v_x_880_);
    leanh::lean_dec_ref(v_x_880_);
    leanh::lean_dec_ref(v_x_879_);
    return v_res_881_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0(
    mut v_00_u03b2_882_: *mut leanh::LeanObject,
    mut v_x_883_: *mut leanh::LeanObject,
    mut v_x_884_: usize,
    mut v_x_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___redArg(v_x_883_, v_x_884_, v_x_885_);
    return v___x_886_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0___boxed(
    mut v_00_u03b2_887_: *mut leanh::LeanObject,
    mut v_x_888_: *mut leanh::LeanObject,
    mut v_x_889_: *mut leanh::LeanObject,
    mut v_x_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_6628__boxed_891_: usize = 0;
    let mut v_res_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_6628__boxed_891_ = leanh::lean_unbox_usize(v_x_889_);
    leanh::lean_dec(v_x_889_);
    v_res_892_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0(v_00_u03b2_887_, v_x_888_, v_x_6628__boxed_891_, v_x_890_);
    leanh::lean_dec_ref(v_x_890_);
    leanh::lean_dec_ref(v_x_888_);
    return v_res_892_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1(
    mut v_00_u03b2_893_: *mut leanh::LeanObject,
    mut v_keys_894_: *mut leanh::LeanObject,
    mut v_vals_895_: *mut leanh::LeanObject,
    mut v_heq_896_: *mut leanh::LeanObject,
    mut v_i_897_: *mut leanh::LeanObject,
    mut v_k_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___redArg(v_keys_894_, v_vals_895_, v_i_897_, v_k_898_);
    return v___x_899_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_900_: *mut leanh::LeanObject,
    mut v_keys_901_: *mut leanh::LeanObject,
    mut v_vals_902_: *mut leanh::LeanObject,
    mut v_heq_903_: *mut leanh::LeanObject,
    mut v_i_904_: *mut leanh::LeanObject,
    mut v_k_905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC_0__Lean_Meta_Grind_Arith_Linear_eqAssignment_spec__0_spec__0_spec__1(v_00_u03b2_900_, v_keys_901_, v_vals_902_, v_heq_903_, v_i_904_, v_k_905_);
    leanh::lean_dec_ref(v_k_905_);
    leanh::lean_dec_ref(v_vals_902_);
    leanh::lean_dec_ref(v_keys_901_);
    return v_res_906_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mbtc(
    mut v_a_914_: *mut leanh::LeanObject,
    mut v_a_915_: *mut leanh::LeanObject,
    mut v_a_916_: *mut leanh::LeanObject,
    mut v_a_917_: *mut leanh::LeanObject,
    mut v_a_918_: *mut leanh::LeanObject,
    mut v_a_919_: *mut leanh::LeanObject,
    mut v_a_920_: *mut leanh::LeanObject,
    mut v_a_921_: *mut leanh::LeanObject,
    mut v_a_922_: *mut leanh::LeanObject,
    mut v_a_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ = l_Lean_Meta_Grind_Arith_Linear_mbtc___closed__3;
    v___x_926_ = l_Lean_Meta_Grind_mbtc(
        v___x_925_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_,
        v_a_922_, v_a_923_,
    );
    return v___x_926_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mbtc___boxed(
    mut v_a_927_: *mut leanh::LeanObject,
    mut v_a_928_: *mut leanh::LeanObject,
    mut v_a_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
    mut v_a_931_: *mut leanh::LeanObject,
    mut v_a_932_: *mut leanh::LeanObject,
    mut v_a_933_: *mut leanh::LeanObject,
    mut v_a_934_: *mut leanh::LeanObject,
    mut v_a_935_: *mut leanh::LeanObject,
    mut v_a_936_: *mut leanh::LeanObject,
    mut v_a_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_Meta_Grind_Arith_Linear_mbtc(
        v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_,
        v_a_936_,
    );
    leanh::lean_dec(v_a_936_);
    leanh::lean_dec_ref(v_a_935_);
    leanh::lean_dec(v_a_934_);
    leanh::lean_dec_ref(v_a_933_);
    leanh::lean_dec(v_a_932_);
    leanh::lean_dec_ref(v_a_931_);
    leanh::lean_dec(v_a_930_);
    leanh::lean_dec_ref(v_a_929_);
    leanh::lean_dec(v_a_928_);
    leanh::lean_dec(v_a_927_);
    return v_res_938_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
}