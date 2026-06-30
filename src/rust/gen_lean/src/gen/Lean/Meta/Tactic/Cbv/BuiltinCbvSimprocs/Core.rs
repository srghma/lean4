// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.Core
// Imports: Lean.Meta.Sym.Simp.SimpM Init.Sym.Lemmas Init.CbvSimproc Lean.Meta.Tactic.Cbv.CbvSimproc
use crate::ffi::lean_sym_simp;
use crate::r#gen::Init::CbvSimproc::{
    initialize_Init_CbvSimproc, runtime_initialize_Init_CbvSimproc,
};
use crate::r#gen::Init::Sym::Lemmas::{
    initialize_Init_Sym_Lemmas, runtime_initialize_Init_Sym_Lemmas,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_replaceFn, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getFalseExpr___redArg, l_Lean_Meta_Sym_getTrueExpr___redArg,
    l_Lean_Meta_Sym_isFalseExpr___redArg, l_Lean_Meta_Sym_isTrueExpr___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::CbvSimproc::{
    initialize_Lean_Meta_Tactic_Cbv_CbvSimproc, l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr,
    l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc,
    runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc,
};
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [79, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__1_value) as *mut leanh::LeanObject,14181099489592536354 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__3_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [102, 97, 108, 115, 101, 95, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__3_value) as *mut leanh::LeanObject,7030941873239652894 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__6_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 117, 101, 95, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__6_value) as *mut leanh::LeanObject,3037741586801491095 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__11_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [111, 114, 95, 101, 113, 95, 114, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__11_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__11_value) as *mut leanh::LeanObject,13300370967057954325 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__13_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [111, 114, 95, 101, 113, 95, 116, 114, 117, 101, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__13_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__13_value) as *mut leanh::LeanObject,1011184777873256822 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,16489734963670585437 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [66, 117, 105, 108, 116, 105, 110, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,8524095998741210685 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,13795083944981294805 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,219597323698272320 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut leanh::LeanObject,1411255169149101689 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,12139464363154525161 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut leanh::LeanObject,17876964083007659580 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,17009103051292104096 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 79, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,12054117545489417188 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2_value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: leanh::LeanArrayObject<3> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__0_value) as *mut leanh::LeanObject,9743492140944907313 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 114, 117, 101, 95, 97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__2_value) as *mut leanh::LeanObject,17391556055311371073 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__5_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 97, 108, 115, 101, 95, 97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__5_value) as *mut leanh::LeanObject,4492176092438480580 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__8_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 110, 100, 95, 101, 113, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__8_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__8_value) as *mut leanh::LeanObject,679327600139009352 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__10_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [97, 110, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__10_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__10_value) as *mut leanh::LeanObject,10479839610626251338 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 105, 109, 112, 65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut leanh::LeanObject,17397356683693532514 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1_value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value: leanh::LeanArrayObject<3> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = leanh::lean_box(0);
    v___x_517_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__4;
    v___x_518_ = l_Lean_mkConst(v___x_517_, v___x_516_);
    return v___x_518_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = leanh::lean_box(0);
    v___x_523_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__7;
    v___x_524_ = l_Lean_mkConst(v___x_523_, v___x_522_);
    return v___x_524_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr(
    mut v_e_537_: *mut leanh::LeanObject,
    mut v_a_538_: *mut leanh::LeanObject,
    mut v_a_539_: *mut leanh::LeanObject,
    mut v_a_540_: *mut leanh::LeanObject,
    mut v_a_541_: *mut leanh::LeanObject,
    mut v_a_542_: *mut leanh::LeanObject,
    mut v_a_543_: *mut leanh::LeanObject,
    mut v_a_544_: *mut leanh::LeanObject,
    mut v_a_545_: *mut leanh::LeanObject,
    mut v_a_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: u8 = 0;
    let mut v_arg_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: u8 = 0;
    let mut v_arg_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: u8 = 0;
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_564_: u8 = 0;
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: u8 = 0;
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_573_: u8 = 0;
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut v___x_577_: u8 = 0;
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: u8 = 0;
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v_a_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v_a_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_a_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_isSharedCheck_628_: u8 = 0;
    let mut v_e_x27_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_633_: u8 = 0;
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: u8 = 0;
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v___x_642_: u8 = 0;
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: u8 = 0;
    let mut v___x_645_: u8 = 0;
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    let mut v___x_655_: u8 = 0;
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut v_a_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_664_: u8 = 0;
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut v_a_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_688_: u8 = 0;
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_692_: u8 = 0;
    let mut v_a_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_696_: u8 = 0;
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_700_: u8 = 0;
    let mut v_isSharedCheck_701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_537_);
                v___x_551_ = l_Lean_Expr_cleanupAnnotations(v_e_537_);
                v___x_552_ = l_Lean_Expr_isApp(v___x_551_);
                if v___x_552_ == 0 {
                    leanh::lean_dec_ref(v___x_551_);
                    leanh::lean_dec_ref(v_e_537_);
                    state = 1;
                    continue;
                } else {
                    v_arg_553_ = leanh::lean_ctor_get(v___x_551_, 1);
                    leanh::lean_inc_ref(v_arg_553_);
                    v___x_554_ = l_Lean_Expr_appFnCleanup___redArg(v___x_551_);
                    v___x_555_ = l_Lean_Expr_isApp(v___x_554_);
                    if v___x_555_ == 0 {
                        leanh::lean_dec_ref(v___x_554_);
                        leanh::lean_dec_ref(v_arg_553_);
                        leanh::lean_dec_ref(v_e_537_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_556_ = leanh::lean_ctor_get(v___x_554_, 1);
                        leanh::lean_inc_ref(v_arg_556_);
                        v___x_557_ = l_Lean_Expr_appFnCleanup___redArg(v___x_554_);
                        v___x_558_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2;
                        v___x_559_ = l_Lean_Expr_isConstOf(v___x_557_, v___x_558_);
                        leanh::lean_dec_ref(v___x_557_);
                        if v___x_559_ == 0 {
                            leanh::lean_dec_ref(v_arg_556_);
                            leanh::lean_dec_ref(v_arg_553_);
                            leanh::lean_dec_ref(v_e_537_);
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_546_);
                            leanh::lean_inc_ref(v_a_545_);
                            leanh::lean_inc(v_a_544_);
                            leanh::lean_inc_ref(v_a_543_);
                            leanh::lean_inc(v_a_542_);
                            leanh::lean_inc_ref(v_a_541_);
                            leanh::lean_inc(v_a_540_);
                            leanh::lean_inc_ref(v_a_539_);
                            leanh::lean_inc(v_a_538_);
                            leanh::lean_inc_ref(v_arg_556_);
                            v___x_560_ = lean_sym_simp(
                                v_arg_556_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_,
                                v_a_543_, v_a_544_, v_a_545_, v_a_546_,
                            );
                            if leanh::lean_obj_tag(v___x_560_) == 0 {
                                v_a_561_ = leanh::lean_ctor_get(v___x_560_, 0);
                                leanh::lean_inc(v_a_561_);
                                leanh::lean_dec_ref_known(v___x_560_, 1);
                                if leanh::lean_obj_tag(v_a_561_) == 0 {
                                    leanh::lean_dec_ref(v_e_537_);
                                    v_isSharedCheck_628_ =
                                        (!leanh::lean_is_exclusive(v_a_561_)) as u8;
                                    if v_isSharedCheck_628_ == 0 {
                                        v___x_563_ = v_a_561_;
                                        v_isShared_564_ = v_isSharedCheck_628_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_561_);
                                        v___x_563_ = leanh::lean_box(0);
                                        v_isShared_564_ = v_isSharedCheck_628_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_556_);
                                    v_e_x27_629_ = leanh::lean_ctor_get(v_a_561_, 0);
                                    v_proof_630_ = leanh::lean_ctor_get(v_a_561_, 1);
                                    v_isSharedCheck_701_ =
                                        (!leanh::lean_is_exclusive(v_a_561_)) as u8;
                                    if v_isSharedCheck_701_ == 0 {
                                        v___x_632_ = v_a_561_;
                                        v_isShared_633_ = v_isSharedCheck_701_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_proof_630_);
                                        leanh::lean_inc(v_e_x27_629_);
                                        leanh::lean_dec(v_a_561_);
                                        v___x_632_ = leanh::lean_box(0);
                                        v_isShared_633_ = v_isSharedCheck_701_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_arg_556_);
                                leanh::lean_dec_ref(v_arg_553_);
                                leanh::lean_dec_ref(v_e_537_);
                                return v___x_560_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_549_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0;
                v___x_550_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_550_, 0, v___x_549_);
                return v___x_550_;
            }
            2 => {
                v___x_565_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_556_, v_a_541_);
                if leanh::lean_obj_tag(v___x_565_) == 0 {
                    v_a_566_ = leanh::lean_ctor_get(v___x_565_, 0);
                    leanh::lean_inc(v_a_566_);
                    leanh::lean_dec_ref_known(v___x_565_, 1);
                    v___x_567_ = (leanh::lean_unbox(v_a_566_) as u8);
                    if v___x_567_ == 0 {
                        v___x_568_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_556_, v_a_541_);
                        leanh::lean_dec_ref(v_arg_556_);
                        if leanh::lean_obj_tag(v___x_568_) == 0 {
                            v_a_569_ = leanh::lean_ctor_get(v___x_568_, 0);
                            v_isSharedCheck_590_ =
                                (!leanh::lean_is_exclusive(v___x_568_)) as u8;
                            if v_isSharedCheck_590_ == 0 {
                                v___x_571_ = v___x_568_;
                                v_isShared_572_ = v_isSharedCheck_590_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_569_);
                                leanh::lean_dec(v___x_568_);
                                v___x_571_ = leanh::lean_box(0);
                                v_isShared_572_ = v_isSharedCheck_590_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_566_);
                            leanh::lean_del_object(v___x_563_);
                            leanh::lean_dec_ref(v_arg_553_);
                            v_a_591_ = leanh::lean_ctor_get(v___x_568_, 0);
                            v_isSharedCheck_598_ =
                                (!leanh::lean_is_exclusive(v___x_568_)) as u8;
                            if v_isSharedCheck_598_ == 0 {
                                v___x_593_ = v___x_568_;
                                v_isShared_594_ = v_isSharedCheck_598_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_591_);
                                leanh::lean_dec(v___x_568_);
                                v___x_593_ = leanh::lean_box(0);
                                v_isShared_594_ = v_isSharedCheck_598_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_566_);
                        leanh::lean_del_object(v___x_563_);
                        leanh::lean_dec_ref(v_arg_556_);
                        v___x_599_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_541_);
                        if leanh::lean_obj_tag(v___x_599_) == 0 {
                            v_a_600_ = leanh::lean_ctor_get(v___x_599_, 0);
                            v_isSharedCheck_611_ =
                                (!leanh::lean_is_exclusive(v___x_599_)) as u8;
                            if v_isSharedCheck_611_ == 0 {
                                v___x_602_ = v___x_599_;
                                v_isShared_603_ = v_isSharedCheck_611_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_600_);
                                leanh::lean_dec(v___x_599_);
                                v___x_602_ = leanh::lean_box(0);
                                v_isShared_603_ = v_isSharedCheck_611_;
                                state = 9;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_553_);
                            v_a_612_ = leanh::lean_ctor_get(v___x_599_, 0);
                            v_isSharedCheck_619_ =
                                (!leanh::lean_is_exclusive(v___x_599_)) as u8;
                            if v_isSharedCheck_619_ == 0 {
                                v___x_614_ = v___x_599_;
                                v_isShared_615_ = v_isSharedCheck_619_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_612_);
                                leanh::lean_dec(v___x_599_);
                                v___x_614_ = leanh::lean_box(0);
                                v_isShared_615_ = v_isSharedCheck_619_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_563_);
                    leanh::lean_dec_ref(v_arg_556_);
                    leanh::lean_dec_ref(v_arg_553_);
                    v_a_620_ = leanh::lean_ctor_get(v___x_565_, 0);
                    v_isSharedCheck_627_ = (!leanh::lean_is_exclusive(v___x_565_)) as u8;
                    if v_isSharedCheck_627_ == 0 {
                        v___x_622_ = v___x_565_;
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_620_);
                        leanh::lean_dec(v___x_565_);
                        v___x_622_ = leanh::lean_box(0);
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => {
                v___x_573_ = (leanh::lean_unbox(v_a_569_) as u8);
                if v___x_573_ == 0 {
                    leanh::lean_dec(v_a_566_);
                    leanh::lean_dec_ref(v_arg_553_);
                    if v_isShared_564_ == 0 {
                        v___x_575_ = v___x_563_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_581_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                        v___x_575_ = v_reuseFailAlloc_581_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_569_);
                    leanh::lean_del_object(v___x_563_);
                    v___x_582_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5_once), _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5);
                    leanh::lean_inc_ref(v_arg_553_);
                    v___x_583_ = l_Lean_Expr_app___override(v___x_582_, v_arg_553_);
                    v___x_584_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v___x_584_, 0, v_arg_553_);
                    leanh::lean_ctor_set(v___x_584_, 1, v___x_583_);
                    v___x_585_ = (leanh::lean_unbox(v_a_566_) as u8);
                    leanh::lean_ctor_set_uint8(
                        v___x_584_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_585_,
                    );
                    v___x_586_ = (leanh::lean_unbox(v_a_566_) as u8);
                    leanh::lean_dec(v_a_566_);
                    leanh::lean_ctor_set_uint8(
                        v___x_584_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v___x_586_,
                    );
                    if v_isShared_572_ == 0 {
                        leanh::lean_ctor_set(v___x_571_, 0, v___x_584_);
                        v___x_588_ = v___x_571_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_584_);
                        v___x_588_ = v_reuseFailAlloc_589_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_576_ = (leanh::lean_unbox(v_a_569_) as u8);
                leanh::lean_ctor_set_uint8(v___x_575_, 0 as u32, v___x_576_);
                v___x_577_ = (leanh::lean_unbox(v_a_569_) as u8);
                leanh::lean_dec(v_a_569_);
                leanh::lean_ctor_set_uint8(v___x_575_, 1 as u32, v___x_577_);
                if v_isShared_572_ == 0 {
                    leanh::lean_ctor_set(v___x_571_, 0, v___x_575_);
                    v___x_579_ = v___x_571_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_580_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_575_);
                    v___x_579_ = v_reuseFailAlloc_580_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_579_;
            }
            6 => {
                return v___x_588_;
            }
            7 => {
                if v_isShared_594_ == 0 {
                    v___x_596_ = v___x_593_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
                    v___x_596_ = v_reuseFailAlloc_597_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_596_;
            }
            9 => {
                v___x_604_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8_once), _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8);
                v___x_605_ = l_Lean_Expr_app___override(v___x_604_, v_arg_553_);
                v___x_606_ = 0;
                v___x_607_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_607_, 0, v_a_600_);
                leanh::lean_ctor_set(v___x_607_, 1, v___x_605_);
                leanh::lean_ctor_set_uint8(
                    v___x_607_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_559_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_607_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_606_,
                );
                if v_isShared_603_ == 0 {
                    leanh::lean_ctor_set(v___x_602_, 0, v___x_607_);
                    v___x_609_ = v___x_602_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_610_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
                    v___x_609_ = v_reuseFailAlloc_610_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_609_;
            }
            11 => {
                if v_isShared_615_ == 0 {
                    v___x_617_ = v___x_614_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
                    v___x_617_ = v_reuseFailAlloc_618_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_617_;
            }
            13 => {
                if v_isShared_623_ == 0 {
                    v___x_625_ = v___x_622_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
                    v___x_625_ = v_reuseFailAlloc_626_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_625_;
            }
            15 => {
                v___x_634_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_629_, v_a_541_);
                if leanh::lean_obj_tag(v___x_634_) == 0 {
                    v_a_635_ = leanh::lean_ctor_get(v___x_634_, 0);
                    leanh::lean_inc(v_a_635_);
                    leanh::lean_dec_ref_known(v___x_634_, 1);
                    v___x_636_ = (leanh::lean_unbox(v_a_635_) as u8);
                    if v___x_636_ == 0 {
                        v___x_637_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_629_, v_a_541_);
                        leanh::lean_dec_ref(v_e_x27_629_);
                        if leanh::lean_obj_tag(v___x_637_) == 0 {
                            v_a_638_ = leanh::lean_ctor_get(v___x_637_, 0);
                            v_isSharedCheck_660_ =
                                (!leanh::lean_is_exclusive(v___x_637_)) as u8;
                            if v_isSharedCheck_660_ == 0 {
                                v___x_640_ = v___x_637_;
                                v_isShared_641_ = v_isSharedCheck_660_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_638_);
                                leanh::lean_dec(v___x_637_);
                                v___x_640_ = leanh::lean_box(0);
                                v_isShared_641_ = v_isSharedCheck_660_;
                                state = 16;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_635_);
                            leanh::lean_del_object(v___x_632_);
                            leanh::lean_dec_ref(v_proof_630_);
                            leanh::lean_dec_ref(v_arg_553_);
                            leanh::lean_dec_ref(v_e_537_);
                            v_a_661_ = leanh::lean_ctor_get(v___x_637_, 0);
                            v_isSharedCheck_668_ =
                                (!leanh::lean_is_exclusive(v___x_637_)) as u8;
                            if v_isSharedCheck_668_ == 0 {
                                v___x_663_ = v___x_637_;
                                v_isShared_664_ = v_isSharedCheck_668_;
                                state = 20;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_661_);
                                leanh::lean_dec(v___x_637_);
                                v___x_663_ = leanh::lean_box(0);
                                v_isShared_664_ = v_isSharedCheck_668_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_635_);
                        leanh::lean_dec_ref(v_e_x27_629_);
                        leanh::lean_dec_ref(v_arg_553_);
                        v___x_669_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_541_);
                        if leanh::lean_obj_tag(v___x_669_) == 0 {
                            v_a_670_ = leanh::lean_ctor_get(v___x_669_, 0);
                            v_isSharedCheck_684_ =
                                (!leanh::lean_is_exclusive(v___x_669_)) as u8;
                            if v_isSharedCheck_684_ == 0 {
                                v___x_672_ = v___x_669_;
                                v_isShared_673_ = v_isSharedCheck_684_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_670_);
                                leanh::lean_dec(v___x_669_);
                                v___x_672_ = leanh::lean_box(0);
                                v_isShared_673_ = v_isSharedCheck_684_;
                                state = 22;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_632_);
                            leanh::lean_dec_ref(v_proof_630_);
                            leanh::lean_dec_ref(v_e_537_);
                            v_a_685_ = leanh::lean_ctor_get(v___x_669_, 0);
                            v_isSharedCheck_692_ =
                                (!leanh::lean_is_exclusive(v___x_669_)) as u8;
                            if v_isSharedCheck_692_ == 0 {
                                v___x_687_ = v___x_669_;
                                v_isShared_688_ = v_isSharedCheck_692_;
                                state = 25;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_685_);
                                leanh::lean_dec(v___x_669_);
                                v___x_687_ = leanh::lean_box(0);
                                v_isShared_688_ = v_isSharedCheck_692_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_632_);
                    leanh::lean_dec_ref(v_proof_630_);
                    leanh::lean_dec_ref(v_e_x27_629_);
                    leanh::lean_dec_ref(v_arg_553_);
                    leanh::lean_dec_ref(v_e_537_);
                    v_a_693_ = leanh::lean_ctor_get(v___x_634_, 0);
                    v_isSharedCheck_700_ = (!leanh::lean_is_exclusive(v___x_634_)) as u8;
                    if v_isSharedCheck_700_ == 0 {
                        v___x_695_ = v___x_634_;
                        v_isShared_696_ = v_isSharedCheck_700_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_693_);
                        leanh::lean_dec(v___x_634_);
                        v___x_695_ = leanh::lean_box(0);
                        v_isShared_696_ = v_isSharedCheck_700_;
                        state = 27;
                        continue;
                    }
                }
            }
            16 => {
                v___x_642_ = (leanh::lean_unbox(v_a_638_) as u8);
                if v___x_642_ == 0 {
                    leanh::lean_dec(v_a_635_);
                    leanh::lean_del_object(v___x_632_);
                    leanh::lean_dec_ref(v_proof_630_);
                    leanh::lean_dec_ref(v_arg_553_);
                    leanh::lean_dec_ref(v_e_537_);
                    v___x_643_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    v___x_644_ = (leanh::lean_unbox(v_a_638_) as u8);
                    leanh::lean_ctor_set_uint8(v___x_643_, 0 as u32, v___x_644_);
                    v___x_645_ = (leanh::lean_unbox(v_a_638_) as u8);
                    leanh::lean_dec(v_a_638_);
                    leanh::lean_ctor_set_uint8(v___x_643_, 1 as u32, v___x_645_);
                    if v_isShared_641_ == 0 {
                        leanh::lean_ctor_set(v___x_640_, 0, v___x_643_);
                        v___x_647_ = v___x_640_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_648_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_643_);
                        v___x_647_ = v_reuseFailAlloc_648_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_638_);
                    v___x_649_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12;
                    v___x_650_ = l_Lean_Expr_replaceFn(v_e_537_, v___x_649_);
                    v___x_651_ = l_Lean_Expr_app___override(v___x_650_, v_proof_630_);
                    if v_isShared_633_ == 0 {
                        leanh::lean_ctor_set(v___x_632_, 1, v___x_651_);
                        leanh::lean_ctor_set(v___x_632_, 0, v_arg_553_);
                        v___x_653_ = v___x_632_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_659_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_659_, 0, v_arg_553_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_651_);
                        v___x_653_ = v_reuseFailAlloc_659_;
                        state = 18;
                        continue;
                    }
                }
            }
            17 => {
                return v___x_647_;
            }
            18 => {
                v___x_654_ = (leanh::lean_unbox(v_a_635_) as u8);
                leanh::lean_ctor_set_uint8(
                    v___x_653_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_654_,
                );
                v___x_655_ = (leanh::lean_unbox(v_a_635_) as u8);
                leanh::lean_dec(v_a_635_);
                leanh::lean_ctor_set_uint8(
                    v___x_653_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_655_,
                );
                if v_isShared_641_ == 0 {
                    leanh::lean_ctor_set(v___x_640_, 0, v___x_653_);
                    v___x_657_ = v___x_640_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_658_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_653_);
                    v___x_657_ = v_reuseFailAlloc_658_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_657_;
            }
            20 => {
                if v_isShared_664_ == 0 {
                    v___x_666_ = v___x_663_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_667_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
                    v___x_666_ = v_reuseFailAlloc_667_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_666_;
            }
            22 => {
                v___x_674_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14;
                v___x_675_ = l_Lean_Expr_replaceFn(v_e_537_, v___x_674_);
                v___x_676_ = l_Lean_Expr_app___override(v___x_675_, v_proof_630_);
                v___x_677_ = 0;
                if v_isShared_633_ == 0 {
                    leanh::lean_ctor_set(v___x_632_, 1, v___x_676_);
                    leanh::lean_ctor_set(v___x_632_, 0, v_a_670_);
                    v___x_679_ = v___x_632_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_676_);
                    v___x_679_ = v_reuseFailAlloc_683_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                leanh::lean_ctor_set_uint8(
                    v___x_679_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_559_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_679_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_677_,
                );
                if v_isShared_673_ == 0 {
                    leanh::lean_ctor_set(v___x_672_, 0, v___x_679_);
                    v___x_681_ = v___x_672_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
                    v___x_681_ = v_reuseFailAlloc_682_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_681_;
            }
            25 => {
                if v_isShared_688_ == 0 {
                    v___x_690_ = v___x_687_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_691_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
                    v___x_690_ = v_reuseFailAlloc_691_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_690_;
            }
            27 => {
                if v_isShared_696_ == 0 {
                    v___x_698_ = v___x_695_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
                    v___x_698_ = v_reuseFailAlloc_699_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___boxed(
    mut v_e_702_: *mut leanh::LeanObject,
    mut v_a_703_: *mut leanh::LeanObject,
    mut v_a_704_: *mut leanh::LeanObject,
    mut v_a_705_: *mut leanh::LeanObject,
    mut v_a_706_: *mut leanh::LeanObject,
    mut v_a_707_: *mut leanh::LeanObject,
    mut v_a_708_: *mut leanh::LeanObject,
    mut v_a_709_: *mut leanh::LeanObject,
    mut v_a_710_: *mut leanh::LeanObject,
    mut v_a_711_: *mut leanh::LeanObject,
    mut v_a_712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_713_ =
        l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr(
            v_e_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_,
            v_a_710_, v_a_711_,
        );
    leanh::lean_dec(v_a_711_);
    leanh::lean_dec_ref(v_a_710_);
    leanh::lean_dec(v_a_709_);
    leanh::lean_dec_ref(v_a_708_);
    leanh::lean_dec(v_a_707_);
    leanh::lean_dec_ref(v_a_706_);
    leanh::lean_dec(v_a_705_);
    leanh::lean_dec_ref(v_a_704_);
    leanh::lean_dec(v_a_703_);
    return v_res_713_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_()
-> *mut leanh::LeanObject {
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_772_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_;
    v___x_773_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_;
    v___x_774_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_775_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_772_, v___x_773_, v___x_774_);
    return v___x_775_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14____boxed(
    mut v_a_776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_777_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_();
    return v_res_777_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_16_()
-> *mut leanh::LeanObject {
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: u8 = 0;
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_779_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_;
    v___x_780_ = 0;
    v___x_781_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_782_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_779_, v___x_780_, v___x_781_);
    return v___x_782_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_16____boxed(
    mut v_a_783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_16_();
    return v_res_784_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_791_ = leanh::lean_box(0);
    v___x_792_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__3;
    v___x_793_ = l_Lean_mkConst(v___x_792_, v___x_791_);
    return v___x_793_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_797_ = leanh::lean_box(0);
    v___x_798_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__6;
    v___x_799_ = l_Lean_mkConst(v___x_798_, v___x_797_);
    return v___x_799_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd(
    mut v_e_810_: *mut leanh::LeanObject,
    mut v_a_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
    mut v_a_814_: *mut leanh::LeanObject,
    mut v_a_815_: *mut leanh::LeanObject,
    mut v_a_816_: *mut leanh::LeanObject,
    mut v_a_817_: *mut leanh::LeanObject,
    mut v_a_818_: *mut leanh::LeanObject,
    mut v_a_819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: u8 = 0;
    let mut v_arg_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: u8 = 0;
    let mut v_arg_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: u8 = 0;
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: u8 = 0;
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_845_: u8 = 0;
    let mut v___x_846_: u8 = 0;
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: u8 = 0;
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: u8 = 0;
    let mut v___x_859_: u8 = 0;
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut v_a_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_867_: u8 = 0;
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_871_: u8 = 0;
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_884_: u8 = 0;
    let mut v_a_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_892_: u8 = 0;
    let mut v_a_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_896_: u8 = 0;
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_900_: u8 = 0;
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_e_x27_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_906_: u8 = 0;
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: u8 = 0;
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_914_: u8 = 0;
    let mut v___x_915_: u8 = 0;
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: u8 = 0;
    let mut v___x_918_: u8 = 0;
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: u8 = 0;
    let mut v___x_928_: u8 = 0;
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut v_a_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_941_: u8 = 0;
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: u8 = 0;
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_a_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut v_a_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_973_: u8 = 0;
    let mut v_isSharedCheck_974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_810_);
                v___x_824_ = l_Lean_Expr_cleanupAnnotations(v_e_810_);
                v___x_825_ = l_Lean_Expr_isApp(v___x_824_);
                if v___x_825_ == 0 {
                    leanh::lean_dec_ref(v___x_824_);
                    leanh::lean_dec_ref(v_e_810_);
                    state = 1;
                    continue;
                } else {
                    v_arg_826_ = leanh::lean_ctor_get(v___x_824_, 1);
                    leanh::lean_inc_ref(v_arg_826_);
                    v___x_827_ = l_Lean_Expr_appFnCleanup___redArg(v___x_824_);
                    v___x_828_ = l_Lean_Expr_isApp(v___x_827_);
                    if v___x_828_ == 0 {
                        leanh::lean_dec_ref(v___x_827_);
                        leanh::lean_dec_ref(v_arg_826_);
                        leanh::lean_dec_ref(v_e_810_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_829_ = leanh::lean_ctor_get(v___x_827_, 1);
                        leanh::lean_inc_ref(v_arg_829_);
                        v___x_830_ = l_Lean_Expr_appFnCleanup___redArg(v___x_827_);
                        v___x_831_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1;
                        v___x_832_ = l_Lean_Expr_isConstOf(v___x_830_, v___x_831_);
                        leanh::lean_dec_ref(v___x_830_);
                        if v___x_832_ == 0 {
                            leanh::lean_dec_ref(v_arg_829_);
                            leanh::lean_dec_ref(v_arg_826_);
                            leanh::lean_dec_ref(v_e_810_);
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_819_);
                            leanh::lean_inc_ref(v_a_818_);
                            leanh::lean_inc(v_a_817_);
                            leanh::lean_inc_ref(v_a_816_);
                            leanh::lean_inc(v_a_815_);
                            leanh::lean_inc_ref(v_a_814_);
                            leanh::lean_inc(v_a_813_);
                            leanh::lean_inc_ref(v_a_812_);
                            leanh::lean_inc(v_a_811_);
                            leanh::lean_inc_ref(v_arg_829_);
                            v___x_833_ = lean_sym_simp(
                                v_arg_829_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_,
                                v_a_816_, v_a_817_, v_a_818_, v_a_819_,
                            );
                            if leanh::lean_obj_tag(v___x_833_) == 0 {
                                v_a_834_ = leanh::lean_ctor_get(v___x_833_, 0);
                                leanh::lean_inc(v_a_834_);
                                leanh::lean_dec_ref_known(v___x_833_, 1);
                                if leanh::lean_obj_tag(v_a_834_) == 0 {
                                    leanh::lean_dec_ref(v_e_810_);
                                    v_isSharedCheck_901_ =
                                        (!leanh::lean_is_exclusive(v_a_834_)) as u8;
                                    if v_isSharedCheck_901_ == 0 {
                                        v___x_836_ = v_a_834_;
                                        v_isShared_837_ = v_isSharedCheck_901_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_834_);
                                        v___x_836_ = leanh::lean_box(0);
                                        v_isShared_837_ = v_isSharedCheck_901_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_829_);
                                    v_e_x27_902_ = leanh::lean_ctor_get(v_a_834_, 0);
                                    v_proof_903_ = leanh::lean_ctor_get(v_a_834_, 1);
                                    v_isSharedCheck_974_ =
                                        (!leanh::lean_is_exclusive(v_a_834_)) as u8;
                                    if v_isSharedCheck_974_ == 0 {
                                        v___x_905_ = v_a_834_;
                                        v_isShared_906_ = v_isSharedCheck_974_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_proof_903_);
                                        leanh::lean_inc(v_e_x27_902_);
                                        leanh::lean_dec(v_a_834_);
                                        v___x_905_ = leanh::lean_box(0);
                                        v_isShared_906_ = v_isSharedCheck_974_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_arg_829_);
                                leanh::lean_dec_ref(v_arg_826_);
                                leanh::lean_dec_ref(v_e_810_);
                                return v___x_833_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_822_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0;
                v___x_823_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_823_, 0, v___x_822_);
                return v___x_823_;
            }
            2 => {
                v___x_838_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_829_, v_a_814_);
                if leanh::lean_obj_tag(v___x_838_) == 0 {
                    v_a_839_ = leanh::lean_ctor_get(v___x_838_, 0);
                    leanh::lean_inc(v_a_839_);
                    leanh::lean_dec_ref_known(v___x_838_, 1);
                    v___x_840_ = (leanh::lean_unbox(v_a_839_) as u8);
                    if v___x_840_ == 0 {
                        v___x_841_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_829_, v_a_814_);
                        leanh::lean_dec_ref(v_arg_829_);
                        if leanh::lean_obj_tag(v___x_841_) == 0 {
                            v_a_842_ = leanh::lean_ctor_get(v___x_841_, 0);
                            v_isSharedCheck_863_ =
                                (!leanh::lean_is_exclusive(v___x_841_)) as u8;
                            if v_isSharedCheck_863_ == 0 {
                                v___x_844_ = v___x_841_;
                                v_isShared_845_ = v_isSharedCheck_863_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_842_);
                                leanh::lean_dec(v___x_841_);
                                v___x_844_ = leanh::lean_box(0);
                                v_isShared_845_ = v_isSharedCheck_863_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_839_);
                            leanh::lean_del_object(v___x_836_);
                            leanh::lean_dec_ref(v_arg_826_);
                            v_a_864_ = leanh::lean_ctor_get(v___x_841_, 0);
                            v_isSharedCheck_871_ =
                                (!leanh::lean_is_exclusive(v___x_841_)) as u8;
                            if v_isSharedCheck_871_ == 0 {
                                v___x_866_ = v___x_841_;
                                v_isShared_867_ = v_isSharedCheck_871_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_864_);
                                leanh::lean_dec(v___x_841_);
                                v___x_866_ = leanh::lean_box(0);
                                v_isShared_867_ = v_isSharedCheck_871_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_839_);
                        leanh::lean_del_object(v___x_836_);
                        leanh::lean_dec_ref(v_arg_829_);
                        v___x_872_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_814_);
                        if leanh::lean_obj_tag(v___x_872_) == 0 {
                            v_a_873_ = leanh::lean_ctor_get(v___x_872_, 0);
                            v_isSharedCheck_884_ =
                                (!leanh::lean_is_exclusive(v___x_872_)) as u8;
                            if v_isSharedCheck_884_ == 0 {
                                v___x_875_ = v___x_872_;
                                v_isShared_876_ = v_isSharedCheck_884_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_873_);
                                leanh::lean_dec(v___x_872_);
                                v___x_875_ = leanh::lean_box(0);
                                v_isShared_876_ = v_isSharedCheck_884_;
                                state = 9;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_826_);
                            v_a_885_ = leanh::lean_ctor_get(v___x_872_, 0);
                            v_isSharedCheck_892_ =
                                (!leanh::lean_is_exclusive(v___x_872_)) as u8;
                            if v_isSharedCheck_892_ == 0 {
                                v___x_887_ = v___x_872_;
                                v_isShared_888_ = v_isSharedCheck_892_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_885_);
                                leanh::lean_dec(v___x_872_);
                                v___x_887_ = leanh::lean_box(0);
                                v_isShared_888_ = v_isSharedCheck_892_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_836_);
                    leanh::lean_dec_ref(v_arg_829_);
                    leanh::lean_dec_ref(v_arg_826_);
                    v_a_893_ = leanh::lean_ctor_get(v___x_838_, 0);
                    v_isSharedCheck_900_ = (!leanh::lean_is_exclusive(v___x_838_)) as u8;
                    if v_isSharedCheck_900_ == 0 {
                        v___x_895_ = v___x_838_;
                        v_isShared_896_ = v_isSharedCheck_900_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_893_);
                        leanh::lean_dec(v___x_838_);
                        v___x_895_ = leanh::lean_box(0);
                        v_isShared_896_ = v_isSharedCheck_900_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => {
                v___x_846_ = (leanh::lean_unbox(v_a_842_) as u8);
                if v___x_846_ == 0 {
                    leanh::lean_dec(v_a_839_);
                    leanh::lean_dec_ref(v_arg_826_);
                    if v_isShared_837_ == 0 {
                        v___x_848_ = v___x_836_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_854_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                        v___x_848_ = v_reuseFailAlloc_854_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_842_);
                    leanh::lean_del_object(v___x_836_);
                    v___x_855_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4_once), _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4);
                    leanh::lean_inc_ref(v_arg_826_);
                    v___x_856_ = l_Lean_Expr_app___override(v___x_855_, v_arg_826_);
                    v___x_857_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v___x_857_, 0, v_arg_826_);
                    leanh::lean_ctor_set(v___x_857_, 1, v___x_856_);
                    v___x_858_ = (leanh::lean_unbox(v_a_839_) as u8);
                    leanh::lean_ctor_set_uint8(
                        v___x_857_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_858_,
                    );
                    v___x_859_ = (leanh::lean_unbox(v_a_839_) as u8);
                    leanh::lean_dec(v_a_839_);
                    leanh::lean_ctor_set_uint8(
                        v___x_857_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v___x_859_,
                    );
                    if v_isShared_845_ == 0 {
                        leanh::lean_ctor_set(v___x_844_, 0, v___x_857_);
                        v___x_861_ = v___x_844_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_857_);
                        v___x_861_ = v_reuseFailAlloc_862_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_849_ = (leanh::lean_unbox(v_a_842_) as u8);
                leanh::lean_ctor_set_uint8(v___x_848_, 0 as u32, v___x_849_);
                v___x_850_ = (leanh::lean_unbox(v_a_842_) as u8);
                leanh::lean_dec(v_a_842_);
                leanh::lean_ctor_set_uint8(v___x_848_, 1 as u32, v___x_850_);
                if v_isShared_845_ == 0 {
                    leanh::lean_ctor_set(v___x_844_, 0, v___x_848_);
                    v___x_852_ = v___x_844_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_853_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_848_);
                    v___x_852_ = v_reuseFailAlloc_853_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_852_;
            }
            6 => {
                return v___x_861_;
            }
            7 => {
                if v_isShared_867_ == 0 {
                    v___x_869_ = v___x_866_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_870_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
                    v___x_869_ = v_reuseFailAlloc_870_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_869_;
            }
            9 => {
                v___x_877_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7_once), _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7);
                v___x_878_ = l_Lean_Expr_app___override(v___x_877_, v_arg_826_);
                v___x_879_ = 0;
                v___x_880_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_880_, 0, v_a_873_);
                leanh::lean_ctor_set(v___x_880_, 1, v___x_878_);
                leanh::lean_ctor_set_uint8(
                    v___x_880_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_832_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_880_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_879_,
                );
                if v_isShared_876_ == 0 {
                    leanh::lean_ctor_set(v___x_875_, 0, v___x_880_);
                    v___x_882_ = v___x_875_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
                    v___x_882_ = v_reuseFailAlloc_883_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_882_;
            }
            11 => {
                if v_isShared_888_ == 0 {
                    v___x_890_ = v___x_887_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_891_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
                    v___x_890_ = v_reuseFailAlloc_891_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_890_;
            }
            13 => {
                if v_isShared_896_ == 0 {
                    v___x_898_ = v___x_895_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_899_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
                    v___x_898_ = v_reuseFailAlloc_899_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_898_;
            }
            15 => {
                v___x_907_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_902_, v_a_814_);
                if leanh::lean_obj_tag(v___x_907_) == 0 {
                    v_a_908_ = leanh::lean_ctor_get(v___x_907_, 0);
                    leanh::lean_inc(v_a_908_);
                    leanh::lean_dec_ref_known(v___x_907_, 1);
                    v___x_909_ = (leanh::lean_unbox(v_a_908_) as u8);
                    if v___x_909_ == 0 {
                        v___x_910_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_902_, v_a_814_);
                        leanh::lean_dec_ref(v_e_x27_902_);
                        if leanh::lean_obj_tag(v___x_910_) == 0 {
                            v_a_911_ = leanh::lean_ctor_get(v___x_910_, 0);
                            v_isSharedCheck_933_ =
                                (!leanh::lean_is_exclusive(v___x_910_)) as u8;
                            if v_isSharedCheck_933_ == 0 {
                                v___x_913_ = v___x_910_;
                                v_isShared_914_ = v_isSharedCheck_933_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_911_);
                                leanh::lean_dec(v___x_910_);
                                v___x_913_ = leanh::lean_box(0);
                                v_isShared_914_ = v_isSharedCheck_933_;
                                state = 16;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_908_);
                            leanh::lean_del_object(v___x_905_);
                            leanh::lean_dec_ref(v_proof_903_);
                            leanh::lean_dec_ref(v_arg_826_);
                            leanh::lean_dec_ref(v_e_810_);
                            v_a_934_ = leanh::lean_ctor_get(v___x_910_, 0);
                            v_isSharedCheck_941_ =
                                (!leanh::lean_is_exclusive(v___x_910_)) as u8;
                            if v_isSharedCheck_941_ == 0 {
                                v___x_936_ = v___x_910_;
                                v_isShared_937_ = v_isSharedCheck_941_;
                                state = 20;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_934_);
                                leanh::lean_dec(v___x_910_);
                                v___x_936_ = leanh::lean_box(0);
                                v_isShared_937_ = v_isSharedCheck_941_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_908_);
                        leanh::lean_dec_ref(v_e_x27_902_);
                        leanh::lean_dec_ref(v_arg_826_);
                        v___x_942_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_814_);
                        if leanh::lean_obj_tag(v___x_942_) == 0 {
                            v_a_943_ = leanh::lean_ctor_get(v___x_942_, 0);
                            v_isSharedCheck_957_ =
                                (!leanh::lean_is_exclusive(v___x_942_)) as u8;
                            if v_isSharedCheck_957_ == 0 {
                                v___x_945_ = v___x_942_;
                                v_isShared_946_ = v_isSharedCheck_957_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_943_);
                                leanh::lean_dec(v___x_942_);
                                v___x_945_ = leanh::lean_box(0);
                                v_isShared_946_ = v_isSharedCheck_957_;
                                state = 22;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_905_);
                            leanh::lean_dec_ref(v_proof_903_);
                            leanh::lean_dec_ref(v_e_810_);
                            v_a_958_ = leanh::lean_ctor_get(v___x_942_, 0);
                            v_isSharedCheck_965_ =
                                (!leanh::lean_is_exclusive(v___x_942_)) as u8;
                            if v_isSharedCheck_965_ == 0 {
                                v___x_960_ = v___x_942_;
                                v_isShared_961_ = v_isSharedCheck_965_;
                                state = 25;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_958_);
                                leanh::lean_dec(v___x_942_);
                                v___x_960_ = leanh::lean_box(0);
                                v_isShared_961_ = v_isSharedCheck_965_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_905_);
                    leanh::lean_dec_ref(v_proof_903_);
                    leanh::lean_dec_ref(v_e_x27_902_);
                    leanh::lean_dec_ref(v_arg_826_);
                    leanh::lean_dec_ref(v_e_810_);
                    v_a_966_ = leanh::lean_ctor_get(v___x_907_, 0);
                    v_isSharedCheck_973_ = (!leanh::lean_is_exclusive(v___x_907_)) as u8;
                    if v_isSharedCheck_973_ == 0 {
                        v___x_968_ = v___x_907_;
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_966_);
                        leanh::lean_dec(v___x_907_);
                        v___x_968_ = leanh::lean_box(0);
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 27;
                        continue;
                    }
                }
            }
            16 => {
                v___x_915_ = (leanh::lean_unbox(v_a_911_) as u8);
                if v___x_915_ == 0 {
                    leanh::lean_dec(v_a_908_);
                    leanh::lean_del_object(v___x_905_);
                    leanh::lean_dec_ref(v_proof_903_);
                    leanh::lean_dec_ref(v_arg_826_);
                    leanh::lean_dec_ref(v_e_810_);
                    v___x_916_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    v___x_917_ = (leanh::lean_unbox(v_a_911_) as u8);
                    leanh::lean_ctor_set_uint8(v___x_916_, 0 as u32, v___x_917_);
                    v___x_918_ = (leanh::lean_unbox(v_a_911_) as u8);
                    leanh::lean_dec(v_a_911_);
                    leanh::lean_ctor_set_uint8(v___x_916_, 1 as u32, v___x_918_);
                    if v_isShared_914_ == 0 {
                        leanh::lean_ctor_set(v___x_913_, 0, v___x_916_);
                        v___x_920_ = v___x_913_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_921_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_916_);
                        v___x_920_ = v_reuseFailAlloc_921_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_911_);
                    v___x_922_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9;
                    v___x_923_ = l_Lean_Expr_replaceFn(v_e_810_, v___x_922_);
                    v___x_924_ = l_Lean_Expr_app___override(v___x_923_, v_proof_903_);
                    if v_isShared_906_ == 0 {
                        leanh::lean_ctor_set(v___x_905_, 1, v___x_924_);
                        leanh::lean_ctor_set(v___x_905_, 0, v_arg_826_);
                        v___x_926_ = v___x_905_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_932_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_932_, 0, v_arg_826_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_924_);
                        v___x_926_ = v_reuseFailAlloc_932_;
                        state = 18;
                        continue;
                    }
                }
            }
            17 => {
                return v___x_920_;
            }
            18 => {
                v___x_927_ = (leanh::lean_unbox(v_a_908_) as u8);
                leanh::lean_ctor_set_uint8(
                    v___x_926_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_927_,
                );
                v___x_928_ = (leanh::lean_unbox(v_a_908_) as u8);
                leanh::lean_dec(v_a_908_);
                leanh::lean_ctor_set_uint8(
                    v___x_926_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_928_,
                );
                if v_isShared_914_ == 0 {
                    leanh::lean_ctor_set(v___x_913_, 0, v___x_926_);
                    v___x_930_ = v___x_913_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_931_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_926_);
                    v___x_930_ = v_reuseFailAlloc_931_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_930_;
            }
            20 => {
                if v_isShared_937_ == 0 {
                    v___x_939_ = v___x_936_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_940_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
                    v___x_939_ = v_reuseFailAlloc_940_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_939_;
            }
            22 => {
                v___x_947_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11;
                v___x_948_ = l_Lean_Expr_replaceFn(v_e_810_, v___x_947_);
                v___x_949_ = l_Lean_Expr_app___override(v___x_948_, v_proof_903_);
                v___x_950_ = 0;
                if v_isShared_906_ == 0 {
                    leanh::lean_ctor_set(v___x_905_, 1, v___x_949_);
                    leanh::lean_ctor_set(v___x_905_, 0, v_a_943_);
                    v___x_952_ = v___x_905_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_956_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_943_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_949_);
                    v___x_952_ = v_reuseFailAlloc_956_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                leanh::lean_ctor_set_uint8(
                    v___x_952_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_832_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_952_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_950_,
                );
                if v_isShared_946_ == 0 {
                    leanh::lean_ctor_set(v___x_945_, 0, v___x_952_);
                    v___x_954_ = v___x_945_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_955_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
                    v___x_954_ = v_reuseFailAlloc_955_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_954_;
            }
            25 => {
                if v_isShared_961_ == 0 {
                    v___x_963_ = v___x_960_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_964_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
                    v___x_963_ = v_reuseFailAlloc_964_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_963_;
            }
            27 => {
                if v_isShared_969_ == 0 {
                    v___x_971_ = v___x_968_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_972_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
                    v___x_971_ = v_reuseFailAlloc_972_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___boxed(
    mut v_e_975_: *mut leanh::LeanObject,
    mut v_a_976_: *mut leanh::LeanObject,
    mut v_a_977_: *mut leanh::LeanObject,
    mut v_a_978_: *mut leanh::LeanObject,
    mut v_a_979_: *mut leanh::LeanObject,
    mut v_a_980_: *mut leanh::LeanObject,
    mut v_a_981_: *mut leanh::LeanObject,
    mut v_a_982_: *mut leanh::LeanObject,
    mut v_a_983_: *mut leanh::LeanObject,
    mut v_a_984_: *mut leanh::LeanObject,
    mut v_a_985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_986_ =
        l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd(
            v_e_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_,
            v_a_983_, v_a_984_,
        );
    leanh::lean_dec(v_a_984_);
    leanh::lean_dec_ref(v_a_983_);
    leanh::lean_dec(v_a_982_);
    leanh::lean_dec_ref(v_a_981_);
    leanh::lean_dec(v_a_980_);
    leanh::lean_dec_ref(v_a_979_);
    leanh::lean_dec(v_a_978_);
    leanh::lean_dec_ref(v_a_977_);
    leanh::lean_dec(v_a_976_);
    return v_res_986_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_()
-> *mut leanh::LeanObject {
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1002_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_;
    v___x_1003_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_;
    v___x_1004_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_1005_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1002_, v___x_1003_, v___x_1004_);
    return v___x_1005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14____boxed(
    mut v_a_1006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1007_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_();
    return v_res_1007_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_16_()
-> *mut leanh::LeanObject {
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: u8 = 0;
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_;
    v___x_1010_ = 0;
    v___x_1011_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_1012_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1009_, v___x_1010_, v___x_1011_);
    return v___x_1012_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_16____boxed(
    mut v_a_1013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1014_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_16_();
    return v_res_1014_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Sym_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_16_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_16_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Sym_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(builtin);
}