// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.Core
// Imports: Lean.Meta.Sym.Simp.SimpM Init.Sym.Lemmas Init.CbvSimproc Lean.Meta.Tactic.Cbv.CbvSimproc
use crate::r#gen::Init::CbvSimproc::{
    initialize_Init_CbvSimproc, runtime_initialize_Init_CbvSimproc,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_num___override, l_Lean_Name_str___override,
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
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Lean::Meta::Sym::Simp::SimpM::lean_sym_simp;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
};
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [79, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__1_value) as *mut LeanObject,14181099489592536354 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [102, 97, 108, 115, 101, 95, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__3_value) as *mut LeanObject,7030941873239652894 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__6_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 117, 101, 95, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__6_value) as *mut LeanObject,3037741586801491095 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__11_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [111, 114, 95, 101, 113, 95, 114, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__11_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut LeanObject,3782814055319769887 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__11_value) as *mut LeanObject,13300370967057954325 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__13_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [111, 114, 95, 101, 113, 95, 116, 114, 117, 101, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__13_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut LeanObject,3782814055319769887 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__13_value) as *mut LeanObject,1011184777873256822 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,16489734963670585437 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [66, 117, 105, 108, 116, 105, 110, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,8524095998741210685 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,13795083944981294805 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,219597323698272320 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut LeanObject,1411255169149101689 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,12139464363154525161 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut LeanObject,17876964083007659580 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,17009103051292104096 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 79, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,12054117545489417188 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2_value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value: LeanArrayObject<3> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__0_value) as *mut LeanObject,9743492140944907313 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 114, 117, 101, 95, 97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__2_value) as *mut LeanObject,17391556055311371073 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 97, 108, 115, 101, 95, 97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__5_value) as *mut LeanObject,4492176092438480580 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__8_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 110, 100, 95, 101, 113, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__8_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut LeanObject,3782814055319769887 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__8_value) as *mut LeanObject,679327600139009352 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__10_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [97, 110, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__9_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__10_value) as *mut LeanObject,3782814055319769887 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__10_value) as *mut LeanObject,10479839610626251338 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 105, 109, 112, 65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut LeanObject,17397356683693532514 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1_value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value: LeanArrayObject<3> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14__value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5()
-> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = lean_box(0);
    v___x_517_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__4;
    v___x_518_ = l_Lean_mkConst(v___x_517_, v___x_516_);
    return v___x_518_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8()
-> *mut LeanObject {
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    v___x_522_ = lean_box(0);
    v___x_523_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__7;
    v___x_524_ = l_Lean_mkConst(v___x_523_, v___x_522_);
    return v___x_524_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr(
    mut v_e_537_: *mut LeanObject,
    mut v_a_538_: *mut LeanObject,
    mut v_a_539_: *mut LeanObject,
    mut v_a_540_: *mut LeanObject,
    mut v_a_541_: *mut LeanObject,
    mut v_a_542_: *mut LeanObject,
    mut v_a_543_: *mut LeanObject,
    mut v_a_544_: *mut LeanObject,
    mut v_a_545_: *mut LeanObject,
    mut v_a_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: u8 = 0;
    let mut v_arg_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: u8 = 0;
    let mut v_arg_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: u8 = 0;
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_564_: u8 = 0;
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: u8 = 0;
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_573_: u8 = 0;
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut v___x_577_: u8 = 0;
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v_a_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v_a_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_a_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_isSharedCheck_628_: u8 = 0;
    let mut v_e_x27_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_633_: u8 = 0;
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: u8 = 0;
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v___x_642_: u8 = 0;
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: u8 = 0;
    let mut v___x_645_: u8 = 0;
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    let mut v___x_655_: u8 = 0;
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut v_a_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_664_: u8 = 0;
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut v_a_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_688_: u8 = 0;
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_692_: u8 = 0;
    let mut v_a_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_696_: u8 = 0;
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_700_: u8 = 0;
    let mut v_isSharedCheck_701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_537_);
                v___x_551_ = l_Lean_Expr_cleanupAnnotations(v_e_537_);
                v___x_552_ = l_Lean_Expr_isApp(v___x_551_);
                if v___x_552_ == 0 {
                    lean_dec_ref(v___x_551_);
                    lean_dec_ref(v_e_537_);
                    state = 1;
                    continue;
                } else {
                    v_arg_553_ = lean_ctor_get(v___x_551_, 1);
                    lean_inc_ref(v_arg_553_);
                    v___x_554_ = l_Lean_Expr_appFnCleanup___redArg(v___x_551_);
                    v___x_555_ = l_Lean_Expr_isApp(v___x_554_);
                    if v___x_555_ == 0 {
                        lean_dec_ref(v___x_554_);
                        lean_dec_ref(v_arg_553_);
                        lean_dec_ref(v_e_537_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_556_ = lean_ctor_get(v___x_554_, 1);
                        lean_inc_ref(v_arg_556_);
                        v___x_557_ = l_Lean_Expr_appFnCleanup___redArg(v___x_554_);
                        v___x_558_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__2;
                        v___x_559_ = l_Lean_Expr_isConstOf(v___x_557_, v___x_558_);
                        lean_dec_ref(v___x_557_);
                        if v___x_559_ == 0 {
                            lean_dec_ref(v_arg_556_);
                            lean_dec_ref(v_arg_553_);
                            lean_dec_ref(v_e_537_);
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_546_);
                            lean_inc_ref(v_a_545_);
                            lean_inc(v_a_544_);
                            lean_inc_ref(v_a_543_);
                            lean_inc(v_a_542_);
                            lean_inc_ref(v_a_541_);
                            lean_inc(v_a_540_);
                            lean_inc_ref(v_a_539_);
                            lean_inc(v_a_538_);
                            lean_inc_ref(v_arg_556_);
                            v___x_560_ = lean_sym_simp(
                                v_arg_556_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_,
                                v_a_543_, v_a_544_, v_a_545_, v_a_546_,
                            );
                            if lean_obj_tag(v___x_560_) == 0 {
                                v_a_561_ = lean_ctor_get(v___x_560_, 0);
                                lean_inc(v_a_561_);
                                lean_dec_ref_known(v___x_560_, 1);
                                if lean_obj_tag(v_a_561_) == 0 {
                                    lean_dec_ref(v_e_537_);
                                    v_isSharedCheck_628_ = (!lean_is_exclusive(v_a_561_)) as u8;
                                    if v_isSharedCheck_628_ == 0 {
                                        v___x_563_ = v_a_561_;
                                        v_isShared_564_ = v_isSharedCheck_628_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v_a_561_);
                                        v___x_563_ = lean_box(0);
                                        v_isShared_564_ = v_isSharedCheck_628_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_556_);
                                    v_e_x27_629_ = lean_ctor_get(v_a_561_, 0);
                                    v_proof_630_ = lean_ctor_get(v_a_561_, 1);
                                    v_isSharedCheck_701_ = (!lean_is_exclusive(v_a_561_)) as u8;
                                    if v_isSharedCheck_701_ == 0 {
                                        v___x_632_ = v_a_561_;
                                        v_isShared_633_ = v_isSharedCheck_701_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_proof_630_);
                                        lean_inc(v_e_x27_629_);
                                        lean_dec(v_a_561_);
                                        v___x_632_ = lean_box(0);
                                        v_isShared_633_ = v_isSharedCheck_701_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_arg_556_);
                                lean_dec_ref(v_arg_553_);
                                lean_dec_ref(v_e_537_);
                                return v___x_560_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_549_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0;
                v___x_550_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_550_, 0, v___x_549_);
                return v___x_550_;
            }
            2 => {
                v___x_565_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_556_, v_a_541_);
                if lean_obj_tag(v___x_565_) == 0 {
                    v_a_566_ = lean_ctor_get(v___x_565_, 0);
                    lean_inc(v_a_566_);
                    lean_dec_ref_known(v___x_565_, 1);
                    v___x_567_ = (lean_unbox(v_a_566_) as u8);
                    if v___x_567_ == 0 {
                        v___x_568_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_556_, v_a_541_);
                        lean_dec_ref(v_arg_556_);
                        if lean_obj_tag(v___x_568_) == 0 {
                            v_a_569_ = lean_ctor_get(v___x_568_, 0);
                            v_isSharedCheck_590_ = (!lean_is_exclusive(v___x_568_)) as u8;
                            if v_isSharedCheck_590_ == 0 {
                                v___x_571_ = v___x_568_;
                                v_isShared_572_ = v_isSharedCheck_590_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_569_);
                                lean_dec(v___x_568_);
                                v___x_571_ = lean_box(0);
                                v_isShared_572_ = v_isSharedCheck_590_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_566_);
                            lean_del_object(v___x_563_);
                            lean_dec_ref(v_arg_553_);
                            v_a_591_ = lean_ctor_get(v___x_568_, 0);
                            v_isSharedCheck_598_ = (!lean_is_exclusive(v___x_568_)) as u8;
                            if v_isSharedCheck_598_ == 0 {
                                v___x_593_ = v___x_568_;
                                v_isShared_594_ = v_isSharedCheck_598_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_591_);
                                lean_dec(v___x_568_);
                                v___x_593_ = lean_box(0);
                                v_isShared_594_ = v_isSharedCheck_598_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_566_);
                        lean_del_object(v___x_563_);
                        lean_dec_ref(v_arg_556_);
                        v___x_599_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_541_);
                        if lean_obj_tag(v___x_599_) == 0 {
                            v_a_600_ = lean_ctor_get(v___x_599_, 0);
                            v_isSharedCheck_611_ = (!lean_is_exclusive(v___x_599_)) as u8;
                            if v_isSharedCheck_611_ == 0 {
                                v___x_602_ = v___x_599_;
                                v_isShared_603_ = v_isSharedCheck_611_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_600_);
                                lean_dec(v___x_599_);
                                v___x_602_ = lean_box(0);
                                v_isShared_603_ = v_isSharedCheck_611_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_arg_553_);
                            v_a_612_ = lean_ctor_get(v___x_599_, 0);
                            v_isSharedCheck_619_ = (!lean_is_exclusive(v___x_599_)) as u8;
                            if v_isSharedCheck_619_ == 0 {
                                v___x_614_ = v___x_599_;
                                v_isShared_615_ = v_isSharedCheck_619_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_612_);
                                lean_dec(v___x_599_);
                                v___x_614_ = lean_box(0);
                                v_isShared_615_ = v_isSharedCheck_619_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_563_);
                    lean_dec_ref(v_arg_556_);
                    lean_dec_ref(v_arg_553_);
                    v_a_620_ = lean_ctor_get(v___x_565_, 0);
                    v_isSharedCheck_627_ = (!lean_is_exclusive(v___x_565_)) as u8;
                    if v_isSharedCheck_627_ == 0 {
                        v___x_622_ = v___x_565_;
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_620_);
                        lean_dec(v___x_565_);
                        v___x_622_ = lean_box(0);
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => {
                v___x_573_ = (lean_unbox(v_a_569_) as u8);
                if v___x_573_ == 0 {
                    lean_dec(v_a_566_);
                    lean_dec_ref(v_arg_553_);
                    if v_isShared_564_ == 0 {
                        v___x_575_ = v___x_563_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 0, (2) as u32);
                        v___x_575_ = v_reuseFailAlloc_581_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_569_);
                    lean_del_object(v___x_563_);
                    v___x_582_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5_once), _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__5);
                    lean_inc_ref(v_arg_553_);
                    v___x_583_ = l_Lean_Expr_app___override(v___x_582_, v_arg_553_);
                    v___x_584_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v___x_584_, 0, v_arg_553_);
                    lean_ctor_set(v___x_584_, 1, v___x_583_);
                    v___x_585_ = (lean_unbox(v_a_566_) as u8);
                    lean_ctor_set_uint8(
                        v___x_584_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_585_,
                    );
                    v___x_586_ = (lean_unbox(v_a_566_) as u8);
                    lean_dec(v_a_566_);
                    lean_ctor_set_uint8(
                        v___x_584_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        v___x_586_,
                    );
                    if v_isShared_572_ == 0 {
                        lean_ctor_set(v___x_571_, 0, v___x_584_);
                        v___x_588_ = v___x_571_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_584_);
                        v___x_588_ = v_reuseFailAlloc_589_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_576_ = (lean_unbox(v_a_569_) as u8);
                lean_ctor_set_uint8(v___x_575_, 0 as u32, v___x_576_);
                v___x_577_ = (lean_unbox(v_a_569_) as u8);
                lean_dec(v_a_569_);
                lean_ctor_set_uint8(v___x_575_, 1 as u32, v___x_577_);
                if v_isShared_572_ == 0 {
                    lean_ctor_set(v___x_571_, 0, v___x_575_);
                    v___x_579_ = v___x_571_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_575_);
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
                    v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
                    v___x_596_ = v_reuseFailAlloc_597_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_596_;
            }
            9 => {
                v___x_604_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8_once), _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__8);
                v___x_605_ = l_Lean_Expr_app___override(v___x_604_, v_arg_553_);
                v___x_606_ = 0;
                v___x_607_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_607_, 0, v_a_600_);
                lean_ctor_set(v___x_607_, 1, v___x_605_);
                lean_ctor_set_uint8(
                    v___x_607_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_559_,
                );
                lean_ctor_set_uint8(
                    v___x_607_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___x_606_,
                );
                if v_isShared_603_ == 0 {
                    lean_ctor_set(v___x_602_, 0, v___x_607_);
                    v___x_609_ = v___x_602_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
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
                    v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
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
                    v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
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
                if lean_obj_tag(v___x_634_) == 0 {
                    v_a_635_ = lean_ctor_get(v___x_634_, 0);
                    lean_inc(v_a_635_);
                    lean_dec_ref_known(v___x_634_, 1);
                    v___x_636_ = (lean_unbox(v_a_635_) as u8);
                    if v___x_636_ == 0 {
                        v___x_637_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_629_, v_a_541_);
                        lean_dec_ref(v_e_x27_629_);
                        if lean_obj_tag(v___x_637_) == 0 {
                            v_a_638_ = lean_ctor_get(v___x_637_, 0);
                            v_isSharedCheck_660_ = (!lean_is_exclusive(v___x_637_)) as u8;
                            if v_isSharedCheck_660_ == 0 {
                                v___x_640_ = v___x_637_;
                                v_isShared_641_ = v_isSharedCheck_660_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_638_);
                                lean_dec(v___x_637_);
                                v___x_640_ = lean_box(0);
                                v_isShared_641_ = v_isSharedCheck_660_;
                                state = 16;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_635_);
                            lean_del_object(v___x_632_);
                            lean_dec_ref(v_proof_630_);
                            lean_dec_ref(v_arg_553_);
                            lean_dec_ref(v_e_537_);
                            v_a_661_ = lean_ctor_get(v___x_637_, 0);
                            v_isSharedCheck_668_ = (!lean_is_exclusive(v___x_637_)) as u8;
                            if v_isSharedCheck_668_ == 0 {
                                v___x_663_ = v___x_637_;
                                v_isShared_664_ = v_isSharedCheck_668_;
                                state = 20;
                                continue;
                            } else {
                                lean_inc(v_a_661_);
                                lean_dec(v___x_637_);
                                v___x_663_ = lean_box(0);
                                v_isShared_664_ = v_isSharedCheck_668_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_635_);
                        lean_dec_ref(v_e_x27_629_);
                        lean_dec_ref(v_arg_553_);
                        v___x_669_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_541_);
                        if lean_obj_tag(v___x_669_) == 0 {
                            v_a_670_ = lean_ctor_get(v___x_669_, 0);
                            v_isSharedCheck_684_ = (!lean_is_exclusive(v___x_669_)) as u8;
                            if v_isSharedCheck_684_ == 0 {
                                v___x_672_ = v___x_669_;
                                v_isShared_673_ = v_isSharedCheck_684_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_a_670_);
                                lean_dec(v___x_669_);
                                v___x_672_ = lean_box(0);
                                v_isShared_673_ = v_isSharedCheck_684_;
                                state = 22;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_632_);
                            lean_dec_ref(v_proof_630_);
                            lean_dec_ref(v_e_537_);
                            v_a_685_ = lean_ctor_get(v___x_669_, 0);
                            v_isSharedCheck_692_ = (!lean_is_exclusive(v___x_669_)) as u8;
                            if v_isSharedCheck_692_ == 0 {
                                v___x_687_ = v___x_669_;
                                v_isShared_688_ = v_isSharedCheck_692_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_685_);
                                lean_dec(v___x_669_);
                                v___x_687_ = lean_box(0);
                                v_isShared_688_ = v_isSharedCheck_692_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_632_);
                    lean_dec_ref(v_proof_630_);
                    lean_dec_ref(v_e_x27_629_);
                    lean_dec_ref(v_arg_553_);
                    lean_dec_ref(v_e_537_);
                    v_a_693_ = lean_ctor_get(v___x_634_, 0);
                    v_isSharedCheck_700_ = (!lean_is_exclusive(v___x_634_)) as u8;
                    if v_isSharedCheck_700_ == 0 {
                        v___x_695_ = v___x_634_;
                        v_isShared_696_ = v_isSharedCheck_700_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_693_);
                        lean_dec(v___x_634_);
                        v___x_695_ = lean_box(0);
                        v_isShared_696_ = v_isSharedCheck_700_;
                        state = 27;
                        continue;
                    }
                }
            }
            16 => {
                v___x_642_ = (lean_unbox(v_a_638_) as u8);
                if v___x_642_ == 0 {
                    lean_dec(v_a_635_);
                    lean_del_object(v___x_632_);
                    lean_dec_ref(v_proof_630_);
                    lean_dec_ref(v_arg_553_);
                    lean_dec_ref(v_e_537_);
                    v___x_643_ = lean_alloc_ctor(0, 0, (2) as u32);
                    v___x_644_ = (lean_unbox(v_a_638_) as u8);
                    lean_ctor_set_uint8(v___x_643_, 0 as u32, v___x_644_);
                    v___x_645_ = (lean_unbox(v_a_638_) as u8);
                    lean_dec(v_a_638_);
                    lean_ctor_set_uint8(v___x_643_, 1 as u32, v___x_645_);
                    if v_isShared_641_ == 0 {
                        lean_ctor_set(v___x_640_, 0, v___x_643_);
                        v___x_647_ = v___x_640_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_643_);
                        v___x_647_ = v_reuseFailAlloc_648_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec(v_a_638_);
                    v___x_649_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__12;
                    v___x_650_ = l_Lean_Expr_replaceFn(v_e_537_, v___x_649_);
                    v___x_651_ = l_Lean_Expr_app___override(v___x_650_, v_proof_630_);
                    if v_isShared_633_ == 0 {
                        lean_ctor_set(v___x_632_, 1, v___x_651_);
                        lean_ctor_set(v___x_632_, 0, v_arg_553_);
                        v___x_653_ = v___x_632_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 2, (2) as u32);
                        lean_ctor_set(v_reuseFailAlloc_659_, 0, v_arg_553_);
                        lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_651_);
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
                v___x_654_ = (lean_unbox(v_a_635_) as u8);
                lean_ctor_set_uint8(
                    v___x_653_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_654_,
                );
                v___x_655_ = (lean_unbox(v_a_635_) as u8);
                lean_dec(v_a_635_);
                lean_ctor_set_uint8(
                    v___x_653_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___x_655_,
                );
                if v_isShared_641_ == 0 {
                    lean_ctor_set(v___x_640_, 0, v___x_653_);
                    v___x_657_ = v___x_640_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_653_);
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
                    v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
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
                    lean_ctor_set(v___x_632_, 1, v___x_676_);
                    lean_ctor_set(v___x_632_, 0, v_a_670_);
                    v___x_679_ = v___x_632_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_670_);
                    lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_676_);
                    v___x_679_ = v_reuseFailAlloc_683_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                lean_ctor_set_uint8(
                    v___x_679_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_559_,
                );
                lean_ctor_set_uint8(
                    v___x_679_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___x_677_,
                );
                if v_isShared_673_ == 0 {
                    lean_ctor_set(v___x_672_, 0, v___x_679_);
                    v___x_681_ = v___x_672_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
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
                    v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
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
                    v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
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
    mut v_e_702_: *mut LeanObject,
    mut v_a_703_: *mut LeanObject,
    mut v_a_704_: *mut LeanObject,
    mut v_a_705_: *mut LeanObject,
    mut v_a_706_: *mut LeanObject,
    mut v_a_707_: *mut LeanObject,
    mut v_a_708_: *mut LeanObject,
    mut v_a_709_: *mut LeanObject,
    mut v_a_710_: *mut LeanObject,
    mut v_a_711_: *mut LeanObject,
    mut v_a_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_713_: *mut LeanObject = core::ptr::null_mut();
    v_res_713_ =
        l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr(
            v_e_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_,
            v_a_710_, v_a_711_,
        );
    lean_dec(v_a_711_);
    lean_dec_ref(v_a_710_);
    lean_dec(v_a_709_);
    lean_dec_ref(v_a_708_);
    lean_dec(v_a_707_);
    lean_dec_ref(v_a_706_);
    lean_dec(v_a_705_);
    lean_dec_ref(v_a_704_);
    lean_dec(v_a_703_);
    return v_res_713_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_()
-> *mut LeanObject {
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    v___x_772_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_;
    v___x_773_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_;
    v___x_774_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_775_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_772_, v___x_773_, v___x_774_);
    return v___x_775_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14____boxed(
    mut v_a_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_777_: *mut LeanObject = core::ptr::null_mut();
    v_res_777_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_();
    return v_res_777_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_16_()
-> *mut LeanObject {
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: u8 = 0;
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    v___x_779_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_;
    v___x_780_ = 0;
    v___x_781_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_782_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_779_, v___x_780_, v___x_781_);
    return v___x_782_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_16____boxed(
    mut v_a_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_784_: *mut LeanObject = core::ptr::null_mut();
    v_res_784_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_16_();
    return v_res_784_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4()
-> *mut LeanObject {
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    v___x_791_ = lean_box(0);
    v___x_792_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__3;
    v___x_793_ = l_Lean_mkConst(v___x_792_, v___x_791_);
    return v___x_793_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7()
-> *mut LeanObject {
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_797_ = lean_box(0);
    v___x_798_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__6;
    v___x_799_ = l_Lean_mkConst(v___x_798_, v___x_797_);
    return v___x_799_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd(
    mut v_e_810_: *mut LeanObject,
    mut v_a_811_: *mut LeanObject,
    mut v_a_812_: *mut LeanObject,
    mut v_a_813_: *mut LeanObject,
    mut v_a_814_: *mut LeanObject,
    mut v_a_815_: *mut LeanObject,
    mut v_a_816_: *mut LeanObject,
    mut v_a_817_: *mut LeanObject,
    mut v_a_818_: *mut LeanObject,
    mut v_a_819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: u8 = 0;
    let mut v_arg_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: u8 = 0;
    let mut v_arg_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: u8 = 0;
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: u8 = 0;
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_845_: u8 = 0;
    let mut v___x_846_: u8 = 0;
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: u8 = 0;
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: u8 = 0;
    let mut v___x_859_: u8 = 0;
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut v_a_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_867_: u8 = 0;
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_871_: u8 = 0;
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_884_: u8 = 0;
    let mut v_a_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_892_: u8 = 0;
    let mut v_a_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_896_: u8 = 0;
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_900_: u8 = 0;
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_e_x27_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_906_: u8 = 0;
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: u8 = 0;
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_914_: u8 = 0;
    let mut v___x_915_: u8 = 0;
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: u8 = 0;
    let mut v___x_918_: u8 = 0;
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: u8 = 0;
    let mut v___x_928_: u8 = 0;
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut v_a_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_941_: u8 = 0;
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: u8 = 0;
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_a_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut v_a_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_973_: u8 = 0;
    let mut v_isSharedCheck_974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_810_);
                v___x_824_ = l_Lean_Expr_cleanupAnnotations(v_e_810_);
                v___x_825_ = l_Lean_Expr_isApp(v___x_824_);
                if v___x_825_ == 0 {
                    lean_dec_ref(v___x_824_);
                    lean_dec_ref(v_e_810_);
                    state = 1;
                    continue;
                } else {
                    v_arg_826_ = lean_ctor_get(v___x_824_, 1);
                    lean_inc_ref(v_arg_826_);
                    v___x_827_ = l_Lean_Expr_appFnCleanup___redArg(v___x_824_);
                    v___x_828_ = l_Lean_Expr_isApp(v___x_827_);
                    if v___x_828_ == 0 {
                        lean_dec_ref(v___x_827_);
                        lean_dec_ref(v_arg_826_);
                        lean_dec_ref(v_e_810_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_829_ = lean_ctor_get(v___x_827_, 1);
                        lean_inc_ref(v_arg_829_);
                        v___x_830_ = l_Lean_Expr_appFnCleanup___redArg(v___x_827_);
                        v___x_831_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__1;
                        v___x_832_ = l_Lean_Expr_isConstOf(v___x_830_, v___x_831_);
                        lean_dec_ref(v___x_830_);
                        if v___x_832_ == 0 {
                            lean_dec_ref(v_arg_829_);
                            lean_dec_ref(v_arg_826_);
                            lean_dec_ref(v_e_810_);
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_819_);
                            lean_inc_ref(v_a_818_);
                            lean_inc(v_a_817_);
                            lean_inc_ref(v_a_816_);
                            lean_inc(v_a_815_);
                            lean_inc_ref(v_a_814_);
                            lean_inc(v_a_813_);
                            lean_inc_ref(v_a_812_);
                            lean_inc(v_a_811_);
                            lean_inc_ref(v_arg_829_);
                            v___x_833_ = lean_sym_simp(
                                v_arg_829_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_,
                                v_a_816_, v_a_817_, v_a_818_, v_a_819_,
                            );
                            if lean_obj_tag(v___x_833_) == 0 {
                                v_a_834_ = lean_ctor_get(v___x_833_, 0);
                                lean_inc(v_a_834_);
                                lean_dec_ref_known(v___x_833_, 1);
                                if lean_obj_tag(v_a_834_) == 0 {
                                    lean_dec_ref(v_e_810_);
                                    v_isSharedCheck_901_ = (!lean_is_exclusive(v_a_834_)) as u8;
                                    if v_isSharedCheck_901_ == 0 {
                                        v___x_836_ = v_a_834_;
                                        v_isShared_837_ = v_isSharedCheck_901_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v_a_834_);
                                        v___x_836_ = lean_box(0);
                                        v_isShared_837_ = v_isSharedCheck_901_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_829_);
                                    v_e_x27_902_ = lean_ctor_get(v_a_834_, 0);
                                    v_proof_903_ = lean_ctor_get(v_a_834_, 1);
                                    v_isSharedCheck_974_ = (!lean_is_exclusive(v_a_834_)) as u8;
                                    if v_isSharedCheck_974_ == 0 {
                                        v___x_905_ = v_a_834_;
                                        v_isShared_906_ = v_isSharedCheck_974_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_proof_903_);
                                        lean_inc(v_e_x27_902_);
                                        lean_dec(v_a_834_);
                                        v___x_905_ = lean_box(0);
                                        v_isShared_906_ = v_isSharedCheck_974_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_arg_829_);
                                lean_dec_ref(v_arg_826_);
                                lean_dec_ref(v_e_810_);
                                return v___x_833_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_822_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___closed__0;
                v___x_823_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_823_, 0, v___x_822_);
                return v___x_823_;
            }
            2 => {
                v___x_838_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_829_, v_a_814_);
                if lean_obj_tag(v___x_838_) == 0 {
                    v_a_839_ = lean_ctor_get(v___x_838_, 0);
                    lean_inc(v_a_839_);
                    lean_dec_ref_known(v___x_838_, 1);
                    v___x_840_ = (lean_unbox(v_a_839_) as u8);
                    if v___x_840_ == 0 {
                        v___x_841_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_829_, v_a_814_);
                        lean_dec_ref(v_arg_829_);
                        if lean_obj_tag(v___x_841_) == 0 {
                            v_a_842_ = lean_ctor_get(v___x_841_, 0);
                            v_isSharedCheck_863_ = (!lean_is_exclusive(v___x_841_)) as u8;
                            if v_isSharedCheck_863_ == 0 {
                                v___x_844_ = v___x_841_;
                                v_isShared_845_ = v_isSharedCheck_863_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_842_);
                                lean_dec(v___x_841_);
                                v___x_844_ = lean_box(0);
                                v_isShared_845_ = v_isSharedCheck_863_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_839_);
                            lean_del_object(v___x_836_);
                            lean_dec_ref(v_arg_826_);
                            v_a_864_ = lean_ctor_get(v___x_841_, 0);
                            v_isSharedCheck_871_ = (!lean_is_exclusive(v___x_841_)) as u8;
                            if v_isSharedCheck_871_ == 0 {
                                v___x_866_ = v___x_841_;
                                v_isShared_867_ = v_isSharedCheck_871_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_864_);
                                lean_dec(v___x_841_);
                                v___x_866_ = lean_box(0);
                                v_isShared_867_ = v_isSharedCheck_871_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_839_);
                        lean_del_object(v___x_836_);
                        lean_dec_ref(v_arg_829_);
                        v___x_872_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_814_);
                        if lean_obj_tag(v___x_872_) == 0 {
                            v_a_873_ = lean_ctor_get(v___x_872_, 0);
                            v_isSharedCheck_884_ = (!lean_is_exclusive(v___x_872_)) as u8;
                            if v_isSharedCheck_884_ == 0 {
                                v___x_875_ = v___x_872_;
                                v_isShared_876_ = v_isSharedCheck_884_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_873_);
                                lean_dec(v___x_872_);
                                v___x_875_ = lean_box(0);
                                v_isShared_876_ = v_isSharedCheck_884_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_arg_826_);
                            v_a_885_ = lean_ctor_get(v___x_872_, 0);
                            v_isSharedCheck_892_ = (!lean_is_exclusive(v___x_872_)) as u8;
                            if v_isSharedCheck_892_ == 0 {
                                v___x_887_ = v___x_872_;
                                v_isShared_888_ = v_isSharedCheck_892_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_885_);
                                lean_dec(v___x_872_);
                                v___x_887_ = lean_box(0);
                                v_isShared_888_ = v_isSharedCheck_892_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_836_);
                    lean_dec_ref(v_arg_829_);
                    lean_dec_ref(v_arg_826_);
                    v_a_893_ = lean_ctor_get(v___x_838_, 0);
                    v_isSharedCheck_900_ = (!lean_is_exclusive(v___x_838_)) as u8;
                    if v_isSharedCheck_900_ == 0 {
                        v___x_895_ = v___x_838_;
                        v_isShared_896_ = v_isSharedCheck_900_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_893_);
                        lean_dec(v___x_838_);
                        v___x_895_ = lean_box(0);
                        v_isShared_896_ = v_isSharedCheck_900_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => {
                v___x_846_ = (lean_unbox(v_a_842_) as u8);
                if v___x_846_ == 0 {
                    lean_dec(v_a_839_);
                    lean_dec_ref(v_arg_826_);
                    if v_isShared_837_ == 0 {
                        v___x_848_ = v___x_836_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 0, (2) as u32);
                        v___x_848_ = v_reuseFailAlloc_854_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_842_);
                    lean_del_object(v___x_836_);
                    v___x_855_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4_once), _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__4);
                    lean_inc_ref(v_arg_826_);
                    v___x_856_ = l_Lean_Expr_app___override(v___x_855_, v_arg_826_);
                    v___x_857_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v___x_857_, 0, v_arg_826_);
                    lean_ctor_set(v___x_857_, 1, v___x_856_);
                    v___x_858_ = (lean_unbox(v_a_839_) as u8);
                    lean_ctor_set_uint8(
                        v___x_857_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_858_,
                    );
                    v___x_859_ = (lean_unbox(v_a_839_) as u8);
                    lean_dec(v_a_839_);
                    lean_ctor_set_uint8(
                        v___x_857_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        v___x_859_,
                    );
                    if v_isShared_845_ == 0 {
                        lean_ctor_set(v___x_844_, 0, v___x_857_);
                        v___x_861_ = v___x_844_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_857_);
                        v___x_861_ = v_reuseFailAlloc_862_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_849_ = (lean_unbox(v_a_842_) as u8);
                lean_ctor_set_uint8(v___x_848_, 0 as u32, v___x_849_);
                v___x_850_ = (lean_unbox(v_a_842_) as u8);
                lean_dec(v_a_842_);
                lean_ctor_set_uint8(v___x_848_, 1 as u32, v___x_850_);
                if v_isShared_845_ == 0 {
                    lean_ctor_set(v___x_844_, 0, v___x_848_);
                    v___x_852_ = v___x_844_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_848_);
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
                    v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
                    v___x_869_ = v_reuseFailAlloc_870_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_869_;
            }
            9 => {
                v___x_877_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7_once), _init_l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__7);
                v___x_878_ = l_Lean_Expr_app___override(v___x_877_, v_arg_826_);
                v___x_879_ = 0;
                v___x_880_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_880_, 0, v_a_873_);
                lean_ctor_set(v___x_880_, 1, v___x_878_);
                lean_ctor_set_uint8(
                    v___x_880_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_832_,
                );
                lean_ctor_set_uint8(
                    v___x_880_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___x_879_,
                );
                if v_isShared_876_ == 0 {
                    lean_ctor_set(v___x_875_, 0, v___x_880_);
                    v___x_882_ = v___x_875_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
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
                    v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
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
                    v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
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
                if lean_obj_tag(v___x_907_) == 0 {
                    v_a_908_ = lean_ctor_get(v___x_907_, 0);
                    lean_inc(v_a_908_);
                    lean_dec_ref_known(v___x_907_, 1);
                    v___x_909_ = (lean_unbox(v_a_908_) as u8);
                    if v___x_909_ == 0 {
                        v___x_910_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_902_, v_a_814_);
                        lean_dec_ref(v_e_x27_902_);
                        if lean_obj_tag(v___x_910_) == 0 {
                            v_a_911_ = lean_ctor_get(v___x_910_, 0);
                            v_isSharedCheck_933_ = (!lean_is_exclusive(v___x_910_)) as u8;
                            if v_isSharedCheck_933_ == 0 {
                                v___x_913_ = v___x_910_;
                                v_isShared_914_ = v_isSharedCheck_933_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_911_);
                                lean_dec(v___x_910_);
                                v___x_913_ = lean_box(0);
                                v_isShared_914_ = v_isSharedCheck_933_;
                                state = 16;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_908_);
                            lean_del_object(v___x_905_);
                            lean_dec_ref(v_proof_903_);
                            lean_dec_ref(v_arg_826_);
                            lean_dec_ref(v_e_810_);
                            v_a_934_ = lean_ctor_get(v___x_910_, 0);
                            v_isSharedCheck_941_ = (!lean_is_exclusive(v___x_910_)) as u8;
                            if v_isSharedCheck_941_ == 0 {
                                v___x_936_ = v___x_910_;
                                v_isShared_937_ = v_isSharedCheck_941_;
                                state = 20;
                                continue;
                            } else {
                                lean_inc(v_a_934_);
                                lean_dec(v___x_910_);
                                v___x_936_ = lean_box(0);
                                v_isShared_937_ = v_isSharedCheck_941_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_908_);
                        lean_dec_ref(v_e_x27_902_);
                        lean_dec_ref(v_arg_826_);
                        v___x_942_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_814_);
                        if lean_obj_tag(v___x_942_) == 0 {
                            v_a_943_ = lean_ctor_get(v___x_942_, 0);
                            v_isSharedCheck_957_ = (!lean_is_exclusive(v___x_942_)) as u8;
                            if v_isSharedCheck_957_ == 0 {
                                v___x_945_ = v___x_942_;
                                v_isShared_946_ = v_isSharedCheck_957_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_a_943_);
                                lean_dec(v___x_942_);
                                v___x_945_ = lean_box(0);
                                v_isShared_946_ = v_isSharedCheck_957_;
                                state = 22;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_905_);
                            lean_dec_ref(v_proof_903_);
                            lean_dec_ref(v_e_810_);
                            v_a_958_ = lean_ctor_get(v___x_942_, 0);
                            v_isSharedCheck_965_ = (!lean_is_exclusive(v___x_942_)) as u8;
                            if v_isSharedCheck_965_ == 0 {
                                v___x_960_ = v___x_942_;
                                v_isShared_961_ = v_isSharedCheck_965_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_958_);
                                lean_dec(v___x_942_);
                                v___x_960_ = lean_box(0);
                                v_isShared_961_ = v_isSharedCheck_965_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_905_);
                    lean_dec_ref(v_proof_903_);
                    lean_dec_ref(v_e_x27_902_);
                    lean_dec_ref(v_arg_826_);
                    lean_dec_ref(v_e_810_);
                    v_a_966_ = lean_ctor_get(v___x_907_, 0);
                    v_isSharedCheck_973_ = (!lean_is_exclusive(v___x_907_)) as u8;
                    if v_isSharedCheck_973_ == 0 {
                        v___x_968_ = v___x_907_;
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_966_);
                        lean_dec(v___x_907_);
                        v___x_968_ = lean_box(0);
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 27;
                        continue;
                    }
                }
            }
            16 => {
                v___x_915_ = (lean_unbox(v_a_911_) as u8);
                if v___x_915_ == 0 {
                    lean_dec(v_a_908_);
                    lean_del_object(v___x_905_);
                    lean_dec_ref(v_proof_903_);
                    lean_dec_ref(v_arg_826_);
                    lean_dec_ref(v_e_810_);
                    v___x_916_ = lean_alloc_ctor(0, 0, (2) as u32);
                    v___x_917_ = (lean_unbox(v_a_911_) as u8);
                    lean_ctor_set_uint8(v___x_916_, 0 as u32, v___x_917_);
                    v___x_918_ = (lean_unbox(v_a_911_) as u8);
                    lean_dec(v_a_911_);
                    lean_ctor_set_uint8(v___x_916_, 1 as u32, v___x_918_);
                    if v_isShared_914_ == 0 {
                        lean_ctor_set(v___x_913_, 0, v___x_916_);
                        v___x_920_ = v___x_913_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_916_);
                        v___x_920_ = v_reuseFailAlloc_921_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec(v_a_911_);
                    v___x_922_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___closed__9;
                    v___x_923_ = l_Lean_Expr_replaceFn(v_e_810_, v___x_922_);
                    v___x_924_ = l_Lean_Expr_app___override(v___x_923_, v_proof_903_);
                    if v_isShared_906_ == 0 {
                        lean_ctor_set(v___x_905_, 1, v___x_924_);
                        lean_ctor_set(v___x_905_, 0, v_arg_826_);
                        v___x_926_ = v___x_905_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 2, (2) as u32);
                        lean_ctor_set(v_reuseFailAlloc_932_, 0, v_arg_826_);
                        lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_924_);
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
                v___x_927_ = (lean_unbox(v_a_908_) as u8);
                lean_ctor_set_uint8(
                    v___x_926_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_927_,
                );
                v___x_928_ = (lean_unbox(v_a_908_) as u8);
                lean_dec(v_a_908_);
                lean_ctor_set_uint8(
                    v___x_926_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___x_928_,
                );
                if v_isShared_914_ == 0 {
                    lean_ctor_set(v___x_913_, 0, v___x_926_);
                    v___x_930_ = v___x_913_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_926_);
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
                    v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
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
                    lean_ctor_set(v___x_905_, 1, v___x_949_);
                    lean_ctor_set(v___x_905_, 0, v_a_943_);
                    v___x_952_ = v___x_905_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_943_);
                    lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_949_);
                    v___x_952_ = v_reuseFailAlloc_956_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                lean_ctor_set_uint8(
                    v___x_952_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_832_,
                );
                lean_ctor_set_uint8(
                    v___x_952_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___x_950_,
                );
                if v_isShared_946_ == 0 {
                    lean_ctor_set(v___x_945_, 0, v___x_952_);
                    v___x_954_ = v___x_945_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
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
                    v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
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
                    v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
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
    mut v_e_975_: *mut LeanObject,
    mut v_a_976_: *mut LeanObject,
    mut v_a_977_: *mut LeanObject,
    mut v_a_978_: *mut LeanObject,
    mut v_a_979_: *mut LeanObject,
    mut v_a_980_: *mut LeanObject,
    mut v_a_981_: *mut LeanObject,
    mut v_a_982_: *mut LeanObject,
    mut v_a_983_: *mut LeanObject,
    mut v_a_984_: *mut LeanObject,
    mut v_a_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_986_: *mut LeanObject = core::ptr::null_mut();
    v_res_986_ =
        l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd(
            v_e_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_,
            v_a_983_, v_a_984_,
        );
    lean_dec(v_a_984_);
    lean_dec_ref(v_a_983_);
    lean_dec(v_a_982_);
    lean_dec_ref(v_a_981_);
    lean_dec(v_a_980_);
    lean_dec_ref(v_a_979_);
    lean_dec(v_a_978_);
    lean_dec_ref(v_a_977_);
    lean_dec(v_a_976_);
    return v_res_986_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_()
-> *mut LeanObject {
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    v___x_1002_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_;
    v___x_1003_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_;
    v___x_1004_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_1005_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1002_, v___x_1003_, v___x_1004_);
    return v___x_1005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14____boxed(
    mut v_a_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1007_: *mut LeanObject = core::ptr::null_mut();
    v_res_1007_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_();
    return v_res_1007_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_16_()
-> *mut LeanObject {
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: u8 = 0;
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    v___x_1009_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_;
    v___x_1010_ = 0;
    v___x_1011_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_1012_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1009_, v___x_1010_, v___x_1011_);
    return v___x_1012_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_16____boxed(
    mut v_a_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1014_: *mut LeanObject = core::ptr::null_mut();
    v_res_1014_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_16_();
    return v_res_1014_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Sym_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_14_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpOr_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_324783323____hygCtx___hyg_16_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_14_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_0__Lean_Meta_Sym_Simp_simpAnd_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core_894573248____hygCtx___hyg_16_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Sym_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(builtin);
}
