// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.Array
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.LitValues Lean.Meta.Sym.InferType Init.CbvSimproc Lean.Meta.Tactic.Cbv.CbvSimproc Lean.Meta.Tactic.Cbv.Util Init.GetElem
use crate::ffi::{lean_array_fget, lean_array_get_size, lean_nat_dec_lt};
use crate::r#gen::Init::CbvSimproc::{
    initialize_Init_CbvSimproc, runtime_initialize_Init_CbvSimproc,
};
use crate::r#gen::Init::GetElem::{initialize_Init_GetElem, runtime_initialize_Init_GetElem};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Sym::InferType::{
    initialize_Lean_Meta_Sym_InferType, l_Lean_Meta_Sym_getLevel___redArg,
    l_Lean_Meta_Sym_mkEqRefl___redArg, runtime_initialize_Lean_Meta_Sym_InferType,
};
use crate::r#gen::Lean::Meta::Sym::LitValues::{
    initialize_Lean_Meta_Sym_LitValues, l_Lean_Meta_Sym_getNatValue_x3f,
    runtime_initialize_Lean_Meta_Sym_LitValues,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommonInc___redArg;
use crate::r#gen::Lean::Meta::Tactic::Cbv::CbvSimproc::{
    initialize_Lean_Meta_Tactic_Cbv_CbvSimproc, l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr,
    l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc,
    runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::Util::{
    initialize_Lean_Meta_Tactic_Cbv_Util, l_Lean_Meta_Tactic_Cbv_getListLitElems,
    runtime_initialize_Lean_Meta_Tactic_Cbv_Util,
};
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__1_value) as *mut leanh::LeanObject,15116455438679371901 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__3_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__1_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [71, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [103, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__1_value) as *mut leanh::LeanObject,854136310249810287 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__2_value) as *mut leanh::LeanObject,8801718159307809986 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,16489734963670585437 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [66, 117, 105, 108, 116, 105, 110, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,8524095998741210685 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value) as *mut leanh::LeanObject,16410770112748744871 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,5129318075627908122 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,2216385626806373307 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,15815158614411347923 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,17744160327223409858 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,8318300268641070792 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 109, 112, 65, 114, 114, 97, 121, 71, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,11452774320338168454 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value) as *mut leanh::LeanObject,((( 8 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__23_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__23_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__23_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__24_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__23_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__24_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__24_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__24_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__26_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: leanh::LeanArrayObject<10> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*10) as u16, other: 0, tag: 246 }, m_size: 10, m_capacity: 10, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__26_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__26_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [71, 101, 116, 69, 108, 101, 109, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [103, 101, 116, 69, 108, 101, 109, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,1284173141442213452 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,14790288273250445109 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3_value) as *mut leanh::LeanObject,18184376426117065311 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__4_value) as *mut leanh::LeanObject,9480010471355609749 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 111, 109, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__6_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3_value) as *mut leanh::LeanObject,18184376426117065311 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__6_value) as *mut leanh::LeanObject,4893146552088433753 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [115, 105, 109, 112, 65, 114, 114, 97, 121, 71, 101, 116, 69, 108, 101, 109, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut leanh::LeanObject,13759082831902185974 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,((( 7 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value: leanh::LeanArrayObject<9> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*9) as u16, other: 0, tag: 246 }, m_size: 9, m_capacity: 9, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f(
    mut v_e_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: u8 = 0;
    v___x_440_ = l_Lean_Expr_cleanupAnnotations(v_e_439_);
    v___x_441_ = l_Lean_Expr_isApp(v___x_440_);
    if v___x_441_ == 0 {
        let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_440_);
        v___x_442_ = leanh::lean_box(0);
        return v___x_442_;
    } else {
        let mut v_arg_443_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_445_: u8 = 0;
        v_arg_443_ = leanh::lean_ctor_get(v___x_440_, 1);
        leanh::lean_inc_ref(v_arg_443_);
        v___x_444_ = l_Lean_Expr_appFnCleanup___redArg(v___x_440_);
        v___x_445_ = l_Lean_Expr_isApp(v___x_444_);
        if v___x_445_ == 0 {
            let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_444_);
            leanh::lean_dec_ref(v_arg_443_);
            v___x_446_ = leanh::lean_box(0);
            return v___x_446_;
        } else {
            let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_449_: u8 = 0;
            v___x_447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_444_);
            v___x_448_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2;
            v___x_449_ = l_Lean_Expr_isConstOf(v___x_447_, v___x_448_);
            leanh::lean_dec_ref(v___x_447_);
            if v___x_449_ == 0 {
                let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_arg_443_);
                v___x_450_ = leanh::lean_box(0);
                return v___x_450_;
            } else {
                let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_451_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__3;
                v___x_452_ = l_Lean_Meta_Tactic_Cbv_getListLitElems(v_arg_443_, v___x_451_);
                return v___x_452_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg(
    mut v_e_460_: *mut leanh::LeanObject,
    mut v_a_461_: *mut leanh::LeanObject,
    mut v_a_462_: *mut leanh::LeanObject,
    mut v_a_463_: *mut leanh::LeanObject,
    mut v_a_464_: *mut leanh::LeanObject,
    mut v_a_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: u8 = 0;
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: u8 = 0;
    let mut v_arg_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: u8 = 0;
    let mut v_arg_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: u8 = 0;
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: u8 = 0;
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: u8 = 0;
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: u8 = 0;
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: u8 = 0;
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: u8 = 0;
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_495_: u8 = 0;
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: u8 = 0;
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_512_: u8 = 0;
    let mut v___x_513_: u8 = 0;
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_518_: u8 = 0;
    let mut v_a_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_522_: u8 = 0;
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_526_: u8 = 0;
    let mut v_isSharedCheck_527_: u8 = 0;
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_532_: u8 = 0;
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_470_ = l_Lean_Expr_cleanupAnnotations(v_e_460_);
                v___x_471_ = l_Lean_Expr_isApp(v___x_470_);
                if v___x_471_ == 0 {
                    leanh::lean_dec_ref(v___x_470_);
                    state = 1;
                    continue;
                } else {
                    v___x_472_ = l_Lean_Expr_appFnCleanup___redArg(v___x_470_);
                    v___x_473_ = l_Lean_Expr_isApp(v___x_472_);
                    if v___x_473_ == 0 {
                        leanh::lean_dec_ref(v___x_472_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_474_ = leanh::lean_ctor_get(v___x_472_, 1);
                        leanh::lean_inc_ref(v_arg_474_);
                        v___x_475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_472_);
                        v___x_476_ = l_Lean_Expr_isApp(v___x_475_);
                        if v___x_476_ == 0 {
                            leanh::lean_dec_ref(v___x_475_);
                            leanh::lean_dec_ref(v_arg_474_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_477_ = leanh::lean_ctor_get(v___x_475_, 1);
                            leanh::lean_inc_ref(v_arg_477_);
                            v___x_478_ = l_Lean_Expr_appFnCleanup___redArg(v___x_475_);
                            v___x_479_ = l_Lean_Expr_isApp(v___x_478_);
                            if v___x_479_ == 0 {
                                leanh::lean_dec_ref(v___x_478_);
                                leanh::lean_dec_ref(v_arg_477_);
                                leanh::lean_dec_ref(v_arg_474_);
                                state = 1;
                                continue;
                            } else {
                                v___x_480_ = l_Lean_Expr_appFnCleanup___redArg(v___x_478_);
                                v___x_481_ = l_Lean_Expr_isApp(v___x_480_);
                                if v___x_481_ == 0 {
                                    leanh::lean_dec_ref(v___x_480_);
                                    leanh::lean_dec_ref(v_arg_477_);
                                    leanh::lean_dec_ref(v_arg_474_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_482_ = l_Lean_Expr_appFnCleanup___redArg(v___x_480_);
                                    v___x_483_ = l_Lean_Expr_isApp(v___x_482_);
                                    if v___x_483_ == 0 {
                                        leanh::lean_dec_ref(v___x_482_);
                                        leanh::lean_dec_ref(v_arg_477_);
                                        leanh::lean_dec_ref(v_arg_474_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_484_ = l_Lean_Expr_appFnCleanup___redArg(v___x_482_);
                                        v___x_485_ = l_Lean_Expr_isApp(v___x_484_);
                                        if v___x_485_ == 0 {
                                            leanh::lean_dec_ref(v___x_484_);
                                            leanh::lean_dec_ref(v_arg_477_);
                                            leanh::lean_dec_ref(v_arg_474_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_486_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_484_);
                                            v___x_487_ = l_Lean_Expr_isApp(v___x_486_);
                                            if v___x_487_ == 0 {
                                                leanh::lean_dec_ref(v___x_486_);
                                                leanh::lean_dec_ref(v_arg_477_);
                                                leanh::lean_dec_ref(v_arg_474_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_488_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_486_);
                                                v___x_489_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3;
                                                v___x_490_ =
                                                    l_Lean_Expr_isConstOf(v___x_488_, v___x_489_);
                                                leanh::lean_dec_ref(v___x_488_);
                                                if v___x_490_ == 0 {
                                                    leanh::lean_dec_ref(v_arg_477_);
                                                    leanh::lean_dec_ref(v_arg_474_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_491_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f(v_arg_477_);
                                                    if leanh::lean_obj_tag(v___x_491_) == 1 {
                                                        v_val_492_ = leanh::lean_ctor_get(
                                                            v___x_491_, 0,
                                                        );
                                                        v_isSharedCheck_532_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_491_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_532_ == 0 {
                                                            v___x_494_ = v___x_491_;
                                                            v_isShared_495_ = v_isSharedCheck_532_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_val_492_);
                                                            leanh::lean_dec(v___x_491_);
                                                            v___x_494_ = leanh::lean_box(0);
                                                            v_isShared_495_ = v_isSharedCheck_532_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v___x_491_);
                                                        leanh::lean_dec_ref(v_arg_474_);
                                                        v___x_533_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                                                        v___x_534_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_534_, 0, v___x_533_,
                                                        );
                                                        return v___x_534_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_468_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                v___x_469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_469_, 0, v___x_468_);
                return v___x_469_;
            }
            2 => {
                v___x_496_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_474_);
                if leanh::lean_obj_tag(v___x_496_) == 1 {
                    leanh::lean_del_object(v___x_494_);
                    v_val_497_ = leanh::lean_ctor_get(v___x_496_, 0);
                    v_isSharedCheck_527_ = (!leanh::lean_is_exclusive(v___x_496_)) as u8;
                    if v_isSharedCheck_527_ == 0 {
                        v___x_499_ = v___x_496_;
                        v_isShared_500_ = v_isSharedCheck_527_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_497_);
                        leanh::lean_dec(v___x_496_);
                        v___x_499_ = leanh::lean_box(0);
                        v_isShared_500_ = v_isSharedCheck_527_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_496_);
                    leanh::lean_dec(v_val_492_);
                    v___x_528_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                    if v_isShared_495_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_494_, 0);
                        leanh::lean_ctor_set(v___x_494_, 0, v___x_528_);
                        v___x_530_ = v___x_494_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
                        v___x_530_ = v_reuseFailAlloc_531_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_501_ = lean_array_get_size(v_val_492_);
                v___x_502_ = lean_nat_dec_lt(v_val_497_, v___x_501_);
                if v___x_502_ == 0 {
                    leanh::lean_dec(v_val_497_);
                    leanh::lean_dec(v_val_492_);
                    v___x_503_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    leanh::lean_ctor_set_uint8(v___x_503_, 0 as u32, v___x_502_);
                    leanh::lean_ctor_set_uint8(v___x_503_, 1 as u32, v___x_502_);
                    if v_isShared_500_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_499_, 0);
                        leanh::lean_ctor_set(v___x_499_, 0, v___x_503_);
                        v___x_505_ = v___x_499_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_506_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
                        v___x_505_ = v_reuseFailAlloc_506_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_499_);
                    v_result_507_ = lean_array_fget(v_val_492_, v_val_497_);
                    leanh::lean_dec(v_val_497_);
                    leanh::lean_dec(v_val_492_);
                    leanh::lean_inc(v_result_507_);
                    v___x_508_ = l_Lean_Meta_Sym_mkEqRefl___redArg(
                        v_result_507_,
                        v_a_461_,
                        v_a_462_,
                        v_a_463_,
                        v_a_464_,
                        v_a_465_,
                    );
                    if leanh::lean_obj_tag(v___x_508_) == 0 {
                        v_a_509_ = leanh::lean_ctor_get(v___x_508_, 0);
                        v_isSharedCheck_518_ = (!leanh::lean_is_exclusive(v___x_508_)) as u8;
                        if v_isSharedCheck_518_ == 0 {
                            v___x_511_ = v___x_508_;
                            v_isShared_512_ = v_isSharedCheck_518_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_509_);
                            leanh::lean_dec(v___x_508_);
                            v___x_511_ = leanh::lean_box(0);
                            v_isShared_512_ = v_isSharedCheck_518_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_result_507_);
                        v_a_519_ = leanh::lean_ctor_get(v___x_508_, 0);
                        v_isSharedCheck_526_ = (!leanh::lean_is_exclusive(v___x_508_)) as u8;
                        if v_isSharedCheck_526_ == 0 {
                            v___x_521_ = v___x_508_;
                            v_isShared_522_ = v_isSharedCheck_526_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_519_);
                            leanh::lean_dec(v___x_508_);
                            v___x_521_ = leanh::lean_box(0);
                            v_isShared_522_ = v_isSharedCheck_526_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_505_;
            }
            5 => {
                v___x_513_ = 0;
                v___x_514_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_514_, 0, v_result_507_);
                leanh::lean_ctor_set(v___x_514_, 1, v_a_509_);
                leanh::lean_ctor_set_uint8(
                    v___x_514_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_513_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_514_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_513_,
                );
                if v_isShared_512_ == 0 {
                    leanh::lean_ctor_set(v___x_511_, 0, v___x_514_);
                    v___x_516_ = v___x_511_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_517_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
                    v___x_516_ = v_reuseFailAlloc_517_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_516_;
            }
            7 => {
                if v_isShared_522_ == 0 {
                    v___x_524_ = v___x_521_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_525_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
                    v___x_524_ = v_reuseFailAlloc_525_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_524_;
            }
            9 => {
                return v___x_530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___boxed(
    mut v_e_535_: *mut leanh::LeanObject,
    mut v_a_536_: *mut leanh::LeanObject,
    mut v_a_537_: *mut leanh::LeanObject,
    mut v_a_538_: *mut leanh::LeanObject,
    mut v_a_539_: *mut leanh::LeanObject,
    mut v_a_540_: *mut leanh::LeanObject,
    mut v_a_541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_542_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg(v_e_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
    leanh::lean_dec(v_a_540_);
    leanh::lean_dec_ref(v_a_539_);
    leanh::lean_dec(v_a_538_);
    leanh::lean_dec_ref(v_a_537_);
    leanh::lean_dec(v_a_536_);
    return v_res_542_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem(
    mut v_e_543_: *mut leanh::LeanObject,
    mut v_a_544_: *mut leanh::LeanObject,
    mut v_a_545_: *mut leanh::LeanObject,
    mut v_a_546_: *mut leanh::LeanObject,
    mut v_a_547_: *mut leanh::LeanObject,
    mut v_a_548_: *mut leanh::LeanObject,
    mut v_a_549_: *mut leanh::LeanObject,
    mut v_a_550_: *mut leanh::LeanObject,
    mut v_a_551_: *mut leanh::LeanObject,
    mut v_a_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg(v_e_543_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
    return v___x_554_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___boxed(
    mut v_e_555_: *mut leanh::LeanObject,
    mut v_a_556_: *mut leanh::LeanObject,
    mut v_a_557_: *mut leanh::LeanObject,
    mut v_a_558_: *mut leanh::LeanObject,
    mut v_a_559_: *mut leanh::LeanObject,
    mut v_a_560_: *mut leanh::LeanObject,
    mut v_a_561_: *mut leanh::LeanObject,
    mut v_a_562_: *mut leanh::LeanObject,
    mut v_a_563_: *mut leanh::LeanObject,
    mut v_a_564_: *mut leanh::LeanObject,
    mut v_a_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_566_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem(v_e_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
    leanh::lean_dec(v_a_564_);
    leanh::lean_dec_ref(v_a_563_);
    leanh::lean_dec(v_a_562_);
    leanh::lean_dec_ref(v_a_561_);
    leanh::lean_dec(v_a_560_);
    leanh::lean_dec_ref(v_a_559_);
    leanh::lean_dec(v_a_558_);
    leanh::lean_dec_ref(v_a_557_);
    leanh::lean_dec(v_a_556_);
    return v_res_566_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_;
    v___x_646_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__26_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_;
    v___x_647_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_648_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_645_, v___x_646_, v___x_647_);
    return v___x_648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22____boxed(
    mut v_a_649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_650_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_();
    return v_res_650_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_24_()
-> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_;
    v___x_653_ = 1;
    v___x_654_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_655_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_652_, v___x_653_, v___x_654_);
    return v___x_655_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_24____boxed(
    mut v_a_656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_657_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_24_();
    return v_res_657_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg(
    mut v_e_672_: *mut leanh::LeanObject,
    mut v_a_673_: *mut leanh::LeanObject,
    mut v_a_674_: *mut leanh::LeanObject,
    mut v_a_675_: *mut leanh::LeanObject,
    mut v_a_676_: *mut leanh::LeanObject,
    mut v_a_677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_693_: u8 = 0;
    let mut v___x_694_: u8 = 0;
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut v_a_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_703_: u8 = 0;
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_707_: u8 = 0;
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: u8 = 0;
    let mut v_arg_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u8 = 0;
    let mut v_arg_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: u8 = 0;
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: u8 = 0;
    let mut v_arg_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: u8 = 0;
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u8 = 0;
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v_a_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_753_: u8 = 0;
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_757_: u8 = 0;
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_769_: u8 = 0;
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_773_: u8 = 0;
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_778_: u8 = 0;
    let mut v_a_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_782_: u8 = 0;
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_786_: u8 = 0;
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_791_: u8 = 0;
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_708_ = l_Lean_Expr_cleanupAnnotations(v_e_672_);
                v___x_709_ = l_Lean_Expr_isApp(v___x_708_);
                if v___x_709_ == 0 {
                    leanh::lean_dec_ref(v___x_708_);
                    state = 1;
                    continue;
                } else {
                    v_arg_710_ = leanh::lean_ctor_get(v___x_708_, 1);
                    leanh::lean_inc_ref(v_arg_710_);
                    v___x_711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_708_);
                    v___x_712_ = l_Lean_Expr_isApp(v___x_711_);
                    if v___x_712_ == 0 {
                        leanh::lean_dec_ref(v___x_711_);
                        leanh::lean_dec_ref(v_arg_710_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_713_ = leanh::lean_ctor_get(v___x_711_, 1);
                        leanh::lean_inc_ref(v_arg_713_);
                        v___x_714_ = l_Lean_Expr_appFnCleanup___redArg(v___x_711_);
                        v___x_715_ = l_Lean_Expr_isApp(v___x_714_);
                        if v___x_715_ == 0 {
                            leanh::lean_dec_ref(v___x_714_);
                            leanh::lean_dec_ref(v_arg_713_);
                            leanh::lean_dec_ref(v_arg_710_);
                            state = 1;
                            continue;
                        } else {
                            v___x_716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_714_);
                            v___x_717_ = l_Lean_Expr_isApp(v___x_716_);
                            if v___x_717_ == 0 {
                                leanh::lean_dec_ref(v___x_716_);
                                leanh::lean_dec_ref(v_arg_713_);
                                leanh::lean_dec_ref(v_arg_710_);
                                state = 1;
                                continue;
                            } else {
                                v___x_718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_716_);
                                v___x_719_ = l_Lean_Expr_isApp(v___x_718_);
                                if v___x_719_ == 0 {
                                    leanh::lean_dec_ref(v___x_718_);
                                    leanh::lean_dec_ref(v_arg_713_);
                                    leanh::lean_dec_ref(v_arg_710_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_720_ = leanh::lean_ctor_get(v___x_718_, 1);
                                    leanh::lean_inc_ref(v_arg_720_);
                                    v___x_721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
                                    v___x_722_ = l_Lean_Expr_isApp(v___x_721_);
                                    if v___x_722_ == 0 {
                                        leanh::lean_dec_ref(v___x_721_);
                                        leanh::lean_dec_ref(v_arg_720_);
                                        leanh::lean_dec_ref(v_arg_713_);
                                        leanh::lean_dec_ref(v_arg_710_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_723_ = l_Lean_Expr_appFnCleanup___redArg(v___x_721_);
                                        v___x_724_ = l_Lean_Expr_isApp(v___x_723_);
                                        if v___x_724_ == 0 {
                                            leanh::lean_dec_ref(v___x_723_);
                                            leanh::lean_dec_ref(v_arg_720_);
                                            leanh::lean_dec_ref(v_arg_713_);
                                            leanh::lean_dec_ref(v_arg_710_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_725_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_723_);
                                            v___x_726_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2;
                                            v___x_727_ =
                                                l_Lean_Expr_isConstOf(v___x_725_, v___x_726_);
                                            leanh::lean_dec_ref(v___x_725_);
                                            if v___x_727_ == 0 {
                                                leanh::lean_dec_ref(v_arg_720_);
                                                leanh::lean_dec_ref(v_arg_713_);
                                                leanh::lean_dec_ref(v_arg_710_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_728_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f(v_arg_713_);
                                                if leanh::lean_obj_tag(v___x_728_) == 1 {
                                                    v_val_729_ =
                                                        leanh::lean_ctor_get(v___x_728_, 0);
                                                    v_isSharedCheck_791_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_728_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_791_ == 0 {
                                                        v___x_731_ = v___x_728_;
                                                        v_isShared_732_ = v_isSharedCheck_791_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_val_729_);
                                                        leanh::lean_dec(v___x_728_);
                                                        v___x_731_ = leanh::lean_box(0);
                                                        v_isShared_732_ = v_isSharedCheck_791_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                } else {
                                                    leanh::lean_dec(v___x_728_);
                                                    leanh::lean_dec_ref(v_arg_720_);
                                                    leanh::lean_dec_ref(v_arg_710_);
                                                    v___x_792_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                                                    v___x_793_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_793_, 0, v___x_792_,
                                                    );
                                                    return v___x_793_;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_680_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                v___x_681_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_681_, 0, v___x_680_);
                return v___x_681_;
            }
            2 => {
                leanh::lean_inc_ref(v_result_683_);
                v___x_689_ = l_Lean_Meta_Sym_mkEqRefl___redArg(
                    v_result_683_,
                    v___y_684_,
                    v___y_685_,
                    v___y_686_,
                    v___y_687_,
                    v___y_688_,
                );
                if leanh::lean_obj_tag(v___x_689_) == 0 {
                    v_a_690_ = leanh::lean_ctor_get(v___x_689_, 0);
                    v_isSharedCheck_699_ = (!leanh::lean_is_exclusive(v___x_689_)) as u8;
                    if v_isSharedCheck_699_ == 0 {
                        v___x_692_ = v___x_689_;
                        v_isShared_693_ = v_isSharedCheck_699_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_690_);
                        leanh::lean_dec(v___x_689_);
                        v___x_692_ = leanh::lean_box(0);
                        v_isShared_693_ = v_isSharedCheck_699_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_result_683_);
                    v_a_700_ = leanh::lean_ctor_get(v___x_689_, 0);
                    v_isSharedCheck_707_ = (!leanh::lean_is_exclusive(v___x_689_)) as u8;
                    if v_isSharedCheck_707_ == 0 {
                        v___x_702_ = v___x_689_;
                        v_isShared_703_ = v_isSharedCheck_707_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_700_);
                        leanh::lean_dec(v___x_689_);
                        v___x_702_ = leanh::lean_box(0);
                        v_isShared_703_ = v_isSharedCheck_707_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_694_ = 0;
                v___x_695_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_695_, 0, v_result_683_);
                leanh::lean_ctor_set(v___x_695_, 1, v_a_690_);
                leanh::lean_ctor_set_uint8(
                    v___x_695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_694_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_694_,
                );
                if v_isShared_693_ == 0 {
                    leanh::lean_ctor_set(v___x_692_, 0, v___x_695_);
                    v___x_697_ = v___x_692_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_698_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
                    v___x_697_ = v_reuseFailAlloc_698_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_697_;
            }
            5 => {
                if v_isShared_703_ == 0 {
                    v___x_705_ = v___x_702_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_706_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
                    v___x_705_ = v_reuseFailAlloc_706_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_705_;
            }
            7 => {
                v___x_733_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_710_);
                if leanh::lean_obj_tag(v___x_733_) == 1 {
                    leanh::lean_del_object(v___x_731_);
                    v_val_734_ = leanh::lean_ctor_get(v___x_733_, 0);
                    leanh::lean_inc(v_val_734_);
                    leanh::lean_dec_ref_known(v___x_733_, 1);
                    leanh::lean_inc_ref(v_arg_720_);
                    v___x_735_ = l_Lean_Meta_Sym_getLevel___redArg(
                        v_arg_720_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_,
                    );
                    if leanh::lean_obj_tag(v___x_735_) == 0 {
                        v_a_736_ = leanh::lean_ctor_get(v___x_735_, 0);
                        v_isSharedCheck_778_ = (!leanh::lean_is_exclusive(v___x_735_)) as u8;
                        if v_isSharedCheck_778_ == 0 {
                            v___x_738_ = v___x_735_;
                            v_isShared_739_ = v_isSharedCheck_778_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_736_);
                            leanh::lean_dec(v___x_735_);
                            v___x_738_ = leanh::lean_box(0);
                            v_isShared_739_ = v_isSharedCheck_778_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_734_);
                        leanh::lean_dec(v_val_729_);
                        leanh::lean_dec_ref(v_arg_720_);
                        v_a_779_ = leanh::lean_ctor_get(v___x_735_, 0);
                        v_isSharedCheck_786_ = (!leanh::lean_is_exclusive(v___x_735_)) as u8;
                        if v_isSharedCheck_786_ == 0 {
                            v___x_781_ = v___x_735_;
                            v_isShared_782_ = v_isSharedCheck_786_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_779_);
                            leanh::lean_dec(v___x_735_);
                            v___x_781_ = leanh::lean_box(0);
                            v_isShared_782_ = v_isSharedCheck_786_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_733_);
                    leanh::lean_dec(v_val_729_);
                    leanh::lean_dec_ref(v_arg_720_);
                    v___x_787_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                    if v_isShared_732_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_731_, 0);
                        leanh::lean_ctor_set(v___x_731_, 0, v___x_787_);
                        v___x_789_ = v___x_731_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_790_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
                        v___x_789_ = v_reuseFailAlloc_790_;
                        state = 16;
                        continue;
                    }
                }
            }
            8 => {
                if leanh::lean_obj_tag(v_a_736_) == 1 {
                    leanh::lean_del_object(v___x_738_);
                    v_a_740_ = leanh::lean_ctor_get(v_a_736_, 0);
                    leanh::lean_inc(v_a_740_);
                    leanh::lean_dec_ref_known(v_a_736_, 1);
                    v___x_741_ = lean_array_get_size(v_val_729_);
                    v___x_742_ = lean_nat_dec_lt(v_val_734_, v___x_741_);
                    if v___x_742_ == 0 {
                        leanh::lean_dec(v_val_734_);
                        leanh::lean_dec(v_val_729_);
                        v___x_743_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5;
                        v___x_744_ = leanh::lean_box(0);
                        v___x_745_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_745_, 0, v_a_740_);
                        leanh::lean_ctor_set(v___x_745_, 1, v___x_744_);
                        v___x_746_ = l_Lean_mkConst(v___x_743_, v___x_745_);
                        v___x_747_ = l_Lean_Expr_app___override(v___x_746_, v_arg_720_);
                        v___x_748_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_747_, v_a_673_);
                        if leanh::lean_obj_tag(v___x_748_) == 0 {
                            v_a_749_ = leanh::lean_ctor_get(v___x_748_, 0);
                            leanh::lean_inc(v_a_749_);
                            leanh::lean_dec_ref_known(v___x_748_, 1);
                            v_result_683_ = v_a_749_;
                            v___y_684_ = v_a_673_;
                            v___y_685_ = v_a_674_;
                            v___y_686_ = v_a_675_;
                            v___y_687_ = v_a_676_;
                            v___y_688_ = v_a_677_;
                            state = 2;
                            continue;
                        } else {
                            v_a_750_ = leanh::lean_ctor_get(v___x_748_, 0);
                            v_isSharedCheck_757_ =
                                (!leanh::lean_is_exclusive(v___x_748_)) as u8;
                            if v_isSharedCheck_757_ == 0 {
                                v___x_752_ = v___x_748_;
                                v_isShared_753_ = v_isSharedCheck_757_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_750_);
                                leanh::lean_dec(v___x_748_);
                                v___x_752_ = leanh::lean_box(0);
                                v_isShared_753_ = v_isSharedCheck_757_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        v___x_758_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7;
                        v___x_759_ = leanh::lean_box(0);
                        v___x_760_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_760_, 0, v_a_740_);
                        leanh::lean_ctor_set(v___x_760_, 1, v___x_759_);
                        v___x_761_ = l_Lean_mkConst(v___x_758_, v___x_760_);
                        v___x_762_ = lean_array_fget(v_val_729_, v_val_734_);
                        leanh::lean_dec(v_val_734_);
                        leanh::lean_dec(v_val_729_);
                        v___x_763_ = l_Lean_mkAppB(v___x_761_, v_arg_720_, v___x_762_);
                        v___x_764_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_763_, v_a_673_);
                        if leanh::lean_obj_tag(v___x_764_) == 0 {
                            v_a_765_ = leanh::lean_ctor_get(v___x_764_, 0);
                            leanh::lean_inc(v_a_765_);
                            leanh::lean_dec_ref_known(v___x_764_, 1);
                            v_result_683_ = v_a_765_;
                            v___y_684_ = v_a_673_;
                            v___y_685_ = v_a_674_;
                            v___y_686_ = v_a_675_;
                            v___y_687_ = v_a_676_;
                            v___y_688_ = v_a_677_;
                            state = 2;
                            continue;
                        } else {
                            v_a_766_ = leanh::lean_ctor_get(v___x_764_, 0);
                            v_isSharedCheck_773_ =
                                (!leanh::lean_is_exclusive(v___x_764_)) as u8;
                            if v_isSharedCheck_773_ == 0 {
                                v___x_768_ = v___x_764_;
                                v_isShared_769_ = v_isSharedCheck_773_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_766_);
                                leanh::lean_dec(v___x_764_);
                                v___x_768_ = leanh::lean_box(0);
                                v_isShared_769_ = v_isSharedCheck_773_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_736_);
                    leanh::lean_dec(v_val_734_);
                    leanh::lean_dec(v_val_729_);
                    leanh::lean_dec_ref(v_arg_720_);
                    v___x_774_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                    if v_isShared_739_ == 0 {
                        leanh::lean_ctor_set(v___x_738_, 0, v___x_774_);
                        v___x_776_ = v___x_738_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_777_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
                        v___x_776_ = v_reuseFailAlloc_777_;
                        state = 13;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_753_ == 0 {
                    v___x_755_ = v___x_752_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_756_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
                    v___x_755_ = v_reuseFailAlloc_756_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_755_;
            }
            11 => {
                if v_isShared_769_ == 0 {
                    v___x_771_ = v___x_768_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_772_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
                    v___x_771_ = v_reuseFailAlloc_772_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_771_;
            }
            13 => {
                return v___x_776_;
            }
            14 => {
                if v_isShared_782_ == 0 {
                    v___x_784_ = v___x_781_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_785_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
                    v___x_784_ = v_reuseFailAlloc_785_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_784_;
            }
            16 => {
                return v___x_789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___boxed(
    mut v_e_794_: *mut leanh::LeanObject,
    mut v_a_795_: *mut leanh::LeanObject,
    mut v_a_796_: *mut leanh::LeanObject,
    mut v_a_797_: *mut leanh::LeanObject,
    mut v_a_798_: *mut leanh::LeanObject,
    mut v_a_799_: *mut leanh::LeanObject,
    mut v_a_800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_801_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg(v_e_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
    leanh::lean_dec(v_a_799_);
    leanh::lean_dec_ref(v_a_798_);
    leanh::lean_dec(v_a_797_);
    leanh::lean_dec_ref(v_a_796_);
    leanh::lean_dec(v_a_795_);
    return v_res_801_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f(
    mut v_e_802_: *mut leanh::LeanObject,
    mut v_a_803_: *mut leanh::LeanObject,
    mut v_a_804_: *mut leanh::LeanObject,
    mut v_a_805_: *mut leanh::LeanObject,
    mut v_a_806_: *mut leanh::LeanObject,
    mut v_a_807_: *mut leanh::LeanObject,
    mut v_a_808_: *mut leanh::LeanObject,
    mut v_a_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
    mut v_a_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg(v_e_802_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
    return v___x_813_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___boxed(
    mut v_e_814_: *mut leanh::LeanObject,
    mut v_a_815_: *mut leanh::LeanObject,
    mut v_a_816_: *mut leanh::LeanObject,
    mut v_a_817_: *mut leanh::LeanObject,
    mut v_a_818_: *mut leanh::LeanObject,
    mut v_a_819_: *mut leanh::LeanObject,
    mut v_a_820_: *mut leanh::LeanObject,
    mut v_a_821_: *mut leanh::LeanObject,
    mut v_a_822_: *mut leanh::LeanObject,
    mut v_a_823_: *mut leanh::LeanObject,
    mut v_a_824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_825_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f(v_e_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
    leanh::lean_dec(v_a_823_);
    leanh::lean_dec_ref(v_a_822_);
    leanh::lean_dec(v_a_821_);
    leanh::lean_dec_ref(v_a_820_);
    leanh::lean_dec(v_a_819_);
    leanh::lean_dec_ref(v_a_818_);
    leanh::lean_dec(v_a_817_);
    leanh::lean_dec_ref(v_a_816_);
    leanh::lean_dec(v_a_815_);
    return v_res_825_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_()
-> *mut leanh::LeanObject {
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_;
    v___x_851_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_;
    v___x_852_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_853_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_850_, v___x_851_, v___x_852_);
    return v___x_853_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21____boxed(
    mut v_a_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_855_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_();
    return v_res_855_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_23_()
-> *mut leanh::LeanObject {
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: u8 = 0;
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_;
    v___x_858_ = 1;
    v___x_859_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_860_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_857_, v___x_858_, v___x_859_);
    return v___x_860_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_23____boxed(
    mut v_a_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_862_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_23_();
    return v_res_862_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(
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
    res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
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
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GetElem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_24_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_23_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(
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
    res = initialize_Lean_Meta_Sym_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
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
    res = initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_GetElem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(builtin);
}