// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.Array
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.LitValues Lean.Meta.Sym.InferType Init.CbvSimproc Lean.Meta.Tactic.Cbv.CbvSimproc Lean.Meta.Tactic.Cbv.Util Init.GetElem
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_nat_dec_lt,
};
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__1_value) as *mut crate::leanh::LeanObject,15116455438679371901 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [71, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [103, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__1_value) as *mut crate::leanh::LeanObject,854136310249810287 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__2_value) as *mut crate::leanh::LeanObject,8801718159307809986 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__5_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,16489734963670585437 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [66, 117, 105, 108, 116, 105, 110, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__9_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__10_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,8524095998741210685 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__11_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value) as *mut crate::leanh::LeanObject,16410770112748744871 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5129318075627908122 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__13_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,2216385626806373307 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__14_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__4_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,15815158614411347923 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__15_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__6_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,17744160327223409858 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__16_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__8_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,8318300268641070792 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 109, 112, 65, 114, 114, 97, 121, 71, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__18_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,11452774320338168454 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3_value) as *mut crate::leanh::LeanObject,((( 8 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__0_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__21_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__23_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__23_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__23_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__24_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__23_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__24_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__24_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__24_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__26_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value: crate::leanh::LeanArrayObject<10> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*10) as u16, other: 0, tag: 246 }, m_size: 10, m_capacity: 10, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__20_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__26_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__26_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [71, 101, 116, 69, 108, 101, 109, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [103, 101, 116, 69, 108, 101, 109, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject,1284173141442213452 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject,14790288273250445109 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3_value) as *mut crate::leanh::LeanObject,18184376426117065311 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__4_value) as *mut crate::leanh::LeanObject,9480010471355609749 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 111, 109, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__3_value) as *mut crate::leanh::LeanObject,18184376426117065311 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__6_value) as *mut crate::leanh::LeanObject,4893146552088433753 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [115, 105, 109, 112, 65, 114, 114, 97, 121, 71, 101, 116, 69, 108, 101, 109, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__17_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__0_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut crate::leanh::LeanObject,13759082831902185974 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject,((( 7 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value: crate::leanh::LeanArrayObject<9> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*9) as u16, other: 0, tag: 246 }, m_size: 9, m_capacity: 9, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__2_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__22_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__25_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f(
    mut v_e_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: u8 = 0;
    v___x_440_ = l_Lean_Expr_cleanupAnnotations(v_e_439_);
    v___x_441_ = l_Lean_Expr_isApp(v___x_440_);
    if v___x_441_ == 0 {
        let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_440_);
        v___x_442_ = crate::leanh::lean_box(0);
        return v___x_442_;
    } else {
        let mut v_arg_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_445_: u8 = 0;
        v_arg_443_ = crate::leanh::lean_ctor_get(v___x_440_, 1);
        crate::leanh::lean_inc_ref(v_arg_443_);
        v___x_444_ = l_Lean_Expr_appFnCleanup___redArg(v___x_440_);
        v___x_445_ = l_Lean_Expr_isApp(v___x_444_);
        if v___x_445_ == 0 {
            let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_444_);
            crate::leanh::lean_dec_ref(v_arg_443_);
            v___x_446_ = crate::leanh::lean_box(0);
            return v___x_446_;
        } else {
            let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_449_: u8 = 0;
            v___x_447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_444_);
            v___x_448_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__2;
            v___x_449_ = l_Lean_Expr_isConstOf(v___x_447_, v___x_448_);
            crate::leanh::lean_dec_ref(v___x_447_);
            if v___x_449_ == 0 {
                let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_arg_443_);
                v___x_450_ = crate::leanh::lean_box(0);
                return v___x_450_;
            } else {
                let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_451_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f___closed__3;
                v___x_452_ = l_Lean_Meta_Tactic_Cbv_getListLitElems(v_arg_443_, v___x_451_);
                return v___x_452_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg(
    mut v_e_460_: *mut crate::leanh::LeanObject,
    mut v_a_461_: *mut crate::leanh::LeanObject,
    mut v_a_462_: *mut crate::leanh::LeanObject,
    mut v_a_463_: *mut crate::leanh::LeanObject,
    mut v_a_464_: *mut crate::leanh::LeanObject,
    mut v_a_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: u8 = 0;
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: u8 = 0;
    let mut v_arg_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: u8 = 0;
    let mut v_arg_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: u8 = 0;
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: u8 = 0;
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: u8 = 0;
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: u8 = 0;
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: u8 = 0;
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: u8 = 0;
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_495_: u8 = 0;
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: u8 = 0;
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_512_: u8 = 0;
    let mut v___x_513_: u8 = 0;
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_518_: u8 = 0;
    let mut v_a_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_522_: u8 = 0;
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_526_: u8 = 0;
    let mut v_isSharedCheck_527_: u8 = 0;
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_532_: u8 = 0;
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_470_ = l_Lean_Expr_cleanupAnnotations(v_e_460_);
                v___x_471_ = l_Lean_Expr_isApp(v___x_470_);
                if v___x_471_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_470_);
                    state = 1;
                    continue;
                } else {
                    v___x_472_ = l_Lean_Expr_appFnCleanup___redArg(v___x_470_);
                    v___x_473_ = l_Lean_Expr_isApp(v___x_472_);
                    if v___x_473_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_472_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_474_ = crate::leanh::lean_ctor_get(v___x_472_, 1);
                        crate::leanh::lean_inc_ref(v_arg_474_);
                        v___x_475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_472_);
                        v___x_476_ = l_Lean_Expr_isApp(v___x_475_);
                        if v___x_476_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_475_);
                            crate::leanh::lean_dec_ref(v_arg_474_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_477_ = crate::leanh::lean_ctor_get(v___x_475_, 1);
                            crate::leanh::lean_inc_ref(v_arg_477_);
                            v___x_478_ = l_Lean_Expr_appFnCleanup___redArg(v___x_475_);
                            v___x_479_ = l_Lean_Expr_isApp(v___x_478_);
                            if v___x_479_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_478_);
                                crate::leanh::lean_dec_ref(v_arg_477_);
                                crate::leanh::lean_dec_ref(v_arg_474_);
                                state = 1;
                                continue;
                            } else {
                                v___x_480_ = l_Lean_Expr_appFnCleanup___redArg(v___x_478_);
                                v___x_481_ = l_Lean_Expr_isApp(v___x_480_);
                                if v___x_481_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_480_);
                                    crate::leanh::lean_dec_ref(v_arg_477_);
                                    crate::leanh::lean_dec_ref(v_arg_474_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_482_ = l_Lean_Expr_appFnCleanup___redArg(v___x_480_);
                                    v___x_483_ = l_Lean_Expr_isApp(v___x_482_);
                                    if v___x_483_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_482_);
                                        crate::leanh::lean_dec_ref(v_arg_477_);
                                        crate::leanh::lean_dec_ref(v_arg_474_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_484_ = l_Lean_Expr_appFnCleanup___redArg(v___x_482_);
                                        v___x_485_ = l_Lean_Expr_isApp(v___x_484_);
                                        if v___x_485_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_484_);
                                            crate::leanh::lean_dec_ref(v_arg_477_);
                                            crate::leanh::lean_dec_ref(v_arg_474_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_486_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_484_);
                                            v___x_487_ = l_Lean_Expr_isApp(v___x_486_);
                                            if v___x_487_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_486_);
                                                crate::leanh::lean_dec_ref(v_arg_477_);
                                                crate::leanh::lean_dec_ref(v_arg_474_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_488_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_486_);
                                                v___x_489_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__3;
                                                v___x_490_ =
                                                    l_Lean_Expr_isConstOf(v___x_488_, v___x_489_);
                                                crate::leanh::lean_dec_ref(v___x_488_);
                                                if v___x_490_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_arg_477_);
                                                    crate::leanh::lean_dec_ref(v_arg_474_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_491_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f(v_arg_477_);
                                                    if crate::leanh::lean_obj_tag(v___x_491_) == 1 {
                                                        v_val_492_ = crate::leanh::lean_ctor_get(
                                                            v___x_491_, 0,
                                                        );
                                                        v_isSharedCheck_532_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_491_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_532_ == 0 {
                                                            v___x_494_ = v___x_491_;
                                                            v_isShared_495_ = v_isSharedCheck_532_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_val_492_);
                                                            crate::leanh::lean_dec(v___x_491_);
                                                            v___x_494_ = crate::leanh::lean_box(0);
                                                            v_isShared_495_ = v_isSharedCheck_532_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_491_);
                                                        crate::leanh::lean_dec_ref(v_arg_474_);
                                                        v___x_533_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                                                        v___x_534_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
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
                v___x_469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_469_, 0, v___x_468_);
                return v___x_469_;
            }
            2 => {
                v___x_496_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_474_);
                if crate::leanh::lean_obj_tag(v___x_496_) == 1 {
                    crate::leanh::lean_del_object(v___x_494_);
                    v_val_497_ = crate::leanh::lean_ctor_get(v___x_496_, 0);
                    v_isSharedCheck_527_ = (!crate::leanh::lean_is_exclusive(v___x_496_)) as u8;
                    if v_isSharedCheck_527_ == 0 {
                        v___x_499_ = v___x_496_;
                        v_isShared_500_ = v_isSharedCheck_527_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_497_);
                        crate::leanh::lean_dec(v___x_496_);
                        v___x_499_ = crate::leanh::lean_box(0);
                        v_isShared_500_ = v_isSharedCheck_527_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_496_);
                    crate::leanh::lean_dec(v_val_492_);
                    v___x_528_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                    if v_isShared_495_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_494_, 0);
                        crate::leanh::lean_ctor_set(v___x_494_, 0, v___x_528_);
                        v___x_530_ = v___x_494_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_531_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
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
                    crate::leanh::lean_dec(v_val_497_);
                    crate::leanh::lean_dec(v_val_492_);
                    v___x_503_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_503_, 0 as u32, v___x_502_);
                    crate::leanh::lean_ctor_set_uint8(v___x_503_, 1 as u32, v___x_502_);
                    if v_isShared_500_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_499_, 0);
                        crate::leanh::lean_ctor_set(v___x_499_, 0, v___x_503_);
                        v___x_505_ = v___x_499_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_506_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
                        v___x_505_ = v_reuseFailAlloc_506_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_499_);
                    v_result_507_ = lean_array_fget(v_val_492_, v_val_497_);
                    crate::leanh::lean_dec(v_val_497_);
                    crate::leanh::lean_dec(v_val_492_);
                    crate::leanh::lean_inc(v_result_507_);
                    v___x_508_ = l_Lean_Meta_Sym_mkEqRefl___redArg(
                        v_result_507_,
                        v_a_461_,
                        v_a_462_,
                        v_a_463_,
                        v_a_464_,
                        v_a_465_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_508_) == 0 {
                        v_a_509_ = crate::leanh::lean_ctor_get(v___x_508_, 0);
                        v_isSharedCheck_518_ = (!crate::leanh::lean_is_exclusive(v___x_508_)) as u8;
                        if v_isSharedCheck_518_ == 0 {
                            v___x_511_ = v___x_508_;
                            v_isShared_512_ = v_isSharedCheck_518_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_509_);
                            crate::leanh::lean_dec(v___x_508_);
                            v___x_511_ = crate::leanh::lean_box(0);
                            v_isShared_512_ = v_isSharedCheck_518_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_result_507_);
                        v_a_519_ = crate::leanh::lean_ctor_get(v___x_508_, 0);
                        v_isSharedCheck_526_ = (!crate::leanh::lean_is_exclusive(v___x_508_)) as u8;
                        if v_isSharedCheck_526_ == 0 {
                            v___x_521_ = v___x_508_;
                            v_isShared_522_ = v_isSharedCheck_526_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_519_);
                            crate::leanh::lean_dec(v___x_508_);
                            v___x_521_ = crate::leanh::lean_box(0);
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
                v___x_514_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_514_, 0, v_result_507_);
                crate::leanh::lean_ctor_set(v___x_514_, 1, v_a_509_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_514_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_513_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_514_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_513_,
                );
                if v_isShared_512_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_511_, 0, v___x_514_);
                    v___x_516_ = v___x_511_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
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
                    v_reuseFailAlloc_525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
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
    mut v_e_535_: *mut crate::leanh::LeanObject,
    mut v_a_536_: *mut crate::leanh::LeanObject,
    mut v_a_537_: *mut crate::leanh::LeanObject,
    mut v_a_538_: *mut crate::leanh::LeanObject,
    mut v_a_539_: *mut crate::leanh::LeanObject,
    mut v_a_540_: *mut crate::leanh::LeanObject,
    mut v_a_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_542_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg(v_e_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
    crate::leanh::lean_dec(v_a_540_);
    crate::leanh::lean_dec_ref(v_a_539_);
    crate::leanh::lean_dec(v_a_538_);
    crate::leanh::lean_dec_ref(v_a_537_);
    crate::leanh::lean_dec(v_a_536_);
    return v_res_542_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem(
    mut v_e_543_: *mut crate::leanh::LeanObject,
    mut v_a_544_: *mut crate::leanh::LeanObject,
    mut v_a_545_: *mut crate::leanh::LeanObject,
    mut v_a_546_: *mut crate::leanh::LeanObject,
    mut v_a_547_: *mut crate::leanh::LeanObject,
    mut v_a_548_: *mut crate::leanh::LeanObject,
    mut v_a_549_: *mut crate::leanh::LeanObject,
    mut v_a_550_: *mut crate::leanh::LeanObject,
    mut v_a_551_: *mut crate::leanh::LeanObject,
    mut v_a_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg(v_e_543_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
    return v___x_554_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___boxed(
    mut v_e_555_: *mut crate::leanh::LeanObject,
    mut v_a_556_: *mut crate::leanh::LeanObject,
    mut v_a_557_: *mut crate::leanh::LeanObject,
    mut v_a_558_: *mut crate::leanh::LeanObject,
    mut v_a_559_: *mut crate::leanh::LeanObject,
    mut v_a_560_: *mut crate::leanh::LeanObject,
    mut v_a_561_: *mut crate::leanh::LeanObject,
    mut v_a_562_: *mut crate::leanh::LeanObject,
    mut v_a_563_: *mut crate::leanh::LeanObject,
    mut v_a_564_: *mut crate::leanh::LeanObject,
    mut v_a_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_566_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem(v_e_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
    crate::leanh::lean_dec(v_a_564_);
    crate::leanh::lean_dec_ref(v_a_563_);
    crate::leanh::lean_dec(v_a_562_);
    crate::leanh::lean_dec_ref(v_a_561_);
    crate::leanh::lean_dec(v_a_560_);
    crate::leanh::lean_dec_ref(v_a_559_);
    crate::leanh::lean_dec(v_a_558_);
    crate::leanh::lean_dec_ref(v_a_557_);
    crate::leanh::lean_dec(v_a_556_);
    return v_res_566_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_;
    v___x_646_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__26_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_;
    v___x_647_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_648_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_645_, v___x_646_, v___x_647_);
    return v___x_648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22____boxed(
    mut v_a_649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_650_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_();
    return v_res_650_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_24_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7___closed__19_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_;
    v___x_653_ = 1;
    v___x_654_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_655_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_652_, v___x_653_, v___x_654_);
    return v___x_655_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_24____boxed(
    mut v_a_656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_657_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_24_();
    return v_res_657_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg(
    mut v_e_672_: *mut crate::leanh::LeanObject,
    mut v_a_673_: *mut crate::leanh::LeanObject,
    mut v_a_674_: *mut crate::leanh::LeanObject,
    mut v_a_675_: *mut crate::leanh::LeanObject,
    mut v_a_676_: *mut crate::leanh::LeanObject,
    mut v_a_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_693_: u8 = 0;
    let mut v___x_694_: u8 = 0;
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut v_a_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_703_: u8 = 0;
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_707_: u8 = 0;
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: u8 = 0;
    let mut v_arg_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u8 = 0;
    let mut v_arg_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: u8 = 0;
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: u8 = 0;
    let mut v_arg_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: u8 = 0;
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u8 = 0;
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v_a_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_753_: u8 = 0;
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_757_: u8 = 0;
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_769_: u8 = 0;
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_773_: u8 = 0;
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_778_: u8 = 0;
    let mut v_a_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_782_: u8 = 0;
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_786_: u8 = 0;
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_791_: u8 = 0;
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_708_ = l_Lean_Expr_cleanupAnnotations(v_e_672_);
                v___x_709_ = l_Lean_Expr_isApp(v___x_708_);
                if v___x_709_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_708_);
                    state = 1;
                    continue;
                } else {
                    v_arg_710_ = crate::leanh::lean_ctor_get(v___x_708_, 1);
                    crate::leanh::lean_inc_ref(v_arg_710_);
                    v___x_711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_708_);
                    v___x_712_ = l_Lean_Expr_isApp(v___x_711_);
                    if v___x_712_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_711_);
                        crate::leanh::lean_dec_ref(v_arg_710_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_713_ = crate::leanh::lean_ctor_get(v___x_711_, 1);
                        crate::leanh::lean_inc_ref(v_arg_713_);
                        v___x_714_ = l_Lean_Expr_appFnCleanup___redArg(v___x_711_);
                        v___x_715_ = l_Lean_Expr_isApp(v___x_714_);
                        if v___x_715_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_714_);
                            crate::leanh::lean_dec_ref(v_arg_713_);
                            crate::leanh::lean_dec_ref(v_arg_710_);
                            state = 1;
                            continue;
                        } else {
                            v___x_716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_714_);
                            v___x_717_ = l_Lean_Expr_isApp(v___x_716_);
                            if v___x_717_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_716_);
                                crate::leanh::lean_dec_ref(v_arg_713_);
                                crate::leanh::lean_dec_ref(v_arg_710_);
                                state = 1;
                                continue;
                            } else {
                                v___x_718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_716_);
                                v___x_719_ = l_Lean_Expr_isApp(v___x_718_);
                                if v___x_719_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_718_);
                                    crate::leanh::lean_dec_ref(v_arg_713_);
                                    crate::leanh::lean_dec_ref(v_arg_710_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_720_ = crate::leanh::lean_ctor_get(v___x_718_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_720_);
                                    v___x_721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
                                    v___x_722_ = l_Lean_Expr_isApp(v___x_721_);
                                    if v___x_722_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_721_);
                                        crate::leanh::lean_dec_ref(v_arg_720_);
                                        crate::leanh::lean_dec_ref(v_arg_713_);
                                        crate::leanh::lean_dec_ref(v_arg_710_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_723_ = l_Lean_Expr_appFnCleanup___redArg(v___x_721_);
                                        v___x_724_ = l_Lean_Expr_isApp(v___x_723_);
                                        if v___x_724_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_723_);
                                            crate::leanh::lean_dec_ref(v_arg_720_);
                                            crate::leanh::lean_dec_ref(v_arg_713_);
                                            crate::leanh::lean_dec_ref(v_arg_710_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_725_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_723_);
                                            v___x_726_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__2;
                                            v___x_727_ =
                                                l_Lean_Expr_isConstOf(v___x_725_, v___x_726_);
                                            crate::leanh::lean_dec_ref(v___x_725_);
                                            if v___x_727_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_720_);
                                                crate::leanh::lean_dec_ref(v_arg_713_);
                                                crate::leanh::lean_dec_ref(v_arg_710_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_728_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_getArrayLitElems_x3f(v_arg_713_);
                                                if crate::leanh::lean_obj_tag(v___x_728_) == 1 {
                                                    v_val_729_ =
                                                        crate::leanh::lean_ctor_get(v___x_728_, 0);
                                                    v_isSharedCheck_791_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_728_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_791_ == 0 {
                                                        v___x_731_ = v___x_728_;
                                                        v_isShared_732_ = v_isSharedCheck_791_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_val_729_);
                                                        crate::leanh::lean_dec(v___x_728_);
                                                        v___x_731_ = crate::leanh::lean_box(0);
                                                        v_isShared_732_ = v_isSharedCheck_791_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v___x_728_);
                                                    crate::leanh::lean_dec_ref(v_arg_720_);
                                                    crate::leanh::lean_dec_ref(v_arg_710_);
                                                    v___x_792_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                                                    v___x_793_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
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
                v___x_681_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_681_, 0, v___x_680_);
                return v___x_681_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_result_683_);
                v___x_689_ = l_Lean_Meta_Sym_mkEqRefl___redArg(
                    v_result_683_,
                    v___y_684_,
                    v___y_685_,
                    v___y_686_,
                    v___y_687_,
                    v___y_688_,
                );
                if crate::leanh::lean_obj_tag(v___x_689_) == 0 {
                    v_a_690_ = crate::leanh::lean_ctor_get(v___x_689_, 0);
                    v_isSharedCheck_699_ = (!crate::leanh::lean_is_exclusive(v___x_689_)) as u8;
                    if v_isSharedCheck_699_ == 0 {
                        v___x_692_ = v___x_689_;
                        v_isShared_693_ = v_isSharedCheck_699_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_690_);
                        crate::leanh::lean_dec(v___x_689_);
                        v___x_692_ = crate::leanh::lean_box(0);
                        v_isShared_693_ = v_isSharedCheck_699_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_result_683_);
                    v_a_700_ = crate::leanh::lean_ctor_get(v___x_689_, 0);
                    v_isSharedCheck_707_ = (!crate::leanh::lean_is_exclusive(v___x_689_)) as u8;
                    if v_isSharedCheck_707_ == 0 {
                        v___x_702_ = v___x_689_;
                        v_isShared_703_ = v_isSharedCheck_707_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_700_);
                        crate::leanh::lean_dec(v___x_689_);
                        v___x_702_ = crate::leanh::lean_box(0);
                        v_isShared_703_ = v_isSharedCheck_707_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_694_ = 0;
                v___x_695_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_695_, 0, v_result_683_);
                crate::leanh::lean_ctor_set(v___x_695_, 1, v_a_690_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_695_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_694_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_695_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_694_,
                );
                if v_isShared_693_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_692_, 0, v___x_695_);
                    v___x_697_ = v___x_692_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_698_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
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
                    v_reuseFailAlloc_706_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
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
                if crate::leanh::lean_obj_tag(v___x_733_) == 1 {
                    crate::leanh::lean_del_object(v___x_731_);
                    v_val_734_ = crate::leanh::lean_ctor_get(v___x_733_, 0);
                    crate::leanh::lean_inc(v_val_734_);
                    crate::leanh::lean_dec_ref_known(v___x_733_, 1);
                    crate::leanh::lean_inc_ref(v_arg_720_);
                    v___x_735_ = l_Lean_Meta_Sym_getLevel___redArg(
                        v_arg_720_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_735_) == 0 {
                        v_a_736_ = crate::leanh::lean_ctor_get(v___x_735_, 0);
                        v_isSharedCheck_778_ = (!crate::leanh::lean_is_exclusive(v___x_735_)) as u8;
                        if v_isSharedCheck_778_ == 0 {
                            v___x_738_ = v___x_735_;
                            v_isShared_739_ = v_isSharedCheck_778_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_736_);
                            crate::leanh::lean_dec(v___x_735_);
                            v___x_738_ = crate::leanh::lean_box(0);
                            v_isShared_739_ = v_isSharedCheck_778_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_734_);
                        crate::leanh::lean_dec(v_val_729_);
                        crate::leanh::lean_dec_ref(v_arg_720_);
                        v_a_779_ = crate::leanh::lean_ctor_get(v___x_735_, 0);
                        v_isSharedCheck_786_ = (!crate::leanh::lean_is_exclusive(v___x_735_)) as u8;
                        if v_isSharedCheck_786_ == 0 {
                            v___x_781_ = v___x_735_;
                            v_isShared_782_ = v_isSharedCheck_786_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_779_);
                            crate::leanh::lean_dec(v___x_735_);
                            v___x_781_ = crate::leanh::lean_box(0);
                            v_isShared_782_ = v_isSharedCheck_786_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_733_);
                    crate::leanh::lean_dec(v_val_729_);
                    crate::leanh::lean_dec_ref(v_arg_720_);
                    v___x_787_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                    if v_isShared_732_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_731_, 0);
                        crate::leanh::lean_ctor_set(v___x_731_, 0, v___x_787_);
                        v___x_789_ = v___x_731_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_790_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
                        v___x_789_ = v_reuseFailAlloc_790_;
                        state = 16;
                        continue;
                    }
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_736_) == 1 {
                    crate::leanh::lean_del_object(v___x_738_);
                    v_a_740_ = crate::leanh::lean_ctor_get(v_a_736_, 0);
                    crate::leanh::lean_inc(v_a_740_);
                    crate::leanh::lean_dec_ref_known(v_a_736_, 1);
                    v___x_741_ = lean_array_get_size(v_val_729_);
                    v___x_742_ = lean_nat_dec_lt(v_val_734_, v___x_741_);
                    if v___x_742_ == 0 {
                        crate::leanh::lean_dec(v_val_734_);
                        crate::leanh::lean_dec(v_val_729_);
                        v___x_743_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__5;
                        v___x_744_ = crate::leanh::lean_box(0);
                        v___x_745_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_745_, 0, v_a_740_);
                        crate::leanh::lean_ctor_set(v___x_745_, 1, v___x_744_);
                        v___x_746_ = l_Lean_mkConst(v___x_743_, v___x_745_);
                        v___x_747_ = l_Lean_Expr_app___override(v___x_746_, v_arg_720_);
                        v___x_748_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_747_, v_a_673_);
                        if crate::leanh::lean_obj_tag(v___x_748_) == 0 {
                            v_a_749_ = crate::leanh::lean_ctor_get(v___x_748_, 0);
                            crate::leanh::lean_inc(v_a_749_);
                            crate::leanh::lean_dec_ref_known(v___x_748_, 1);
                            v_result_683_ = v_a_749_;
                            v___y_684_ = v_a_673_;
                            v___y_685_ = v_a_674_;
                            v___y_686_ = v_a_675_;
                            v___y_687_ = v_a_676_;
                            v___y_688_ = v_a_677_;
                            state = 2;
                            continue;
                        } else {
                            v_a_750_ = crate::leanh::lean_ctor_get(v___x_748_, 0);
                            v_isSharedCheck_757_ =
                                (!crate::leanh::lean_is_exclusive(v___x_748_)) as u8;
                            if v_isSharedCheck_757_ == 0 {
                                v___x_752_ = v___x_748_;
                                v_isShared_753_ = v_isSharedCheck_757_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_750_);
                                crate::leanh::lean_dec(v___x_748_);
                                v___x_752_ = crate::leanh::lean_box(0);
                                v_isShared_753_ = v_isSharedCheck_757_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        v___x_758_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg___closed__7;
                        v___x_759_ = crate::leanh::lean_box(0);
                        v___x_760_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_760_, 0, v_a_740_);
                        crate::leanh::lean_ctor_set(v___x_760_, 1, v___x_759_);
                        v___x_761_ = l_Lean_mkConst(v___x_758_, v___x_760_);
                        v___x_762_ = lean_array_fget(v_val_729_, v_val_734_);
                        crate::leanh::lean_dec(v_val_734_);
                        crate::leanh::lean_dec(v_val_729_);
                        v___x_763_ = l_Lean_mkAppB(v___x_761_, v_arg_720_, v___x_762_);
                        v___x_764_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_763_, v_a_673_);
                        if crate::leanh::lean_obj_tag(v___x_764_) == 0 {
                            v_a_765_ = crate::leanh::lean_ctor_get(v___x_764_, 0);
                            crate::leanh::lean_inc(v_a_765_);
                            crate::leanh::lean_dec_ref_known(v___x_764_, 1);
                            v_result_683_ = v_a_765_;
                            v___y_684_ = v_a_673_;
                            v___y_685_ = v_a_674_;
                            v___y_686_ = v_a_675_;
                            v___y_687_ = v_a_676_;
                            v___y_688_ = v_a_677_;
                            state = 2;
                            continue;
                        } else {
                            v_a_766_ = crate::leanh::lean_ctor_get(v___x_764_, 0);
                            v_isSharedCheck_773_ =
                                (!crate::leanh::lean_is_exclusive(v___x_764_)) as u8;
                            if v_isSharedCheck_773_ == 0 {
                                v___x_768_ = v___x_764_;
                                v_isShared_769_ = v_isSharedCheck_773_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_766_);
                                crate::leanh::lean_dec(v___x_764_);
                                v___x_768_ = crate::leanh::lean_box(0);
                                v_isShared_769_ = v_isSharedCheck_773_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_736_);
                    crate::leanh::lean_dec(v_val_734_);
                    crate::leanh::lean_dec(v_val_729_);
                    crate::leanh::lean_dec_ref(v_arg_720_);
                    v___x_774_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___redArg___closed__0;
                    if v_isShared_739_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_738_, 0, v___x_774_);
                        v___x_776_ = v___x_738_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
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
                    v_reuseFailAlloc_756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
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
                    v_reuseFailAlloc_772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
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
                    v_reuseFailAlloc_785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
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
    mut v_e_794_: *mut crate::leanh::LeanObject,
    mut v_a_795_: *mut crate::leanh::LeanObject,
    mut v_a_796_: *mut crate::leanh::LeanObject,
    mut v_a_797_: *mut crate::leanh::LeanObject,
    mut v_a_798_: *mut crate::leanh::LeanObject,
    mut v_a_799_: *mut crate::leanh::LeanObject,
    mut v_a_800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_801_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg(v_e_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
    crate::leanh::lean_dec(v_a_799_);
    crate::leanh::lean_dec_ref(v_a_798_);
    crate::leanh::lean_dec(v_a_797_);
    crate::leanh::lean_dec_ref(v_a_796_);
    crate::leanh::lean_dec(v_a_795_);
    return v_res_801_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f(
    mut v_e_802_: *mut crate::leanh::LeanObject,
    mut v_a_803_: *mut crate::leanh::LeanObject,
    mut v_a_804_: *mut crate::leanh::LeanObject,
    mut v_a_805_: *mut crate::leanh::LeanObject,
    mut v_a_806_: *mut crate::leanh::LeanObject,
    mut v_a_807_: *mut crate::leanh::LeanObject,
    mut v_a_808_: *mut crate::leanh::LeanObject,
    mut v_a_809_: *mut crate::leanh::LeanObject,
    mut v_a_810_: *mut crate::leanh::LeanObject,
    mut v_a_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___redArg(v_e_802_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
    return v___x_813_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___boxed(
    mut v_e_814_: *mut crate::leanh::LeanObject,
    mut v_a_815_: *mut crate::leanh::LeanObject,
    mut v_a_816_: *mut crate::leanh::LeanObject,
    mut v_a_817_: *mut crate::leanh::LeanObject,
    mut v_a_818_: *mut crate::leanh::LeanObject,
    mut v_a_819_: *mut crate::leanh::LeanObject,
    mut v_a_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
    mut v_a_823_: *mut crate::leanh::LeanObject,
    mut v_a_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_825_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f(v_e_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
    crate::leanh::lean_dec(v_a_823_);
    crate::leanh::lean_dec_ref(v_a_822_);
    crate::leanh::lean_dec(v_a_821_);
    crate::leanh::lean_dec_ref(v_a_820_);
    crate::leanh::lean_dec(v_a_819_);
    crate::leanh::lean_dec_ref(v_a_818_);
    crate::leanh::lean_dec(v_a_817_);
    crate::leanh::lean_dec_ref(v_a_816_);
    crate::leanh::lean_dec(v_a_815_);
    return v_res_825_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_;
    v___x_851_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__3_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_;
    v___x_852_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_853_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_850_, v___x_851_, v___x_852_);
    return v___x_853_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21____boxed(
    mut v_a_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_855_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_();
    return v_res_855_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_23_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: u8 = 0;
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12___closed__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_;
    v___x_858_ = 1;
    v___x_859_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_860_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_857_, v___x_858_, v___x_859_);
    return v___x_860_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_23____boxed(
    mut v_a_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_862_ = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_23_();
    return v_res_862_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__7_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_22_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_3512865534____hygCtx___hyg_24_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__12_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_21_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f___regBuiltin___private_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_0__Lean_Meta_Tactic_Cbv_simpArrayGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array_4139808704____hygCtx___hyg_23_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(builtin);
}
