// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SimpUtil
// Imports: Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.ForallProp Lean.Meta.Tactic.Grind.Arith.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs.List Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core Lean.Meta.Tactic.Grind.Util Lean.Meta.Sym.Util Init.Grind.Norm Init.Grind.Config Init.ByCases Lean.Meta.Tactic.Simp.Main
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Grind::Config::{
    initialize_Init_Grind_Config, runtime_initialize_Init_Grind_Config,
};
use crate::r#gen::Init::Grind::Norm::{
    initialize_Init_Grind_Norm, runtime_initialize_Init_Grind_Norm,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_Node_isEmpty___redArg, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_contains;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_isForall, l_Lean_Expr_isProp,
    l_Lean_mkAnd, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkAppB, l_Lean_mkBVar,
    l_Lean_mkConst, l_Lean_mkForall, l_Lean_mkIntAdd, l_Lean_mkIntLE, l_Lean_mkIntLit,
    l_Lean_mkLambda, l_Lean_mkNatAdd, l_Lean_mkNatLE, l_Lean_mkNatLit, l_Lean_mkNot, l_Lean_mkOr,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkEq, l_Lean_Meta_mkEqFalse_x27, l_Lean_Meta_mkNoConfusion,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp_x3f;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_unfoldReducibleStep,
    runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Simproc::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Simproc, l_Lean_Meta_Grind_Arith_addSimproc,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Attr::l_Lean_Meta_Grind_normExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::ForallProp::{
    initialize_Lean_Meta_Tactic_Grind_ForallProp, l_Lean_Meta_Grind_addForallSimproc,
    runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MatchDiscrOnly::{
    initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly, l_Lean_Meta_Grind_addSimpMatchDiscrsOnly,
    runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, l_Lean_Meta_Grind_addPreMatchCondSimproc,
    runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Core::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::List::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_simp,
    runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_SimpExtension_getTheorems___redArg, l_Lean_Meta_SimpTheorems_addDeclToUnfold,
    l_Lean_Meta_addSimpTheorem,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_Simprocs_add,
    l_Lean_Meta_Simp_Simprocs_erase, l_Lean_Meta_Simp_getSEvalSimprocs___redArg,
    l_Lean_Meta_Simp_registerBuiltinDSimproc, l_Lean_Meta_Simp_registerBuiltinSimproc,
    runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_mkContext___redArg;
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::lean_nat_to_int;
use crate::ffi::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
};
use crate::ffi::lean_st_ref_get;
use crate::ffi::lean_expr_eqv;
pub static l_Lean_Meta_Grind_registerNormTheorems___closed__0_value:
    crate::leanh::LeanStringObject<61> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 61,
    m_capacity: 61,
    m_length: 60,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 110, 111, 114, 109, 97, 108, 105, 122, 97, 116, 105,
        111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 104, 97, 118, 101, 32, 97, 108,
        114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 105, 110, 105, 116, 105, 97, 108, 105,
        122, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_registerNormTheorems___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_registerNormTheorems___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_registerNormTheorems___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_registerNormTheorems___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value) as *mut crate::leanh::LeanObject,1655553077289932752 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [98, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value) as *mut crate::leanh::LeanObject,16093780639914376387 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value) as *mut crate::leanh::LeanObject,9753356465987597394 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value) as *mut crate::leanh::LeanObject,4342836574150310743 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value) as *mut crate::leanh::LeanObject,15998082856370921488 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value) as *mut crate::leanh::LeanObject,6148012076188572320 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value) as *mut crate::leanh::LeanObject,13145409667090857818 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__1_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__4_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [84, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            11870096045526947150 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__7_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [70, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            907667957179513571 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__10_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__11_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__12_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [101, 113, 95, 102, 97, 108, 115, 101, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__12_value)
                as *mut crate::leanh::LeanObject,
            11584624889955424335 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__15_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [101, 113, 95, 116, 114, 117, 101, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__15_value)
                as *mut crate::leanh::LeanObject,
            6518306046597794916 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__18_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 113, 95, 115, 101, 108, 102, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__19_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__18_value)
                as *mut crate::leanh::LeanObject,
            12181656444938130656 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__20_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__21_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__21_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__20_value)
                as *mut crate::leanh::LeanObject,
            9255189395584251158 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__23_value: crate::leanh::LeanStringObject<
    16,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        98, 111, 111, 108, 95, 101, 113, 95, 116, 111, 95, 112, 114, 111, 112, 0,
    ],
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__23_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__24_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__23_value)
                as *mut crate::leanh::LeanObject,
            12040479670535018831 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__24_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__26_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [102, 108, 105, 112, 95, 98, 111, 111, 108, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__26_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__27_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__26_value)
                as *mut crate::leanh::LeanObject,
            3966638278125175059 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__29_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__29_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__30_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__30_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__29_value)
                as *mut crate::leanh::LeanObject,
            15761733860085307253 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,8256812394612487643 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__2_value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 105, 116, 101, 0],
};
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8391571994004792969 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 116, 101, 0],
};
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18356704233129443855 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [100, 105, 116, 101, 95, 101, 113, 95, 105, 116, 101, 0],
};
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            14630272000144361786 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 68, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,11972642169564782543 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value) as *mut crate::leanh::LeanObject,((( 5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: crate::leanh::LeanArrayObject<6> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 111, 116, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16612019923665488825 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [69, 120, 105, 115, 116, 115, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5086165725197901121 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__4_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [110, 111, 116, 95, 102, 111, 114, 97, 108, 108, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            1910603056246669445 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__6_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [110, 111, 116, 95, 105, 109, 112, 108, 105, 101, 115, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
            4878178320848305550 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__9_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [79, 114, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            14181099489592536354 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__11_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [65, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            9743492140944907313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__13_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [76, 69, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__14_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [108, 101, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__15_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
        8347582161988589016 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__15_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__15_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__14_value)
                as *mut crate::leanh::LeanObject,
            7316284823769321069 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__16_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 111, 116, 95, 105, 116, 101, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__17_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__16_value)
                as *mut crate::leanh::LeanObject,
            10012160887734445444 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__19_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__20_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__21_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__22_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__21_value)
                as *mut crate::leanh::LeanObject,
            7009148538150066493 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__25_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 111, 116, 95, 108, 101, 95, 101, 113, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__26_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__21_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__26_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__26_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__25_value)
                as *mut crate::leanh::LeanObject,
            5162611250653448781 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__26_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Grind_pushNot___redArg___closed__29_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__29_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__29_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__25_value)
                as *mut crate::leanh::LeanObject,
            4324381115663783915 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__29_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__32_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [110, 111, 116, 95, 101, 113, 95, 116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__32_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__33_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__33_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__33_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__32_value)
                as *mut crate::leanh::LeanObject,
            11675589336077694177 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__33_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__35_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [110, 111, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__35_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__36_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__36_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__35_value)
                as *mut crate::leanh::LeanObject,
            2183596451816792659 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__36_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__37_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__38_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [110, 111, 116, 95, 101, 113, 95, 112, 114, 111, 112, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__38_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__39_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__38_value)
                as *mut crate::leanh::LeanObject,
            14629220074354903389 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__39_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__40_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__42_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 111, 116, 95, 97, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__42_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__43_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__42_value)
                as *mut crate::leanh::LeanObject,
            1943741726499332591 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__43_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__45_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__46_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [110, 111, 116, 95, 111, 114, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__46_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__47_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__46_value)
                as *mut crate::leanh::LeanObject,
            2778442929519348459 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__47_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__48_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__49_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [97, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__50_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__49_value)
                as *mut crate::leanh::LeanObject,
            7839396180116328695 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__50_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__51_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__52_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [110, 111, 116, 95, 101, 120, 105, 115, 116, 115, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__52_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__53_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__52_value)
                as *mut crate::leanh::LeanObject,
            14364261837424776314 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__54_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 111, 116, 95, 110, 111, 116, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__54_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__55_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__54_value)
                as *mut crate::leanh::LeanObject,
            1433178546513579301 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__55_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__56_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__57_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [110, 111, 116, 95, 116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__57_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__58_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__57_value)
                as *mut crate::leanh::LeanObject,
            13154267707496524221 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__58_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__59_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__59: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__60_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__60: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__61_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 111, 116, 95, 102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__61: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__61_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__62_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__61_value)
                as *mut crate::leanh::LeanObject,
            1591550254088102176 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__62: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__62_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__63_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__63: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__64_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__64: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 117, 115, 104, 78, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,14132401962984515005 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__1_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: crate::leanh::LeanArrayObject<2> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [111, 114, 95, 115, 119, 97, 112, 49, 51, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7325503363791193584 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [111, 114, 95, 115, 119, 97, 112, 49, 50, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            3950801501127104890 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__6_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [111, 114, 95, 116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
            15885495678138479146 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__9_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 114, 95, 102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            14011086014131787929 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__12_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 114, 95, 97, 115, 115, 111, 99, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__12_value)
                as *mut crate::leanh::LeanObject,
            8641488168956777649 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__15_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [116, 114, 117, 101, 95, 111, 114, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__15_value)
                as *mut crate::leanh::LeanObject,
            3037741586801491095 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__18_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [102, 97, 108, 115, 101, 95, 111, 114, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__19_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__18_value)
                as *mut crate::leanh::LeanObject,
            7030941873239652894 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 79, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject,11712137666541898468 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__10_value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: crate::leanh::LeanArrayObject<3> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0: u64 = 0;
pub static l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [104, 0],
};
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8738205681931236784 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 69, 113, 67, 104, 101, 97, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject,7640757303824383266 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [117, 110, 102, 111, 108, 100, 82, 101, 100, 117, 99, 105, 98, 108, 101, 83, 105, 109, 112, 114, 111, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut crate::leanh::LeanObject,18075408319424519475 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: crate::leanh::LeanArrayObject<1> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 105, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        114, 101, 100, 117, 99, 101, 82, 101, 112, 108, 105, 99, 97, 116, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9582258842178272501 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        4445492996492257536 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 69, 113, 0],
};
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        233589347272681201 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [71, 69, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__1_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [103, 101, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1755019837031360842 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5555145617058846791 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__3_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [71, 84, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__4_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [103, 116, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__3_value)
                as *mut crate::leanh::LeanObject,
            2272833755566510320 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__4_value)
                as *mut crate::leanh::LeanObject,
            9426339939459091439 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__6_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [99, 97, 115, 116, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__6_value)
                as *mut crate::leanh::LeanObject,
            8075995802451307795 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__8_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [120, 111, 114, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__9_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__8_value)
                as *mut crate::leanh::LeanObject,
            10425341760733586335 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__10_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [78, 101, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__10_value)
                as *mut crate::leanh::LeanObject,
            6695605208187598753 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_normalizeImp___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(
    mut v_x_2220_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2221_: u8 = 0;
    v___x_2221_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2220_);
    return v___x_2221_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(
    mut v_x_2222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2223_: u8 = 0;
    let mut v_r_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2223_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v_x_2222_);
    crate::leanh::lean_dec_ref(v_x_2222_);
    v_r_2224_ = crate::leanh::lean_box((v_res_2223_) as usize);
    return v_r_2224_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(
    mut v_00_u03b2_2225_: *mut crate::leanh::LeanObject,
    mut v_x_2226_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2227_: u8 = 0;
    v___x_2227_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2226_);
    return v___x_2227_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(
    mut v_00_u03b2_2228_: *mut crate::leanh::LeanObject,
    mut v_x_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2230_: u8 = 0;
    let mut v_r_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2230_ =
        l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(
            v_00_u03b2_2228_,
            v_x_2229_,
        );
    crate::leanh::lean_dec_ref(v_x_2229_);
    v_r_2231_ = crate::leanh::lean_box((v_res_2230_) as usize);
    return v_r_2231_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(
    mut v_msgData_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = lean_st_ref_get(v___y_2236_);
    v_env_2239_ = crate::leanh::lean_ctor_get(v___x_2238_, 0);
    crate::leanh::lean_inc_ref(v_env_2239_);
    crate::leanh::lean_dec(v___x_2238_);
    v___x_2240_ = lean_st_ref_get(v___y_2234_);
    v_mctx_2241_ = crate::leanh::lean_ctor_get(v___x_2240_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2241_);
    crate::leanh::lean_dec(v___x_2240_);
    v_lctx_2242_ = crate::leanh::lean_ctor_get(v___y_2233_, 2);
    v_options_2243_ = crate::leanh::lean_ctor_get(v___y_2235_, 2);
    crate::leanh::lean_inc_ref(v_options_2243_);
    crate::leanh::lean_inc_ref(v_lctx_2242_);
    v___x_2244_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2244_, 0, v_env_2239_);
    crate::leanh::lean_ctor_set(v___x_2244_, 1, v_mctx_2241_);
    crate::leanh::lean_ctor_set(v___x_2244_, 2, v_lctx_2242_);
    crate::leanh::lean_ctor_set(v___x_2244_, 3, v_options_2243_);
    v___x_2245_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    crate::leanh::lean_ctor_set(v___x_2245_, 1, v_msgData_2232_);
    v___x_2246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2246_, 0, v___x_2245_);
    return v___x_2246_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3___boxed(
    mut v_msgData_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(v_msgData_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
    crate::leanh::lean_dec(v___y_2251_);
    crate::leanh::lean_dec_ref(v___y_2250_);
    crate::leanh::lean_dec(v___y_2249_);
    crate::leanh::lean_dec_ref(v___y_2248_);
    return v_res_2253_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(
    mut v_msg_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2260_ = crate::leanh::lean_ctor_get(v___y_2257_, 5);
                v___x_2261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(v_msg_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
                v_a_2262_ = crate::leanh::lean_ctor_get(v___x_2261_, 0);
                v_isSharedCheck_2270_ = (!crate::leanh::lean_is_exclusive(v___x_2261_)) as u8;
                if v_isSharedCheck_2270_ == 0 {
                    v___x_2264_ = v___x_2261_;
                    v_isShared_2265_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2262_);
                    crate::leanh::lean_dec(v___x_2261_);
                    v___x_2264_ = crate::leanh::lean_box(0);
                    v_isShared_2265_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2260_);
                v___x_2266_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2266_, 0, v_ref_2260_);
                crate::leanh::lean_ctor_set(v___x_2266_, 1, v_a_2262_);
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2264_, 1);
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg___boxed(
    mut v_msg_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(
        v_msg_2271_,
        v___y_2272_,
        v___y_2273_,
        v___y_2274_,
        v___y_2275_,
    );
    crate::leanh::lean_dec(v___y_2275_);
    crate::leanh::lean_dec_ref(v___y_2274_);
    crate::leanh::lean_dec(v___y_2273_);
    crate::leanh::lean_dec_ref(v___y_2272_);
    return v_res_2277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(
    mut v_as_2278_: *mut crate::leanh::LeanObject,
    mut v_sz_2279_: usize,
    mut v_i_2280_: usize,
    mut v_b_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: usize = 0;
    let mut v___x_2297_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2287_ = lean_usize_dec_lt(v_i_2280_, v_sz_2279_);
                if v___x_2287_ == 0 {
                    v___x_2288_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2288_, 0, v_b_2281_);
                    return v___x_2288_;
                } else {
                    v___x_2289_ = l_Lean_Meta_Grind_normExt;
                    v_a_2290_ = lean_array_uget_borrowed(v_as_2278_, v_i_2280_);
                    v___x_2291_ = 0;
                    v___x_2292_ = 0;
                    v___x_2293_ = crate::leanh::lean_unsigned_to_nat(1000);
                    crate::leanh::lean_inc(v_a_2290_);
                    v___x_2294_ = l_Lean_Meta_addSimpTheorem(
                        v___x_2289_,
                        v_a_2290_,
                        v___x_2287_,
                        v___x_2291_,
                        v___x_2292_,
                        v___x_2293_,
                        v___y_2282_,
                        v___y_2283_,
                        v___y_2284_,
                        v___y_2285_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2294_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2294_, 1);
                        v___x_2295_ = crate::leanh::lean_box(0);
                        v___x_2296_ = 1usize;
                        v___x_2297_ = lean_usize_add(v_i_2280_, v___x_2296_);
                        v_i_2280_ = v___x_2297_;
                        v_b_2281_ = v___x_2295_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2294_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(
    mut v_as_2299_: *mut crate::leanh::LeanObject,
    mut v_sz_2300_: *mut crate::leanh::LeanObject,
    mut v_i_2301_: *mut crate::leanh::LeanObject,
    mut v_b_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2308_: usize = 0;
    let mut v_i_boxed_2309_: usize = 0;
    let mut v_res_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2308_ = crate::leanh::lean_unbox_usize(v_sz_2300_);
    crate::leanh::lean_dec(v_sz_2300_);
    v_i_boxed_2309_ = crate::leanh::lean_unbox_usize(v_i_2301_);
    crate::leanh::lean_dec(v_i_2301_);
    v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_as_2299_, v_sz_boxed_2308_, v_i_boxed_2309_, v_b_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
    crate::leanh::lean_dec(v___y_2306_);
    crate::leanh::lean_dec_ref(v___y_2305_);
    crate::leanh::lean_dec(v___y_2304_);
    crate::leanh::lean_dec_ref(v___y_2303_);
    crate::leanh::lean_dec_ref(v_as_2299_);
    return v_res_2310_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(
    mut v_as_2311_: *mut crate::leanh::LeanObject,
    mut v_sz_2312_: usize,
    mut v_i_2313_: usize,
    mut v_b_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
    mut v___y_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2320_ = lean_usize_dec_lt(v_i_2313_, v_sz_2312_);
                if v___x_2320_ == 0 {
                    v___x_2321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2321_, 0, v_b_2314_);
                    return v___x_2321_;
                } else {
                    v___x_2322_ = l_Lean_Meta_Grind_normExt;
                    v_a_2323_ = lean_array_uget_borrowed(v_as_2311_, v_i_2313_);
                    v___x_2324_ = 0;
                    v___x_2325_ = 0;
                    v___x_2326_ = crate::leanh::lean_unsigned_to_nat(1000);
                    crate::leanh::lean_inc(v_a_2323_);
                    v___x_2327_ = l_Lean_Meta_addSimpTheorem(
                        v___x_2322_,
                        v_a_2323_,
                        v___x_2324_,
                        v___x_2324_,
                        v___x_2325_,
                        v___x_2326_,
                        v___y_2315_,
                        v___y_2316_,
                        v___y_2317_,
                        v___y_2318_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2327_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2327_, 1);
                        v___x_2328_ = crate::leanh::lean_box(0);
                        v___x_2329_ = 1usize;
                        v___x_2330_ = lean_usize_add(v_i_2313_, v___x_2329_);
                        v_i_2313_ = v___x_2330_;
                        v_b_2314_ = v___x_2328_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2327_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(
    mut v_as_2332_: *mut crate::leanh::LeanObject,
    mut v_sz_2333_: *mut crate::leanh::LeanObject,
    mut v_i_2334_: *mut crate::leanh::LeanObject,
    mut v_b_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2341_: usize = 0;
    let mut v_i_boxed_2342_: usize = 0;
    let mut v_res_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2341_ = crate::leanh::lean_unbox_usize(v_sz_2333_);
    crate::leanh::lean_dec(v_sz_2333_);
    v_i_boxed_2342_ = crate::leanh::lean_unbox_usize(v_i_2334_);
    crate::leanh::lean_dec(v_i_2334_);
    v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_as_2332_, v_sz_boxed_2341_, v_i_boxed_2342_, v_b_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
    crate::leanh::lean_dec(v___y_2339_);
    crate::leanh::lean_dec_ref(v___y_2338_);
    crate::leanh::lean_dec(v___y_2337_);
    crate::leanh::lean_dec_ref(v___y_2336_);
    crate::leanh::lean_dec_ref(v_as_2332_);
    return v_res_2343_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2345_ = l_Lean_Meta_Grind_registerNormTheorems___closed__0;
    v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
    return v___x_2346_;
}
pub unsafe fn l_Lean_Meta_Grind_registerNormTheorems(
    mut v_preDeclNames_2347_: *mut crate::leanh::LeanObject,
    mut v_postDeclNames_2348_: *mut crate::leanh::LeanObject,
    mut v_a_2349_: *mut crate::leanh::LeanObject,
    mut v_a_2350_: *mut crate::leanh::LeanObject,
    mut v_a_2351_: *mut crate::leanh::LeanObject,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2360_: usize = 0;
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2363_: usize = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2367_: u8 = 0;
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_unused_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmaNames_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2373_ = l_Lean_Meta_Grind_normExt;
                v___x_2374_ =
                    l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_2373_, v_a_2352_);
                if crate::leanh::lean_obj_tag(v___x_2374_) == 0 {
                    v_a_2375_ = crate::leanh::lean_ctor_get(v___x_2374_, 0);
                    crate::leanh::lean_inc(v_a_2375_);
                    crate::leanh::lean_dec_ref_known(v___x_2374_, 1);
                    v_lemmaNames_2376_ = crate::leanh::lean_ctor_get(v_a_2375_, 2);
                    crate::leanh::lean_inc_ref(v_lemmaNames_2376_);
                    crate::leanh::lean_dec(v_a_2375_);
                    v___x_2377_ =
                        l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_lemmaNames_2376_);
                    crate::leanh::lean_dec_ref(v_lemmaNames_2376_);
                    if v___x_2377_ == 0 {
                        v___x_2378_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_registerNormTheorems___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_registerNormTheorems___closed__1_once
                            ),
                            _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1,
                        );
                        v___x_2379_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(v___x_2378_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
                        return v___x_2379_;
                    } else {
                        v___y_2355_ = v_a_2349_;
                        v___y_2356_ = v_a_2350_;
                        v___y_2357_ = v_a_2351_;
                        v___y_2358_ = v_a_2352_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2380_ = crate::leanh::lean_ctor_get(v___x_2374_, 0);
                    v_isSharedCheck_2387_ = (!crate::leanh::lean_is_exclusive(v___x_2374_)) as u8;
                    if v_isSharedCheck_2387_ == 0 {
                        v___x_2382_ = v___x_2374_;
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2380_);
                        crate::leanh::lean_dec(v___x_2374_);
                        v___x_2382_ = crate::leanh::lean_box(0);
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2359_ = crate::leanh::lean_box(0);
                v_sz_2360_ = lean_array_size(v_preDeclNames_2347_);
                v___x_2361_ = 0usize;
                v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_preDeclNames_2347_, v_sz_2360_, v___x_2361_, v___x_2359_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
                if crate::leanh::lean_obj_tag(v___x_2362_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2362_, 1);
                    v_sz_2363_ = lean_array_size(v_postDeclNames_2348_);
                    v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_postDeclNames_2348_, v_sz_2363_, v___x_2361_, v___x_2359_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
                    if crate::leanh::lean_obj_tag(v___x_2364_) == 0 {
                        v_isSharedCheck_2371_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2364_)) as u8;
                        if v_isSharedCheck_2371_ == 0 {
                            v_unused_2372_ = crate::leanh::lean_ctor_get(v___x_2364_, 0);
                            crate::leanh::lean_dec(v_unused_2372_);
                            v___x_2366_ = v___x_2364_;
                            v_isShared_2367_ = v_isSharedCheck_2371_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2364_);
                            v___x_2366_ = crate::leanh::lean_box(0);
                            v_isShared_2367_ = v_isSharedCheck_2371_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_2364_;
                    }
                } else {
                    return v___x_2362_;
                }
            }
            2 => {
                if v_isShared_2367_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2366_, 0, v___x_2359_);
                    v___x_2369_ = v___x_2366_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2359_);
                    v___x_2369_ = v_reuseFailAlloc_2370_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2369_;
            }
            4 => {
                if v_isShared_2383_ == 0 {
                    v___x_2385_ = v___x_2382_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_registerNormTheorems___boxed(
    mut v_preDeclNames_2388_: *mut crate::leanh::LeanObject,
    mut v_postDeclNames_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_a_2393_: *mut crate::leanh::LeanObject,
    mut v_a_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Lean_Meta_Grind_registerNormTheorems(
        v_preDeclNames_2388_,
        v_postDeclNames_2389_,
        v_a_2390_,
        v_a_2391_,
        v_a_2392_,
        v_a_2393_,
    );
    crate::leanh::lean_dec(v_a_2393_);
    crate::leanh::lean_dec_ref(v_a_2392_);
    crate::leanh::lean_dec(v_a_2391_);
    crate::leanh::lean_dec_ref(v_a_2390_);
    crate::leanh::lean_dec_ref(v_postDeclNames_2389_);
    crate::leanh::lean_dec_ref(v_preDeclNames_2388_);
    return v_res_2395_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(
    mut v_00_u03b1_2396_: *mut crate::leanh::LeanObject,
    mut v_msg_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2403_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(
        v_msg_2397_,
        v___y_2398_,
        v___y_2399_,
        v___y_2400_,
        v___y_2401_,
    );
    return v___x_2403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___boxed(
    mut v_00_u03b1_2404_: *mut crate::leanh::LeanObject,
    mut v_msg_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(
        v_00_u03b1_2404_,
        v_msg_2405_,
        v___y_2406_,
        v___y_2407_,
        v___y_2408_,
        v___y_2409_,
    );
    crate::leanh::lean_dec(v___y_2409_);
    crate::leanh::lean_dec_ref(v___y_2408_);
    crate::leanh::lean_dec(v___y_2407_);
    crate::leanh::lean_dec_ref(v___y_2406_);
    return v_res_2411_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(
    mut v_declName_2435_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2437_: u8 = 0;
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u8 = 0;
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2444_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10;
                v___x_2445_ = lean_name_eq(v_declName_2435_, v___x_2444_);
                if v___x_2445_ == 0 {
                    v___x_2446_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12;
                    v___x_2447_ = lean_name_eq(v_declName_2435_, v___x_2446_);
                    v___y_2437_ = v___x_2447_;
                    state = 1;
                    continue;
                } else {
                    v___y_2437_ = v___x_2445_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2437_ == 0 {
                    v___x_2438_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2;
                    v___x_2439_ = lean_name_eq(v_declName_2435_, v___x_2438_);
                    if v___x_2439_ == 0 {
                        v___x_2440_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5;
                        v___x_2441_ = lean_name_eq(v_declName_2435_, v___x_2440_);
                        if v___x_2441_ == 0 {
                            v___x_2442_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8;
                            v___x_2443_ = lean_name_eq(v_declName_2435_, v___x_2442_);
                            return v___x_2443_;
                        } else {
                            return v___x_2441_;
                        }
                    } else {
                        return v___x_2439_;
                    }
                } else {
                    return v___y_2437_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(
    mut v_declName_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2449_: u8 = 0;
    let mut v_r_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2449_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(
        v_declName_2448_,
    );
    crate::leanh::lean_dec(v_declName_2448_);
    v_r_2450_ = crate::leanh::lean_box((v_res_2449_) as usize);
    return v_r_2450_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = crate::leanh::lean_box(0);
    v___x_2462_ = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
    v___x_2463_ = l_Lean_mkConst(v___x_2462_, v___x_2461_);
    return v___x_2463_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2467_ = crate::leanh::lean_box(0);
    v___x_2468_ = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
    v___x_2469_ = l_Lean_mkConst(v___x_2468_, v___x_2467_);
    return v___x_2469_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = crate::leanh::lean_box(0);
    v___x_2478_ = l_Lean_Meta_Grind_simpEq___redArg___closed__13;
    v___x_2479_ = l_Lean_mkConst(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ = crate::leanh::lean_box(0);
    v___x_2486_ = l_Lean_Meta_Grind_simpEq___redArg___closed__16;
    v___x_2487_ = l_Lean_mkConst(v___x_2486_, v___x_2485_);
    return v___x_2487_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2495_ = crate::leanh::lean_box(0);
    v___x_2496_ = l_Lean_Meta_Grind_simpEq___redArg___closed__21;
    v___x_2497_ = l_Lean_mkConst(v___x_2496_, v___x_2495_);
    return v___x_2497_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2503_ = crate::leanh::lean_box(0);
    v___x_2504_ = l_Lean_Meta_Grind_simpEq___redArg___closed__24;
    v___x_2505_ = l_Lean_mkConst(v___x_2504_, v___x_2503_);
    return v___x_2505_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2511_ = crate::leanh::lean_box(0);
    v___x_2512_ = l_Lean_Meta_Grind_simpEq___redArg___closed__27;
    v___x_2513_ = l_Lean_mkConst(v___x_2512_, v___x_2511_);
    return v___x_2513_;
}
pub unsafe fn l_Lean_Meta_Grind_simpEq___redArg(
    mut v_e_2518_: *mut crate::leanh::LeanObject,
    mut v_a_2519_: *mut crate::leanh::LeanObject,
    mut v_a_2520_: *mut crate::leanh::LeanObject,
    mut v_a_2521_: *mut crate::leanh::LeanObject,
    mut v_a_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2528_: u8 = 0;
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v_arg_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    let mut v_arg_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v_arg_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2550_: u8 = 0;
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: u8 = 0;
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: u8 = 0;
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: u8 = 0;
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2595_: u8 = 0;
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut v_a_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut v___y_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2627_: u8 = 0;
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2638_: u8 = 0;
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: u8 = 0;
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u8 = 0;
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: u8 = 0;
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_a_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2659_: u8 = 0;
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2663_: u8 = 0;
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut v_a_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2524_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2518_, v_a_2520_);
                if crate::leanh::lean_obj_tag(v___x_2524_) == 0 {
                    v_a_2525_ = crate::leanh::lean_ctor_get(v___x_2524_, 0);
                    v_isSharedCheck_2664_ = (!crate::leanh::lean_is_exclusive(v___x_2524_)) as u8;
                    if v_isSharedCheck_2664_ == 0 {
                        v___x_2527_ = v___x_2524_;
                        v_isShared_2528_ = v_isSharedCheck_2664_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2525_);
                        crate::leanh::lean_dec(v___x_2524_);
                        v___x_2527_ = crate::leanh::lean_box(0);
                        v_isShared_2528_ = v_isSharedCheck_2664_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2665_ = crate::leanh::lean_ctor_get(v___x_2524_, 0);
                    v_isSharedCheck_2672_ = (!crate::leanh::lean_is_exclusive(v___x_2524_)) as u8;
                    if v_isSharedCheck_2672_ == 0 {
                        v___x_2667_ = v___x_2524_;
                        v_isShared_2668_ = v_isSharedCheck_2672_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2665_);
                        crate::leanh::lean_dec(v___x_2524_);
                        v___x_2667_ = crate::leanh::lean_box(0);
                        v_isShared_2668_ = v_isSharedCheck_2672_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2534_ = l_Lean_Expr_cleanupAnnotations(v_a_2525_);
                v___x_2535_ = l_Lean_Expr_isApp(v___x_2534_);
                if v___x_2535_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2534_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2536_ = crate::leanh::lean_ctor_get(v___x_2534_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2536_);
                    v___x_2537_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2534_);
                    v___x_2538_ = l_Lean_Expr_isApp(v___x_2537_);
                    if v___x_2538_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2537_);
                        crate::leanh::lean_dec_ref(v_arg_2536_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2539_ = crate::leanh::lean_ctor_get(v___x_2537_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2539_);
                        v___x_2540_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2537_);
                        v___x_2541_ = l_Lean_Expr_isApp(v___x_2540_);
                        if v___x_2541_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2540_);
                            crate::leanh::lean_dec_ref(v_arg_2539_);
                            crate::leanh::lean_dec_ref(v_arg_2536_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2542_ = crate::leanh::lean_ctor_get(v___x_2540_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2542_);
                            v___x_2543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2540_);
                            v___x_2544_ = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
                            v___x_2545_ = l_Lean_Expr_isConstOf(v___x_2543_, v___x_2544_);
                            if v___x_2545_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2543_);
                                crate::leanh::lean_dec_ref(v_arg_2542_);
                                crate::leanh::lean_dec_ref(v_arg_2539_);
                                crate::leanh::lean_dec_ref(v_arg_2536_);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_2527_);
                                crate::leanh::lean_inc_ref(v_arg_2542_);
                                v___x_2546_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                    v_arg_2542_,
                                    v_a_2520_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2546_) == 0 {
                                    v_a_2547_ = crate::leanh::lean_ctor_get(v___x_2546_, 0);
                                    v_isSharedCheck_2655_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2546_)) as u8;
                                    if v_isSharedCheck_2655_ == 0 {
                                        v___x_2549_ = v___x_2546_;
                                        v_isShared_2550_ = v_isSharedCheck_2655_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2547_);
                                        crate::leanh::lean_dec(v___x_2546_);
                                        v___x_2549_ = crate::leanh::lean_box(0);
                                        v_isShared_2550_ = v_isSharedCheck_2655_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2543_);
                                    crate::leanh::lean_dec_ref(v_arg_2542_);
                                    crate::leanh::lean_dec_ref(v_arg_2539_);
                                    crate::leanh::lean_dec_ref(v_arg_2536_);
                                    v_a_2656_ = crate::leanh::lean_ctor_get(v___x_2546_, 0);
                                    v_isSharedCheck_2663_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2546_)) as u8;
                                    if v_isSharedCheck_2663_ == 0 {
                                        v___x_2658_ = v___x_2546_;
                                        v_isShared_2659_ = v_isSharedCheck_2663_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2656_);
                                        crate::leanh::lean_dec(v___x_2546_);
                                        v___x_2658_ = crate::leanh::lean_box(0);
                                        v_isShared_2659_ = v_isSharedCheck_2663_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2530_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_2528_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2527_, 0, v___x_2530_);
                    v___x_2532_ = v___x_2527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
                    v___x_2532_ = v_reuseFailAlloc_2533_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2532_;
            }
            4 => {
                v___x_2551_ = l_Lean_Expr_cleanupAnnotations(v_a_2547_);
                v___x_2552_ = l_Lean_Meta_Grind_simpEq___redArg___closed__3;
                v___x_2553_ = l_Lean_Expr_isConstOf(v___x_2551_, v___x_2552_);
                crate::leanh::lean_dec_ref(v___x_2551_);
                if v___x_2553_ == 0 {
                    v___x_2554_ = lean_expr_eqv(v_arg_2539_, v_arg_2536_);
                    if v___x_2554_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2543_);
                        crate::leanh::lean_dec_ref(v_arg_2542_);
                        v___x_2555_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpEq___redArg___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6,
                        );
                        v___x_2556_ = lean_expr_eqv(v_arg_2536_, v___x_2555_);
                        if v___x_2556_ == 0 {
                            v___x_2557_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__9_once
                                ),
                                _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9,
                            );
                            v___x_2558_ = lean_expr_eqv(v_arg_2536_, v___x_2557_);
                            crate::leanh::lean_dec_ref(v_arg_2536_);
                            if v___x_2558_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2539_);
                                v___x_2559_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                if v_isShared_2550_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2559_);
                                    v___x_2561_ = v___x_2549_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2562_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2562_,
                                        0,
                                        v___x_2559_,
                                    );
                                    v___x_2561_ = v_reuseFailAlloc_2562_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc_ref(v_arg_2539_);
                                v___x_2563_ = l_Lean_mkNot(v_arg_2539_);
                                v___x_2564_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_simpEq___redArg___closed__14
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_simpEq___redArg___closed__14_once
                                    ),
                                    _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14,
                                );
                                v___x_2565_ = l_Lean_Expr_app___override(v___x_2564_, v_arg_2539_);
                                v___x_2566_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2566_, 0, v___x_2565_);
                                v___x_2567_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_2567_, 0, v___x_2563_);
                                crate::leanh::lean_ctor_set(v___x_2567_, 1, v___x_2566_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2567_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                                        as u32,
                                    v___x_2545_,
                                );
                                v___x_2568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2568_, 0, v___x_2567_);
                                if v_isShared_2550_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2568_);
                                    v___x_2570_ = v___x_2549_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2571_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2571_,
                                        0,
                                        v___x_2568_,
                                    );
                                    v___x_2570_ = v_reuseFailAlloc_2571_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_arg_2536_);
                            v___x_2572_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__17
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__17_once
                                ),
                                _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17,
                            );
                            crate::leanh::lean_inc_ref(v_arg_2539_);
                            v___x_2573_ = l_Lean_Expr_app___override(v___x_2572_, v_arg_2539_);
                            v___x_2574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2574_, 0, v___x_2573_);
                            v___x_2575_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_2575_, 0, v_arg_2539_);
                            crate::leanh::lean_ctor_set(v___x_2575_, 1, v___x_2574_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_2575_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v___x_2545_,
                            );
                            v___x_2576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2576_, 0, v___x_2575_);
                            if v_isShared_2550_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2576_);
                                v___x_2578_ = v___x_2549_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_2579_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
                                v___x_2578_ = v_reuseFailAlloc_2579_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2536_);
                        v___x_2580_ = l_Lean_Expr_constLevels_x21(v___x_2543_);
                        crate::leanh::lean_dec_ref(v___x_2543_);
                        v___x_2581_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpEq___redArg___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6,
                        );
                        v___x_2582_ = l_Lean_Meta_Grind_simpEq___redArg___closed__19;
                        v___x_2583_ = l_Lean_mkConst(v___x_2582_, v___x_2580_);
                        v___x_2584_ = l_Lean_mkAppB(v___x_2583_, v_arg_2542_, v_arg_2539_);
                        v___x_2585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2585_, 0, v___x_2584_);
                        v___x_2586_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2586_, 0, v___x_2581_);
                        crate::leanh::lean_ctor_set(v___x_2586_, 1, v___x_2585_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2586_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_2545_,
                        );
                        v___x_2587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2587_, 0, v___x_2586_);
                        if v_isShared_2550_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2587_);
                            v___x_2589_ = v___x_2549_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_2590_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
                            v___x_2589_ = v_reuseFailAlloc_2590_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_2591_ = l_Lean_Expr_getAppFn(v_arg_2536_);
                    if crate::leanh::lean_obj_tag(v___x_2591_) == 4 {
                        v_declName_2592_ = crate::leanh::lean_ctor_get(v___x_2591_, 0);
                        crate::leanh::lean_inc(v_declName_2592_);
                        crate::leanh::lean_dec_ref_known(v___x_2591_, 2);
                        v___x_2593_ = l_Lean_Meta_Grind_simpEq___redArg___closed__21;
                        v___x_2648_ = lean_name_eq(v_declName_2592_, v___x_2593_);
                        if v___x_2648_ == 0 {
                            v___x_2649_ = l_Lean_Meta_Grind_simpEq___redArg___closed__30;
                            v___x_2650_ = lean_name_eq(v_declName_2592_, v___x_2649_);
                            v___y_2638_ = v___x_2650_;
                            state = 16;
                            continue;
                        } else {
                            v___y_2638_ = v___x_2648_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2591_);
                        crate::leanh::lean_dec_ref(v___x_2543_);
                        crate::leanh::lean_dec_ref(v_arg_2542_);
                        crate::leanh::lean_dec_ref(v_arg_2539_);
                        crate::leanh::lean_dec_ref(v_arg_2536_);
                        v___x_2651_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        if v_isShared_2550_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2651_);
                            v___x_2653_ = v___x_2549_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_2654_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
                            v___x_2653_ = v_reuseFailAlloc_2654_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_2561_;
            }
            6 => {
                return v___x_2570_;
            }
            7 => {
                return v___x_2578_;
            }
            8 => {
                return v___x_2589_;
            }
            9 => {
                if v___y_2595_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2543_);
                    crate::leanh::lean_dec_ref(v_arg_2542_);
                    crate::leanh::lean_dec_ref(v_arg_2539_);
                    crate::leanh::lean_dec_ref(v_arg_2536_);
                    v___x_2596_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    if v_isShared_2550_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2596_);
                        v___x_2598_ = v___x_2549_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
                        v___x_2598_ = v_reuseFailAlloc_2599_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2549_);
                    v___x_2600_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__22),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpEq___redArg___closed__22_once
                        ),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22,
                    );
                    crate::leanh::lean_inc_ref(v_arg_2539_);
                    crate::leanh::lean_inc_ref(v_arg_2542_);
                    crate::leanh::lean_inc_ref(v___x_2543_);
                    v___x_2601_ = l_Lean_mkApp3(v___x_2543_, v_arg_2542_, v_arg_2539_, v___x_2600_);
                    crate::leanh::lean_inc_ref(v_arg_2536_);
                    v___x_2602_ = l_Lean_mkApp3(v___x_2543_, v_arg_2542_, v_arg_2536_, v___x_2600_);
                    v___x_2603_ = l_Lean_Meta_mkEq(
                        v___x_2601_,
                        v___x_2602_,
                        v_a_2519_,
                        v_a_2520_,
                        v_a_2521_,
                        v_a_2522_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2603_) == 0 {
                        v_a_2604_ = crate::leanh::lean_ctor_get(v___x_2603_, 0);
                        v_isSharedCheck_2616_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2603_)) as u8;
                        if v_isSharedCheck_2616_ == 0 {
                            v___x_2606_ = v___x_2603_;
                            v_isShared_2607_ = v_isSharedCheck_2616_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2604_);
                            crate::leanh::lean_dec(v___x_2603_);
                            v___x_2606_ = crate::leanh::lean_box(0);
                            v_isShared_2607_ = v_isSharedCheck_2616_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2539_);
                        crate::leanh::lean_dec_ref(v_arg_2536_);
                        v_a_2617_ = crate::leanh::lean_ctor_get(v___x_2603_, 0);
                        v_isSharedCheck_2624_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2603_)) as u8;
                        if v_isSharedCheck_2624_ == 0 {
                            v___x_2619_ = v___x_2603_;
                            v_isShared_2620_ = v_isSharedCheck_2624_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2617_);
                            crate::leanh::lean_dec(v___x_2603_);
                            v___x_2619_ = crate::leanh::lean_box(0);
                            v_isShared_2620_ = v_isSharedCheck_2624_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            10 => {
                return v___x_2598_;
            }
            11 => {
                v___x_2608_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__25),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__25_once),
                    _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25,
                );
                v___x_2609_ = l_Lean_mkAppB(v___x_2608_, v_arg_2539_, v_arg_2536_);
                v___x_2610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2610_, 0, v___x_2609_);
                v___x_2611_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2611_, 0, v_a_2604_);
                crate::leanh::lean_ctor_set(v___x_2611_, 1, v___x_2610_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2611_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2553_,
                );
                v___x_2612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2612_, 0, v___x_2611_);
                if v_isShared_2607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2606_, 0, v___x_2612_);
                    v___x_2614_ = v___x_2606_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
                    v___x_2614_ = v_reuseFailAlloc_2615_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2614_;
            }
            13 => {
                if v_isShared_2620_ == 0 {
                    v___x_2622_ = v___x_2619_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
                    v___x_2622_ = v_reuseFailAlloc_2623_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2622_;
            }
            15 => {
                if v___y_2627_ == 0 {
                    v___x_2628_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v___y_2626_);
                    crate::leanh::lean_dec(v___y_2626_);
                    if v___x_2628_ == 0 {
                        v___x_2629_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_2592_);
                        crate::leanh::lean_dec(v_declName_2592_);
                        v___y_2595_ = v___x_2629_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_2592_);
                        v___y_2595_ = v___x_2628_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2626_);
                    crate::leanh::lean_dec(v_declName_2592_);
                    crate::leanh::lean_del_object(v___x_2549_);
                    crate::leanh::lean_inc_ref(v_arg_2539_);
                    crate::leanh::lean_inc_ref(v_arg_2536_);
                    v___x_2630_ = l_Lean_mkApp3(v___x_2543_, v_arg_2542_, v_arg_2536_, v_arg_2539_);
                    v___x_2631_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__28),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpEq___redArg___closed__28_once
                        ),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28,
                    );
                    v___x_2632_ = l_Lean_mkAppB(v___x_2631_, v_arg_2539_, v_arg_2536_);
                    v___x_2633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2633_, 0, v___x_2632_);
                    v___x_2634_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2630_);
                    crate::leanh::lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2634_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_2553_,
                    );
                    v___x_2635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2635_, 0, v___x_2634_);
                    v___x_2636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2636_, 0, v___x_2635_);
                    return v___x_2636_;
                }
            }
            16 => {
                if v___y_2638_ == 0 {
                    v___x_2639_ = l_Lean_Expr_getAppFn(v_arg_2539_);
                    if crate::leanh::lean_obj_tag(v___x_2639_) == 4 {
                        v_declName_2640_ = crate::leanh::lean_ctor_get(v___x_2639_, 0);
                        crate::leanh::lean_inc(v_declName_2640_);
                        crate::leanh::lean_dec_ref_known(v___x_2639_, 2);
                        v___x_2641_ = lean_name_eq(v_declName_2640_, v___x_2593_);
                        if v___x_2641_ == 0 {
                            v___x_2642_ = l_Lean_Meta_Grind_simpEq___redArg___closed__30;
                            v___x_2643_ = lean_name_eq(v_declName_2640_, v___x_2642_);
                            v___y_2626_ = v_declName_2640_;
                            v___y_2627_ = v___x_2643_;
                            state = 15;
                            continue;
                        } else {
                            v___y_2626_ = v_declName_2640_;
                            v___y_2627_ = v___x_2641_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2639_);
                        crate::leanh::lean_dec(v_declName_2592_);
                        crate::leanh::lean_del_object(v___x_2549_);
                        crate::leanh::lean_dec_ref(v___x_2543_);
                        crate::leanh::lean_dec_ref(v_arg_2542_);
                        crate::leanh::lean_dec_ref(v_arg_2539_);
                        crate::leanh::lean_dec_ref(v_arg_2536_);
                        v___x_2644_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        v___x_2645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2645_, 0, v___x_2644_);
                        return v___x_2645_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2592_);
                    crate::leanh::lean_del_object(v___x_2549_);
                    crate::leanh::lean_dec_ref(v___x_2543_);
                    crate::leanh::lean_dec_ref(v_arg_2542_);
                    crate::leanh::lean_dec_ref(v_arg_2539_);
                    crate::leanh::lean_dec_ref(v_arg_2536_);
                    v___x_2646_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    v___x_2647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2647_, 0, v___x_2646_);
                    return v___x_2647_;
                }
            }
            17 => {
                return v___x_2653_;
            }
            18 => {
                if v_isShared_2659_ == 0 {
                    v___x_2661_ = v___x_2658_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2662_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
                    v___x_2661_ = v_reuseFailAlloc_2662_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2661_;
            }
            20 => {
                if v_isShared_2668_ == 0 {
                    v___x_2670_ = v___x_2667_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
                    v___x_2670_ = v_reuseFailAlloc_2671_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_simpEq___redArg___boxed(
    mut v_e_2673_: *mut crate::leanh::LeanObject,
    mut v_a_2674_: *mut crate::leanh::LeanObject,
    mut v_a_2675_: *mut crate::leanh::LeanObject,
    mut v_a_2676_: *mut crate::leanh::LeanObject,
    mut v_a_2677_: *mut crate::leanh::LeanObject,
    mut v_a_2678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ =
        l_Lean_Meta_Grind_simpEq___redArg(v_e_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
    crate::leanh::lean_dec(v_a_2677_);
    crate::leanh::lean_dec_ref(v_a_2676_);
    crate::leanh::lean_dec(v_a_2675_);
    crate::leanh::lean_dec_ref(v_a_2674_);
    return v_res_2679_;
}
pub unsafe fn l_Lean_Meta_Grind_simpEq(
    mut v_e_2680_: *mut crate::leanh::LeanObject,
    mut v_a_2681_: *mut crate::leanh::LeanObject,
    mut v_a_2682_: *mut crate::leanh::LeanObject,
    mut v_a_2683_: *mut crate::leanh::LeanObject,
    mut v_a_2684_: *mut crate::leanh::LeanObject,
    mut v_a_2685_: *mut crate::leanh::LeanObject,
    mut v_a_2686_: *mut crate::leanh::LeanObject,
    mut v_a_2687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2689_ =
        l_Lean_Meta_Grind_simpEq___redArg(v_e_2680_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
    return v___x_2689_;
}
pub unsafe fn l_Lean_Meta_Grind_simpEq___boxed(
    mut v_e_2690_: *mut crate::leanh::LeanObject,
    mut v_a_2691_: *mut crate::leanh::LeanObject,
    mut v_a_2692_: *mut crate::leanh::LeanObject,
    mut v_a_2693_: *mut crate::leanh::LeanObject,
    mut v_a_2694_: *mut crate::leanh::LeanObject,
    mut v_a_2695_: *mut crate::leanh::LeanObject,
    mut v_a_2696_: *mut crate::leanh::LeanObject,
    mut v_a_2697_: *mut crate::leanh::LeanObject,
    mut v_a_2698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2699_ = l_Lean_Meta_Grind_simpEq(
        v_e_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_,
    );
    crate::leanh::lean_dec(v_a_2697_);
    crate::leanh::lean_dec_ref(v_a_2696_);
    crate::leanh::lean_dec(v_a_2695_);
    crate::leanh::lean_dec_ref(v_a_2694_);
    crate::leanh::lean_dec(v_a_2693_);
    crate::leanh::lean_dec_ref(v_a_2692_);
    crate::leanh::lean_dec(v_a_2691_);
    return v_res_2699_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2719_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
    v___x_2720_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
    v___x_2721_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_simpEq___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2722_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2719_, v___x_2720_, v___x_2721_);
    return v___x_2722_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12____boxed(
    mut v_a_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2724_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_();
    return v_res_2724_;
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte___redArg(
    mut v_e_2734_: *mut crate::leanh::LeanObject,
    mut v_a_2735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: u8 = 0;
    let mut v_arg_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    let mut v_arg_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: u8 = 0;
    let mut v_arg_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: u8 = 0;
    let mut v_arg_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v_arg_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: u8 = 0;
    let mut v_body_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: u8 = 0;
    let mut v_body_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut v_a_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2737_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2734_, v_a_2735_);
                if crate::leanh::lean_obj_tag(v___x_2737_) == 0 {
                    v_a_2738_ = crate::leanh::lean_ctor_get(v___x_2737_, 0);
                    v_isSharedCheck_2788_ = (!crate::leanh::lean_is_exclusive(v___x_2737_)) as u8;
                    if v_isSharedCheck_2788_ == 0 {
                        v___x_2740_ = v___x_2737_;
                        v_isShared_2741_ = v_isSharedCheck_2788_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2738_);
                        crate::leanh::lean_dec(v___x_2737_);
                        v___x_2740_ = crate::leanh::lean_box(0);
                        v_isShared_2741_ = v_isSharedCheck_2788_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2789_ = crate::leanh::lean_ctor_get(v___x_2737_, 0);
                    v_isSharedCheck_2796_ = (!crate::leanh::lean_is_exclusive(v___x_2737_)) as u8;
                    if v_isSharedCheck_2796_ == 0 {
                        v___x_2791_ = v___x_2737_;
                        v_isShared_2792_ = v_isSharedCheck_2796_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2789_);
                        crate::leanh::lean_dec(v___x_2737_);
                        v___x_2791_ = crate::leanh::lean_box(0);
                        v_isShared_2792_ = v_isSharedCheck_2796_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2747_ = l_Lean_Expr_cleanupAnnotations(v_a_2738_);
                v___x_2748_ = l_Lean_Expr_isApp(v___x_2747_);
                if v___x_2748_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2747_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2749_ = crate::leanh::lean_ctor_get(v___x_2747_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2749_);
                    v___x_2750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2747_);
                    v___x_2751_ = l_Lean_Expr_isApp(v___x_2750_);
                    if v___x_2751_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2750_);
                        crate::leanh::lean_dec_ref(v_arg_2749_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2752_ = crate::leanh::lean_ctor_get(v___x_2750_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2752_);
                        v___x_2753_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2750_);
                        v___x_2754_ = l_Lean_Expr_isApp(v___x_2753_);
                        if v___x_2754_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2753_);
                            crate::leanh::lean_dec_ref(v_arg_2752_);
                            crate::leanh::lean_dec_ref(v_arg_2749_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2755_ = crate::leanh::lean_ctor_get(v___x_2753_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2755_);
                            v___x_2756_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2753_);
                            v___x_2757_ = l_Lean_Expr_isApp(v___x_2756_);
                            if v___x_2757_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2756_);
                                crate::leanh::lean_dec_ref(v_arg_2755_);
                                crate::leanh::lean_dec_ref(v_arg_2752_);
                                crate::leanh::lean_dec_ref(v_arg_2749_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_2758_ = crate::leanh::lean_ctor_get(v___x_2756_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2758_);
                                v___x_2759_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2756_);
                                v___x_2760_ = l_Lean_Expr_isApp(v___x_2759_);
                                if v___x_2760_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2759_);
                                    crate::leanh::lean_dec_ref(v_arg_2758_);
                                    crate::leanh::lean_dec_ref(v_arg_2755_);
                                    crate::leanh::lean_dec_ref(v_arg_2752_);
                                    crate::leanh::lean_dec_ref(v_arg_2749_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_2761_ = crate::leanh::lean_ctor_get(v___x_2759_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_2761_);
                                    v___x_2762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2759_);
                                    v___x_2763_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__1;
                                    v___x_2764_ = l_Lean_Expr_isConstOf(v___x_2762_, v___x_2763_);
                                    if v___x_2764_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2762_);
                                        crate::leanh::lean_dec_ref(v_arg_2761_);
                                        crate::leanh::lean_dec_ref(v_arg_2758_);
                                        crate::leanh::lean_dec_ref(v_arg_2755_);
                                        crate::leanh::lean_dec_ref(v_arg_2752_);
                                        crate::leanh::lean_dec_ref(v_arg_2749_);
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_del_object(v___x_2740_);
                                        if crate::leanh::lean_obj_tag(v_arg_2752_) == 6 {
                                            v_body_2765_ =
                                                crate::leanh::lean_ctor_get(v_arg_2752_, 2);
                                            crate::leanh::lean_inc_ref(v_body_2765_);
                                            crate::leanh::lean_dec_ref_known(v_arg_2752_, 3);
                                            v___x_2766_ = l_Lean_Expr_hasLooseBVars(v_body_2765_);
                                            if v___x_2766_ == 0 {
                                                if crate::leanh::lean_obj_tag(v_arg_2749_) == 6 {
                                                    v_body_2767_ =
                                                        crate::leanh::lean_ctor_get(v_arg_2749_, 2);
                                                    crate::leanh::lean_inc_ref(v_body_2767_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_arg_2749_,
                                                        3,
                                                    );
                                                    v___x_2768_ =
                                                        l_Lean_Expr_hasLooseBVars(v_body_2767_);
                                                    if v___x_2768_ == 0 {
                                                        v___x_2769_ = l_Lean_Expr_constLevels_x21(
                                                            v___x_2762_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v___x_2762_);
                                                        v___x_2770_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__3;
                                                        crate::leanh::lean_inc(v___x_2769_);
                                                        v___x_2771_ = l_Lean_mkConst(
                                                            v___x_2770_,
                                                            v___x_2769_,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_body_2767_);
                                                        crate::leanh::lean_inc_ref(v_body_2765_);
                                                        crate::leanh::lean_inc_ref(v_arg_2755_);
                                                        crate::leanh::lean_inc_ref(v_arg_2758_);
                                                        crate::leanh::lean_inc_ref(v_arg_2761_);
                                                        v___x_2772_ = l_Lean_mkApp5(
                                                            v___x_2771_,
                                                            v_arg_2761_,
                                                            v_arg_2758_,
                                                            v_arg_2755_,
                                                            v_body_2765_,
                                                            v_body_2767_,
                                                        );
                                                        v___x_2773_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__5;
                                                        v___x_2774_ = l_Lean_mkConst(
                                                            v___x_2773_,
                                                            v___x_2769_,
                                                        );
                                                        v___x_2775_ = l_Lean_mkApp5(
                                                            v___x_2774_,
                                                            v_arg_2758_,
                                                            v_arg_2761_,
                                                            v_body_2765_,
                                                            v_body_2767_,
                                                            v_arg_2755_,
                                                        );
                                                        v___x_2776_ = crate::leanh::lean_alloc_ctor(
                                                            1,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2776_,
                                                            0,
                                                            v___x_2775_,
                                                        );
                                                        v___x_2777_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (1) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2777_,
                                                            0,
                                                            v___x_2772_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2777_,
                                                            1,
                                                            v___x_2776_,
                                                        );
                                                        crate::leanh::lean_ctor_set_uint8(
                                                            v___x_2777_,
                                                            (core::mem::size_of::<
                                                                *mut crate::leanh::LeanObject,
                                                            >(
                                                            ) * 2)
                                                                as u32,
                                                            v___x_2764_,
                                                        );
                                                        v___x_2778_ = crate::leanh::lean_alloc_ctor(
                                                            1,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2778_,
                                                            0,
                                                            v___x_2777_,
                                                        );
                                                        v___x_2779_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2779_,
                                                            0,
                                                            v___x_2778_,
                                                        );
                                                        return v___x_2779_;
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_body_2767_);
                                                        crate::leanh::lean_dec_ref(v_body_2765_);
                                                        crate::leanh::lean_dec_ref(v___x_2762_);
                                                        crate::leanh::lean_dec_ref(v_arg_2761_);
                                                        crate::leanh::lean_dec_ref(v_arg_2758_);
                                                        crate::leanh::lean_dec_ref(v_arg_2755_);
                                                        v___x_2780_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                        v___x_2781_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2781_,
                                                            0,
                                                            v___x_2780_,
                                                        );
                                                        return v___x_2781_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_body_2765_);
                                                    crate::leanh::lean_dec_ref(v___x_2762_);
                                                    crate::leanh::lean_dec_ref(v_arg_2761_);
                                                    crate::leanh::lean_dec_ref(v_arg_2758_);
                                                    crate::leanh::lean_dec_ref(v_arg_2755_);
                                                    crate::leanh::lean_dec_ref(v_arg_2749_);
                                                    v___x_2782_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                    v___x_2783_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2783_,
                                                        0,
                                                        v___x_2782_,
                                                    );
                                                    return v___x_2783_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_body_2765_);
                                                crate::leanh::lean_dec_ref(v___x_2762_);
                                                crate::leanh::lean_dec_ref(v_arg_2761_);
                                                crate::leanh::lean_dec_ref(v_arg_2758_);
                                                crate::leanh::lean_dec_ref(v_arg_2755_);
                                                crate::leanh::lean_dec_ref(v_arg_2749_);
                                                v___x_2784_ =
                                                    l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                v___x_2785_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2785_,
                                                    0,
                                                    v___x_2784_,
                                                );
                                                return v___x_2785_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_2762_);
                                            crate::leanh::lean_dec_ref(v_arg_2761_);
                                            crate::leanh::lean_dec_ref(v_arg_2758_);
                                            crate::leanh::lean_dec_ref(v_arg_2755_);
                                            crate::leanh::lean_dec_ref(v_arg_2752_);
                                            crate::leanh::lean_dec_ref(v_arg_2749_);
                                            v___x_2786_ =
                                                l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                            v___x_2787_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2787_,
                                                0,
                                                v___x_2786_,
                                            );
                                            return v___x_2787_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2743_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_2741_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2740_, 0, v___x_2743_);
                    v___x_2745_ = v___x_2740_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
                    v___x_2745_ = v_reuseFailAlloc_2746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2745_;
            }
            4 => {
                if v_isShared_2792_ == 0 {
                    v___x_2794_ = v___x_2791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2795_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
                    v___x_2794_ = v_reuseFailAlloc_2795_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte___redArg___boxed(
    mut v_e_2797_: *mut crate::leanh::LeanObject,
    mut v_a_2798_: *mut crate::leanh::LeanObject,
    mut v_a_2799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2800_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_2797_, v_a_2798_);
    crate::leanh::lean_dec(v_a_2798_);
    return v_res_2800_;
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte(
    mut v_e_2801_: *mut crate::leanh::LeanObject,
    mut v_a_2802_: *mut crate::leanh::LeanObject,
    mut v_a_2803_: *mut crate::leanh::LeanObject,
    mut v_a_2804_: *mut crate::leanh::LeanObject,
    mut v_a_2805_: *mut crate::leanh::LeanObject,
    mut v_a_2806_: *mut crate::leanh::LeanObject,
    mut v_a_2807_: *mut crate::leanh::LeanObject,
    mut v_a_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2810_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_2801_, v_a_2806_);
    return v___x_2810_;
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte___boxed(
    mut v_e_2811_: *mut crate::leanh::LeanObject,
    mut v_a_2812_: *mut crate::leanh::LeanObject,
    mut v_a_2813_: *mut crate::leanh::LeanObject,
    mut v_a_2814_: *mut crate::leanh::LeanObject,
    mut v_a_2815_: *mut crate::leanh::LeanObject,
    mut v_a_2816_: *mut crate::leanh::LeanObject,
    mut v_a_2817_: *mut crate::leanh::LeanObject,
    mut v_a_2818_: *mut crate::leanh::LeanObject,
    mut v_a_2819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2820_ = l_Lean_Meta_Grind_simpDIte(
        v_e_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_,
    );
    crate::leanh::lean_dec(v_a_2818_);
    crate::leanh::lean_dec_ref(v_a_2817_);
    crate::leanh::lean_dec(v_a_2816_);
    crate::leanh::lean_dec_ref(v_a_2815_);
    crate::leanh::lean_dec(v_a_2814_);
    crate::leanh::lean_dec_ref(v_a_2813_);
    crate::leanh::lean_dec(v_a_2812_);
    return v_res_2820_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_;
    v___x_2842_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_;
    v___x_2843_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_simpDIte___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2844_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2841_, v___x_2842_, v___x_2843_);
    return v___x_2844_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13____boxed(
    mut v_a_2845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2846_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_();
    return v_res_2846_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2863_ = crate::leanh::lean_box(0);
    v___x_2864_ = l_Lean_Meta_Grind_pushNot___redArg___closed__7;
    v___x_2865_ = l_Lean_mkConst(v___x_2864_, v___x_2863_);
    return v___x_2865_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ = crate::leanh::lean_box(0);
    v___x_2883_ = l_Lean_Meta_Grind_pushNot___redArg___closed__17;
    v___x_2884_ = l_Lean_mkConst(v___x_2883_, v___x_2882_);
    return v___x_2884_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2891_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2892_ = lean_nat_to_int(v___x_2891_);
    return v___x_2892_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2893_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__23_once),
        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23,
    );
    v___x_2894_ = l_Lean_mkIntLit(v___x_2893_);
    return v___x_2894_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2899_ = crate::leanh::lean_box(0);
    v___x_2900_ = l_Lean_Meta_Grind_pushNot___redArg___closed__26;
    v___x_2901_ = l_Lean_mkConst(v___x_2900_, v___x_2899_);
    return v___x_2901_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2903_ = l_Lean_mkNatLit(v___x_2902_);
    return v___x_2903_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2907_ = crate::leanh::lean_box(0);
    v___x_2908_ = l_Lean_Meta_Grind_pushNot___redArg___closed__29;
    v___x_2909_ = l_Lean_mkConst(v___x_2908_, v___x_2907_);
    return v___x_2909_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2910_ = crate::leanh::lean_box(0);
    v___x_2911_ = l_Lean_Meta_Grind_simpEq___redArg___closed__30;
    v___x_2912_ = l_Lean_mkConst(v___x_2911_, v___x_2910_);
    return v___x_2912_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = crate::leanh::lean_box(0);
    v___x_2918_ = l_Lean_Meta_Grind_pushNot___redArg___closed__33;
    v___x_2919_ = l_Lean_mkConst(v___x_2918_, v___x_2917_);
    return v___x_2919_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2924_ = crate::leanh::lean_box(0);
    v___x_2925_ = l_Lean_Meta_Grind_pushNot___redArg___closed__36;
    v___x_2926_ = l_Lean_mkConst(v___x_2925_, v___x_2924_);
    return v___x_2926_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2932_ = crate::leanh::lean_box(0);
    v___x_2933_ = l_Lean_Meta_Grind_pushNot___redArg___closed__39;
    v___x_2934_ = l_Lean_mkConst(v___x_2933_, v___x_2932_);
    return v___x_2934_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2935_ = crate::leanh::lean_box(0);
    v___x_2936_ = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
    v___x_2937_ = l_Lean_mkConst(v___x_2936_, v___x_2935_);
    return v___x_2937_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2943_ = crate::leanh::lean_box(0);
    v___x_2944_ = l_Lean_Meta_Grind_pushNot___redArg___closed__43;
    v___x_2945_ = l_Lean_mkConst(v___x_2944_, v___x_2943_);
    return v___x_2945_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2946_ = crate::leanh::lean_box(0);
    v___x_2947_ = l_Lean_Meta_Grind_pushNot___redArg___closed__12;
    v___x_2948_ = l_Lean_mkConst(v___x_2947_, v___x_2946_);
    return v___x_2948_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2954_ = crate::leanh::lean_box(0);
    v___x_2955_ = l_Lean_Meta_Grind_pushNot___redArg___closed__47;
    v___x_2956_ = l_Lean_mkConst(v___x_2955_, v___x_2954_);
    return v___x_2956_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2960_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2961_ = l_Lean_mkBVar(v___x_2960_);
    return v___x_2961_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__56()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2972_ = crate::leanh::lean_box(0);
    v___x_2973_ = l_Lean_Meta_Grind_pushNot___redArg___closed__55;
    v___x_2974_ = l_Lean_mkConst(v___x_2973_, v___x_2972_);
    return v___x_2974_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2980_ = crate::leanh::lean_box(0);
    v___x_2981_ = l_Lean_Meta_Grind_pushNot___redArg___closed__58;
    v___x_2982_ = l_Lean_mkConst(v___x_2981_, v___x_2980_);
    return v___x_2982_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__59),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__59_once),
        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59,
    );
    v___x_2984_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2984_, 0, v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2990_ = crate::leanh::lean_box(0);
    v___x_2991_ = l_Lean_Meta_Grind_pushNot___redArg___closed__62;
    v___x_2992_ = l_Lean_mkConst(v___x_2991_, v___x_2990_);
    return v___x_2992_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__64()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2993_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__63),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__63_once),
        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__63,
    );
    v___x_2994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2994_, 0, v___x_2993_);
    return v___x_2994_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNot___redArg(
    mut v_e_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
    mut v_a_2997_: *mut crate::leanh::LeanObject,
    mut v_a_2998_: *mut crate::leanh::LeanObject,
    mut v_a_2999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v_arg_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: u8 = 0;
    let mut v___y_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3025_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_a_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut v___y_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3065_: u8 = 0;
    let mut v___y_3066_: u8 = 0;
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3083_: u8 = 0;
    let mut v___x_3084_: u8 = 0;
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3092_: u8 = 0;
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: u8 = 0;
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: u8 = 0;
    let mut v_arg_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: u8 = 0;
    let mut v_arg_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: u8 = 0;
    let mut v___x_3111_: u8 = 0;
    let mut v_arg_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: u8 = 0;
    let mut v_arg_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: u8 = 0;
    let mut v___x_3121_: u8 = 0;
    let mut v_arg_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: u8 = 0;
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3141_: u8 = 0;
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: u8 = 0;
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_a_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v___x_3182_: u8 = 0;
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: u8 = 0;
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: u8 = 0;
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3217_: u8 = 0;
    let mut v_a_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut v_a_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3286_: u8 = 0;
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_a_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut v_isSharedCheck_3322_: u8 = 0;
    let mut v_a_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2995_);
                v___x_3001_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2995_, v_a_2997_);
                if crate::leanh::lean_obj_tag(v___x_3001_) == 0 {
                    v_a_3002_ = crate::leanh::lean_ctor_get(v___x_3001_, 0);
                    v_isSharedCheck_3322_ = (!crate::leanh::lean_is_exclusive(v___x_3001_)) as u8;
                    if v_isSharedCheck_3322_ == 0 {
                        v___x_3004_ = v___x_3001_;
                        v_isShared_3005_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3002_);
                        crate::leanh::lean_dec(v___x_3001_);
                        v___x_3004_ = crate::leanh::lean_box(0);
                        v_isShared_3005_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2995_);
                    v_a_3323_ = crate::leanh::lean_ctor_get(v___x_3001_, 0);
                    v_isSharedCheck_3330_ = (!crate::leanh::lean_is_exclusive(v___x_3001_)) as u8;
                    if v_isSharedCheck_3330_ == 0 {
                        v___x_3325_ = v___x_3001_;
                        v_isShared_3326_ = v_isSharedCheck_3330_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3323_);
                        crate::leanh::lean_dec(v___x_3001_);
                        v___x_3325_ = crate::leanh::lean_box(0);
                        v_isShared_3326_ = v_isSharedCheck_3330_;
                        state = 37;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3011_ = l_Lean_Expr_cleanupAnnotations(v_a_3002_);
                v___x_3012_ = l_Lean_Expr_isApp(v___x_3011_);
                if v___x_3012_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3011_);
                    crate::leanh::lean_dec_ref(v_e_2995_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3013_ = crate::leanh::lean_ctor_get(v___x_3011_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3013_);
                    v___x_3014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3011_);
                    v___x_3015_ = l_Lean_Meta_Grind_pushNot___redArg___closed__1;
                    v___x_3016_ = l_Lean_Expr_isConstOf(v___x_3014_, v___x_3015_);
                    crate::leanh::lean_dec_ref(v___x_3014_);
                    if v___x_3016_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_3013_);
                        crate::leanh::lean_dec_ref(v_e_2995_);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_3004_);
                        v___x_3088_ =
                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3013_, v_a_2997_);
                        if crate::leanh::lean_obj_tag(v___x_3088_) == 0 {
                            v_a_3089_ = crate::leanh::lean_ctor_get(v___x_3088_, 0);
                            v_isSharedCheck_3313_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3088_)) as u8;
                            if v_isSharedCheck_3313_ == 0 {
                                v___x_3091_ = v___x_3088_;
                                v_isShared_3092_ = v_isSharedCheck_3313_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3089_);
                                crate::leanh::lean_dec(v___x_3088_);
                                v___x_3091_ = crate::leanh::lean_box(0);
                                v_isShared_3092_ = v_isSharedCheck_3313_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_2995_);
                            v_a_3314_ = crate::leanh::lean_ctor_get(v___x_3088_, 0);
                            v_isSharedCheck_3321_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3088_)) as u8;
                            if v_isSharedCheck_3321_ == 0 {
                                v___x_3316_ = v___x_3088_;
                                v_isShared_3317_ = v_isSharedCheck_3321_;
                                state = 35;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3314_);
                                crate::leanh::lean_dec(v___x_3088_);
                                v___x_3316_ = crate::leanh::lean_box(0);
                                v_isShared_3317_ = v_isSharedCheck_3321_;
                                state = 35;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3007_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_3005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3004_, 0, v___x_3007_);
                    v___x_3009_ = v___x_3004_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3010_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
                    v___x_3009_ = v_reuseFailAlloc_3010_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3009_;
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_3022_);
                crate::leanh::lean_inc_ref_n(v___y_3023_, 3);
                crate::leanh::lean_inc(v___y_3024_);
                v___x_3026_ = l_Lean_mkLambda(v___y_3024_, v___y_3025_, v___y_3023_, v___y_3022_);
                v___x_3027_ = l_Lean_mkNot(v___y_3022_);
                v___x_3028_ = l_Lean_mkLambda(v___y_3024_, v___y_3025_, v___y_3023_, v___x_3027_);
                v___x_3029_ = l_Lean_Meta_getLevel(
                    v___y_3023_,
                    v___y_3021_,
                    v___y_3020_,
                    v___y_3019_,
                    v___y_3018_,
                );
                if crate::leanh::lean_obj_tag(v___x_3029_) == 0 {
                    v_a_3030_ = crate::leanh::lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3048_ = (!crate::leanh::lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3048_ == 0 {
                        v___x_3032_ = v___x_3029_;
                        v_isShared_3033_ = v_isSharedCheck_3048_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3030_);
                        crate::leanh::lean_dec(v___x_3029_);
                        v___x_3032_ = crate::leanh::lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3048_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3028_);
                    crate::leanh::lean_dec_ref(v___x_3026_);
                    crate::leanh::lean_dec_ref(v___y_3023_);
                    v_a_3049_ = crate::leanh::lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3056_ = (!crate::leanh::lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3056_ == 0 {
                        v___x_3051_ = v___x_3029_;
                        v_isShared_3052_ = v_isSharedCheck_3056_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3049_);
                        crate::leanh::lean_dec(v___x_3029_);
                        v___x_3051_ = crate::leanh::lean_box(0);
                        v_isShared_3052_ = v_isSharedCheck_3056_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3034_ = l_Lean_Meta_Grind_pushNot___redArg___closed__3;
                v___x_3035_ = crate::leanh::lean_box(0);
                v___x_3036_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3036_, 0, v_a_3030_);
                crate::leanh::lean_ctor_set(v___x_3036_, 1, v___x_3035_);
                crate::leanh::lean_inc_ref(v___x_3036_);
                v___x_3037_ = l_Lean_mkConst(v___x_3034_, v___x_3036_);
                crate::leanh::lean_inc_ref(v___y_3023_);
                v___x_3038_ = l_Lean_mkAppB(v___x_3037_, v___y_3023_, v___x_3028_);
                v___x_3039_ = l_Lean_Meta_Grind_pushNot___redArg___closed__5;
                v___x_3040_ = l_Lean_mkConst(v___x_3039_, v___x_3036_);
                v___x_3041_ = l_Lean_mkAppB(v___x_3040_, v___y_3023_, v___x_3026_);
                v___x_3042_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3042_, 0, v___x_3041_);
                v___x_3043_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3043_, 0, v___x_3038_);
                crate::leanh::lean_ctor_set(v___x_3043_, 1, v___x_3042_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3043_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3016_,
                );
                v___x_3044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3044_, 0, v___x_3043_);
                if v_isShared_3033_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3032_, 0, v___x_3044_);
                    v___x_3046_ = v___x_3032_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
                    v___x_3046_ = v_reuseFailAlloc_3047_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3046_;
            }
            7 => {
                if v_isShared_3052_ == 0 {
                    v___x_3054_ = v___x_3051_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
                    v___x_3054_ = v_reuseFailAlloc_3055_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3054_;
            }
            9 => {
                if v___y_3066_ == 0 {
                    v___y_3018_ = v___y_3060_;
                    v___y_3019_ = v___y_3059_;
                    v___y_3020_ = v___y_3058_;
                    v___y_3021_ = v___y_3062_;
                    v___y_3022_ = v___y_3061_;
                    v___y_3023_ = v___y_3064_;
                    v___y_3024_ = v___y_3063_;
                    v___y_3025_ = v___y_3065_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3063_);
                    crate::leanh::lean_inc_ref(v___y_3061_);
                    v___x_3067_ = l_Lean_mkNot(v___y_3061_);
                    crate::leanh::lean_inc_ref(v___y_3064_);
                    v___x_3068_ = l_Lean_mkAnd(v___y_3064_, v___x_3067_);
                    v___x_3069_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__8),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__8_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8,
                    );
                    v___x_3070_ = l_Lean_mkAppB(v___x_3069_, v___y_3064_, v___y_3061_);
                    v___x_3071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3071_, 0, v___x_3070_);
                    v___x_3072_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3072_, 0, v___x_3068_);
                    crate::leanh::lean_ctor_set(v___x_3072_, 1, v___x_3071_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3072_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_3016_,
                    );
                    v___x_3073_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3073_, 0, v___x_3072_);
                    v___x_3074_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3074_, 0, v___x_3073_);
                    return v___x_3074_;
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_e_2995_) == 7 {
                    v_binderName_3080_ = crate::leanh::lean_ctor_get(v_e_2995_, 0);
                    crate::leanh::lean_inc(v_binderName_3080_);
                    v_binderType_3081_ = crate::leanh::lean_ctor_get(v_e_2995_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_3081_);
                    v_body_3082_ = crate::leanh::lean_ctor_get(v_e_2995_, 2);
                    crate::leanh::lean_inc_ref(v_body_3082_);
                    v_binderInfo_3083_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_2995_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_e_2995_, 3);
                    v___x_3084_ = l_Lean_Expr_isProp(v_binderType_3081_);
                    if v___x_3084_ == 0 {
                        v___y_3058_ = v___y_3077_;
                        v___y_3059_ = v___y_3078_;
                        v___y_3060_ = v___y_3079_;
                        v___y_3061_ = v_body_3082_;
                        v___y_3062_ = v___y_3076_;
                        v___y_3063_ = v_binderName_3080_;
                        v___y_3064_ = v_binderType_3081_;
                        v___y_3065_ = v_binderInfo_3083_;
                        v___y_3066_ = v___x_3084_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3085_ = l_Lean_Expr_hasLooseBVars(v_body_3082_);
                        if v___x_3085_ == 0 {
                            v___y_3058_ = v___y_3077_;
                            v___y_3059_ = v___y_3078_;
                            v___y_3060_ = v___y_3079_;
                            v___y_3061_ = v_body_3082_;
                            v___y_3062_ = v___y_3076_;
                            v___y_3063_ = v_binderName_3080_;
                            v___y_3064_ = v_binderType_3081_;
                            v___y_3065_ = v_binderInfo_3083_;
                            v___y_3066_ = v___x_3084_;
                            state = 9;
                            continue;
                        } else {
                            v___y_3018_ = v___y_3079_;
                            v___y_3019_ = v___y_3078_;
                            v___y_3020_ = v___y_3077_;
                            v___y_3021_ = v___y_3076_;
                            v___y_3022_ = v_body_3082_;
                            v___y_3023_ = v_binderType_3081_;
                            v___y_3024_ = v_binderName_3080_;
                            v___y_3025_ = v_binderInfo_3083_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2995_);
                    v___x_3086_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    v___x_3087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3087_, 0, v___x_3086_);
                    return v___x_3087_;
                }
            }
            11 => {
                v___x_3093_ = l_Lean_Expr_cleanupAnnotations(v_a_3089_);
                v___x_3094_ = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
                v___x_3095_ = l_Lean_Expr_isConstOf(v___x_3093_, v___x_3094_);
                if v___x_3095_ == 0 {
                    v___x_3096_ = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
                    v___x_3097_ = l_Lean_Expr_isConstOf(v___x_3093_, v___x_3096_);
                    if v___x_3097_ == 0 {
                        v___x_3098_ = l_Lean_Expr_isApp(v___x_3093_);
                        if v___x_3098_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3093_);
                            crate::leanh::lean_del_object(v___x_3091_);
                            v___y_3076_ = v_a_2996_;
                            v___y_3077_ = v_a_2997_;
                            v___y_3078_ = v_a_2998_;
                            v___y_3079_ = v_a_2999_;
                            state = 10;
                            continue;
                        } else {
                            v_arg_3099_ = crate::leanh::lean_ctor_get(v___x_3093_, 1);
                            crate::leanh::lean_inc_ref(v_arg_3099_);
                            v___x_3100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3093_);
                            v___x_3101_ = l_Lean_Expr_isConstOf(v___x_3100_, v___x_3015_);
                            if v___x_3101_ == 0 {
                                v___x_3102_ = l_Lean_Expr_isApp(v___x_3100_);
                                if v___x_3102_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_3100_);
                                    crate::leanh::lean_dec_ref(v_arg_3099_);
                                    crate::leanh::lean_del_object(v___x_3091_);
                                    v___y_3076_ = v_a_2996_;
                                    v___y_3077_ = v_a_2997_;
                                    v___y_3078_ = v_a_2998_;
                                    v___y_3079_ = v_a_2999_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_arg_3103_ = crate::leanh::lean_ctor_get(v___x_3100_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_3103_);
                                    v___x_3104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3100_);
                                    v___x_3105_ = l_Lean_Meta_Grind_pushNot___redArg___closed__3;
                                    v___x_3106_ = l_Lean_Expr_isConstOf(v___x_3104_, v___x_3105_);
                                    if v___x_3106_ == 0 {
                                        v___x_3107_ =
                                            l_Lean_Meta_Grind_pushNot___redArg___closed__10;
                                        v___x_3108_ =
                                            l_Lean_Expr_isConstOf(v___x_3104_, v___x_3107_);
                                        if v___x_3108_ == 0 {
                                            v___x_3109_ =
                                                l_Lean_Meta_Grind_pushNot___redArg___closed__12;
                                            v___x_3110_ =
                                                l_Lean_Expr_isConstOf(v___x_3104_, v___x_3109_);
                                            if v___x_3110_ == 0 {
                                                v___x_3111_ = l_Lean_Expr_isApp(v___x_3104_);
                                                if v___x_3111_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_3104_);
                                                    crate::leanh::lean_dec_ref(v_arg_3103_);
                                                    crate::leanh::lean_dec_ref(v_arg_3099_);
                                                    crate::leanh::lean_del_object(v___x_3091_);
                                                    v___y_3076_ = v_a_2996_;
                                                    v___y_3077_ = v_a_2997_;
                                                    v___y_3078_ = v_a_2998_;
                                                    v___y_3079_ = v_a_2999_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    v_arg_3112_ =
                                                        crate::leanh::lean_ctor_get(v___x_3104_, 1);
                                                    crate::leanh::lean_inc_ref(v_arg_3112_);
                                                    v___x_3113_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_3104_,
                                                    );
                                                    v___x_3114_ = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
                                                    v___x_3115_ = l_Lean_Expr_isConstOf(
                                                        v___x_3113_,
                                                        v___x_3114_,
                                                    );
                                                    if v___x_3115_ == 0 {
                                                        v___x_3116_ =
                                                            l_Lean_Expr_isApp(v___x_3113_);
                                                        if v___x_3116_ == 0 {
                                                            crate::leanh::lean_dec_ref(v___x_3113_);
                                                            crate::leanh::lean_dec_ref(v_arg_3112_);
                                                            crate::leanh::lean_dec_ref(v_arg_3103_);
                                                            crate::leanh::lean_dec_ref(v_arg_3099_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_3091_,
                                                            );
                                                            v___y_3076_ = v_a_2996_;
                                                            v___y_3077_ = v_a_2997_;
                                                            v___y_3078_ = v_a_2998_;
                                                            v___y_3079_ = v_a_2999_;
                                                            state = 10;
                                                            continue;
                                                        } else {
                                                            v_arg_3117_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v___x_3113_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_inc_ref(v_arg_3117_);
                                                            v___x_3118_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_3113_,
                                                                );
                                                            v___x_3119_ = l_Lean_Meta_Grind_pushNot___redArg___closed__15;
                                                            v___x_3120_ = l_Lean_Expr_isConstOf(
                                                                v___x_3118_,
                                                                v___x_3119_,
                                                            );
                                                            if v___x_3120_ == 0 {
                                                                v___x_3121_ =
                                                                    l_Lean_Expr_isApp(v___x_3118_);
                                                                if v___x_3121_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_3118_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3117_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3112_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3103_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3099_,
                                                                    );
                                                                    crate::leanh::lean_del_object(
                                                                        v___x_3091_,
                                                                    );
                                                                    v___y_3076_ = v_a_2996_;
                                                                    v___y_3077_ = v_a_2997_;
                                                                    v___y_3078_ = v_a_2998_;
                                                                    v___y_3079_ = v_a_2999_;
                                                                    state = 10;
                                                                    continue;
                                                                } else {
                                                                    v_arg_3122_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3118_,
                                                                            1,
                                                                        );
                                                                    crate::leanh::lean_inc_ref(
                                                                        v_arg_3122_,
                                                                    );
                                                                    v___x_3123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3118_);
                                                                    v___x_3124_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__3;
                                                                    v___x_3125_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_3123_,
                                                                            v___x_3124_,
                                                                        );
                                                                    if v___x_3125_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_3123_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3122_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3117_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3112_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3103_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3099_,
                                                                        );
                                                                        crate::leanh::lean_del_object(v___x_3091_);
                                                                        v___y_3076_ = v_a_2996_;
                                                                        v___y_3077_ = v_a_2997_;
                                                                        v___y_3078_ = v_a_2998_;
                                                                        v___y_3079_ = v_a_2999_;
                                                                        state = 10;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_2995_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_3103_,
                                                                        );
                                                                        v___x_3126_ = l_Lean_mkNot(
                                                                            v_arg_3103_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_3099_,
                                                                        );
                                                                        v___x_3127_ = l_Lean_mkNot(
                                                                            v_arg_3099_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_3112_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_3117_,
                                                                        );
                                                                        v___x_3128_ = l_Lean_mkApp5(
                                                                            v___x_3123_,
                                                                            v_arg_3122_,
                                                                            v_arg_3117_,
                                                                            v_arg_3112_,
                                                                            v___x_3126_,
                                                                            v___x_3127_,
                                                                        );
                                                                        v___x_3129_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__18), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__18_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18);
                                                                        v___x_3130_ = l_Lean_mkApp4(
                                                                            v___x_3129_,
                                                                            v_arg_3117_,
                                                                            v_arg_3112_,
                                                                            v_arg_3103_,
                                                                            v_arg_3099_,
                                                                        );
                                                                        v___x_3131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                                        crate::leanh::lean_ctor_set(
                                                                            v___x_3131_,
                                                                            0,
                                                                            v___x_3130_,
                                                                        );
                                                                        v___x_3132_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                                                        crate::leanh::lean_ctor_set(
                                                                            v___x_3132_,
                                                                            0,
                                                                            v___x_3128_,
                                                                        );
                                                                        crate::leanh::lean_ctor_set(
                                                                            v___x_3132_,
                                                                            1,
                                                                            v___x_3131_,
                                                                        );
                                                                        crate::leanh::lean_ctor_set_uint8(v___x_3132_, (core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u32, v___x_3125_);
                                                                        v___x_3133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                                        crate::leanh::lean_ctor_set(
                                                                            v___x_3133_,
                                                                            0,
                                                                            v___x_3132_,
                                                                        );
                                                                        if v_isShared_3092_ == 0 {
                                                                            crate::leanh::lean_ctor_set(v___x_3091_, 0, v___x_3133_);
                                                                            v___x_3135_ =
                                                                                v___x_3091_;
                                                                            state = 12;
                                                                            continue;
                                                                        } else {
                                                                            v_reuseFailAlloc_3136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
                                                                            v___x_3135_ = v_reuseFailAlloc_3136_;
                                                                            state = 12;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_3118_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3112_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_3091_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_2995_,
                                                                );
                                                                v___x_3137_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3117_, v_a_2997_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_3137_,
                                                                ) == 0
                                                                {
                                                                    v_a_3138_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3137_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3173_ = (!crate::leanh::lean_is_exclusive(v___x_3137_)) as u8;
                                                                    if v_isSharedCheck_3173_ == 0 {
                                                                        v___x_3140_ = v___x_3137_;
                                                                        v_isShared_3141_ =
                                                                            v_isSharedCheck_3173_;
                                                                        state = 13;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_3138_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_3137_,
                                                                        );
                                                                        v___x_3140_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3141_ =
                                                                            v_isSharedCheck_3173_;
                                                                        state = 13;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3103_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3099_,
                                                                    );
                                                                    v_a_3174_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3137_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3181_ = (!crate::leanh::lean_is_exclusive(v___x_3137_)) as u8;
                                                                    if v_isSharedCheck_3181_ == 0 {
                                                                        v___x_3176_ = v___x_3137_;
                                                                        v_isShared_3177_ =
                                                                            v_isSharedCheck_3181_;
                                                                        state = 17;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_3174_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_3137_,
                                                                        );
                                                                        v___x_3176_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3177_ =
                                                                            v_isSharedCheck_3181_;
                                                                        state = 17;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_e_2995_);
                                                        v___x_3182_ =
                                                            l_Lean_Expr_isProp(v_arg_3112_);
                                                        if v___x_3182_ == 0 {
                                                            crate::leanh::lean_del_object(
                                                                v___x_3091_,
                                                            );
                                                            v___x_3183_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3099_, v_a_2997_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_3183_,
                                                            ) == 0
                                                            {
                                                                v_a_3184_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3183_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3217_ = (!crate::leanh::lean_is_exclusive(v___x_3183_)) as u8;
                                                                if v_isSharedCheck_3217_ == 0 {
                                                                    v___x_3186_ = v___x_3183_;
                                                                    v_isShared_3187_ =
                                                                        v_isSharedCheck_3217_;
                                                                    state = 19;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_3184_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3183_,
                                                                    );
                                                                    v___x_3186_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_3187_ =
                                                                        v_isSharedCheck_3217_;
                                                                    state = 19;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_3113_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3112_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3103_,
                                                                );
                                                                v_a_3218_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3183_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3225_ = (!crate::leanh::lean_is_exclusive(v___x_3183_)) as u8;
                                                                if v_isSharedCheck_3225_ == 0 {
                                                                    v___x_3220_ = v___x_3183_;
                                                                    v_isShared_3221_ =
                                                                        v_isSharedCheck_3225_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_3218_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3183_,
                                                                    );
                                                                    v___x_3220_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_3221_ =
                                                                        v_isSharedCheck_3225_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_inc_ref(v_arg_3099_);
                                                            v___x_3226_ = l_Lean_mkNot(v_arg_3099_);
                                                            crate::leanh::lean_inc_ref(v_arg_3103_);
                                                            v___x_3227_ = l_Lean_mkApp3(
                                                                v___x_3113_,
                                                                v_arg_3112_,
                                                                v_arg_3103_,
                                                                v___x_3226_,
                                                            );
                                                            v___x_3228_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__40), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__40_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40);
                                                            v___x_3229_ = l_Lean_mkAppB(
                                                                v___x_3228_,
                                                                v_arg_3103_,
                                                                v_arg_3099_,
                                                            );
                                                            v___x_3230_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3230_,
                                                                0,
                                                                v___x_3229_,
                                                            );
                                                            v___x_3231_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    0,
                                                                    2,
                                                                    (1) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3231_,
                                                                0,
                                                                v___x_3227_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3231_,
                                                                1,
                                                                v___x_3230_,
                                                            );
                                                            crate::leanh::lean_ctor_set_uint8(
                                                                v___x_3231_,
                                                                (core::mem::size_of::<
                                                                    *mut crate::leanh::LeanObject,
                                                                >(
                                                                ) * 2)
                                                                    as u32,
                                                                v___x_3115_,
                                                            );
                                                            v___x_3232_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3232_,
                                                                0,
                                                                v___x_3231_,
                                                            );
                                                            if v_isShared_3092_ == 0 {
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_3091_,
                                                                    0,
                                                                    v___x_3232_,
                                                                );
                                                                v___x_3234_ = v___x_3091_;
                                                                state = 25;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_3235_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v_reuseFailAlloc_3235_,
                                                                    0,
                                                                    v___x_3232_,
                                                                );
                                                                v___x_3234_ =
                                                                    v_reuseFailAlloc_3235_;
                                                                state = 25;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3104_);
                                                crate::leanh::lean_dec_ref(v_e_2995_);
                                                v___x_3236_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__41), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__41_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__41);
                                                crate::leanh::lean_inc_ref(v_arg_3103_);
                                                v___x_3237_ = l_Lean_mkNot(v_arg_3103_);
                                                crate::leanh::lean_inc_ref(v_arg_3099_);
                                                v___x_3238_ = l_Lean_mkNot(v_arg_3099_);
                                                v___x_3239_ = l_Lean_mkAppB(
                                                    v___x_3236_,
                                                    v___x_3237_,
                                                    v___x_3238_,
                                                );
                                                v___x_3240_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__44), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__44_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__44);
                                                v___x_3241_ = l_Lean_mkAppB(
                                                    v___x_3240_,
                                                    v_arg_3103_,
                                                    v_arg_3099_,
                                                );
                                                v___x_3242_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3242_,
                                                    0,
                                                    v___x_3241_,
                                                );
                                                v___x_3243_ =
                                                    crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3243_,
                                                    0,
                                                    v___x_3239_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3243_,
                                                    1,
                                                    v___x_3242_,
                                                );
                                                crate::leanh::lean_ctor_set_uint8(
                                                    v___x_3243_,
                                                    (core::mem::size_of::<
                                                        *mut crate::leanh::LeanObject,
                                                    >(
                                                    ) * 2)
                                                        as u32,
                                                    v___x_3110_,
                                                );
                                                v___x_3244_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3244_,
                                                    0,
                                                    v___x_3243_,
                                                );
                                                if v_isShared_3092_ == 0 {
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3091_,
                                                        0,
                                                        v___x_3244_,
                                                    );
                                                    v___x_3246_ = v___x_3091_;
                                                    state = 26;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3247_ =
                                                        crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3247_,
                                                        0,
                                                        v___x_3244_,
                                                    );
                                                    v___x_3246_ = v_reuseFailAlloc_3247_;
                                                    state = 26;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3104_);
                                            crate::leanh::lean_dec_ref(v_e_2995_);
                                            v___x_3248_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__45), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__45_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__45);
                                            crate::leanh::lean_inc_ref(v_arg_3103_);
                                            v___x_3249_ = l_Lean_mkNot(v_arg_3103_);
                                            crate::leanh::lean_inc_ref(v_arg_3099_);
                                            v___x_3250_ = l_Lean_mkNot(v_arg_3099_);
                                            v___x_3251_ = l_Lean_mkAppB(
                                                v___x_3248_,
                                                v___x_3249_,
                                                v___x_3250_,
                                            );
                                            v___x_3252_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__48), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__48_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__48);
                                            v___x_3253_ = l_Lean_mkAppB(
                                                v___x_3252_,
                                                v_arg_3103_,
                                                v_arg_3099_,
                                            );
                                            v___x_3254_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3254_,
                                                0,
                                                v___x_3253_,
                                            );
                                            v___x_3255_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3255_,
                                                0,
                                                v___x_3251_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3255_,
                                                1,
                                                v___x_3254_,
                                            );
                                            crate::leanh::lean_ctor_set_uint8(
                                                v___x_3255_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 2)
                                                    as u32,
                                                v___x_3108_,
                                            );
                                            v___x_3256_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3256_,
                                                0,
                                                v___x_3255_,
                                            );
                                            if v_isShared_3092_ == 0 {
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3091_,
                                                    0,
                                                    v___x_3256_,
                                                );
                                                v___x_3258_ = v___x_3091_;
                                                state = 27;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3259_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_3259_,
                                                    0,
                                                    v___x_3256_,
                                                );
                                                v___x_3258_ = v_reuseFailAlloc_3259_;
                                                state = 27;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_3104_);
                                        crate::leanh::lean_del_object(v___x_3091_);
                                        crate::leanh::lean_dec_ref(v_e_2995_);
                                        v___x_3260_ =
                                            l_Lean_Meta_Grind_pushNot___redArg___closed__50;
                                        v___x_3261_ = 0;
                                        v___x_3262_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__51), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__51_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51);
                                        crate::leanh::lean_inc_ref(v_arg_3099_);
                                        v___x_3263_ =
                                            l_Lean_Expr_app___override(v_arg_3099_, v___x_3262_);
                                        v___x_3264_ = l_Lean_mkNot(v___x_3263_);
                                        crate::leanh::lean_inc_ref_n(v_arg_3103_, 2);
                                        v___x_3265_ = l_Lean_mkForall(
                                            v___x_3260_,
                                            v___x_3261_,
                                            v_arg_3103_,
                                            v___x_3264_,
                                        );
                                        v___x_3266_ = l_Lean_Meta_getLevel(
                                            v_arg_3103_,
                                            v_a_2996_,
                                            v_a_2997_,
                                            v_a_2998_,
                                            v_a_2999_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_3266_) == 0 {
                                            v_a_3267_ = crate::leanh::lean_ctor_get(v___x_3266_, 0);
                                            v_isSharedCheck_3282_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3266_))
                                                    as u8;
                                            if v_isSharedCheck_3282_ == 0 {
                                                v___x_3269_ = v___x_3266_;
                                                v_isShared_3270_ = v_isSharedCheck_3282_;
                                                state = 28;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3267_);
                                                crate::leanh::lean_dec(v___x_3266_);
                                                v___x_3269_ = crate::leanh::lean_box(0);
                                                v_isShared_3270_ = v_isSharedCheck_3282_;
                                                state = 28;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3265_);
                                            crate::leanh::lean_dec_ref(v_arg_3103_);
                                            crate::leanh::lean_dec_ref(v_arg_3099_);
                                            v_a_3283_ = crate::leanh::lean_ctor_get(v___x_3266_, 0);
                                            v_isSharedCheck_3290_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3266_))
                                                    as u8;
                                            if v_isSharedCheck_3290_ == 0 {
                                                v___x_3285_ = v___x_3266_;
                                                v_isShared_3286_ = v_isSharedCheck_3290_;
                                                state = 30;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3283_);
                                                crate::leanh::lean_dec(v___x_3266_);
                                                v___x_3285_ = crate::leanh::lean_box(0);
                                                v_isShared_3286_ = v_isSharedCheck_3290_;
                                                state = 30;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3100_);
                                crate::leanh::lean_dec_ref(v_e_2995_);
                                v___x_3291_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_pushNot___redArg___closed__56
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_pushNot___redArg___closed__56_once
                                    ),
                                    _init_l_Lean_Meta_Grind_pushNot___redArg___closed__56,
                                );
                                crate::leanh::lean_inc_ref(v_arg_3099_);
                                v___x_3292_ = l_Lean_Expr_app___override(v___x_3291_, v_arg_3099_);
                                v___x_3293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3293_, 0, v___x_3292_);
                                v___x_3294_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_3294_, 0, v_arg_3099_);
                                crate::leanh::lean_ctor_set(v___x_3294_, 1, v___x_3293_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_3294_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                                        as u32,
                                    v___x_3101_,
                                );
                                v___x_3295_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3295_, 0, v___x_3294_);
                                if v_isShared_3092_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3091_, 0, v___x_3295_);
                                    v___x_3297_ = v___x_3091_;
                                    state = 32;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3298_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3298_,
                                        0,
                                        v___x_3295_,
                                    );
                                    v___x_3297_ = v_reuseFailAlloc_3298_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3093_);
                        crate::leanh::lean_dec_ref(v_e_2995_);
                        v___x_3299_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpEq___redArg___closed__9_once
                            ),
                            _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9,
                        );
                        v___x_3300_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__60
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__60_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__60,
                        );
                        v___x_3301_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3301_, 0, v___x_3299_);
                        crate::leanh::lean_ctor_set(v___x_3301_, 1, v___x_3300_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3301_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_3097_,
                        );
                        v___x_3302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3302_, 0, v___x_3301_);
                        if v_isShared_3092_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3091_, 0, v___x_3302_);
                            v___x_3304_ = v___x_3091_;
                            state = 33;
                            continue;
                        } else {
                            v_reuseFailAlloc_3305_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
                            v___x_3304_ = v_reuseFailAlloc_3305_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3093_);
                    crate::leanh::lean_dec_ref(v_e_2995_);
                    v___x_3306_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6_once),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6,
                    );
                    v___x_3307_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__64),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__64_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__64,
                    );
                    v___x_3308_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3308_, 0, v___x_3306_);
                    crate::leanh::lean_ctor_set(v___x_3308_, 1, v___x_3307_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3308_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_3095_,
                    );
                    v___x_3309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3309_, 0, v___x_3308_);
                    if v_isShared_3092_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3091_, 0, v___x_3309_);
                        v___x_3311_ = v___x_3091_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
                        v___x_3311_ = v_reuseFailAlloc_3312_;
                        state = 34;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_3135_;
            }
            13 => {
                v___x_3142_ = l_Lean_Expr_cleanupAnnotations(v_a_3138_);
                v___x_3143_ = l_Lean_Meta_Grind_pushNot___redArg___closed__20;
                v___x_3144_ = l_Lean_Expr_isConstOf(v___x_3142_, v___x_3143_);
                if v___x_3144_ == 0 {
                    v___x_3145_ = l_Lean_Meta_Grind_pushNot___redArg___closed__22;
                    v___x_3146_ = l_Lean_Expr_isConstOf(v___x_3142_, v___x_3145_);
                    crate::leanh::lean_dec_ref(v___x_3142_);
                    if v___x_3146_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_3103_);
                        crate::leanh::lean_dec_ref(v_arg_3099_);
                        v___x_3147_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        if v_isShared_3141_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3140_, 0, v___x_3147_);
                            v___x_3149_ = v___x_3140_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3150_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
                            v___x_3149_ = v_reuseFailAlloc_3150_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___x_3151_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__24
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__24_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24,
                        );
                        crate::leanh::lean_inc_ref(v_arg_3099_);
                        v___x_3152_ = l_Lean_mkIntAdd(v_arg_3099_, v___x_3151_);
                        crate::leanh::lean_inc_ref(v_arg_3103_);
                        v___x_3153_ = l_Lean_mkIntLE(v___x_3152_, v_arg_3103_);
                        v___x_3154_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__27
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__27_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27,
                        );
                        v___x_3155_ = l_Lean_mkAppB(v___x_3154_, v_arg_3103_, v_arg_3099_);
                        v___x_3156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
                        v___x_3157_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3157_, 0, v___x_3153_);
                        crate::leanh::lean_ctor_set(v___x_3157_, 1, v___x_3156_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3157_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_3146_,
                        );
                        v___x_3158_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3158_, 0, v___x_3157_);
                        if v_isShared_3141_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3140_, 0, v___x_3158_);
                            v___x_3160_ = v___x_3140_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_3161_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3158_);
                            v___x_3160_ = v_reuseFailAlloc_3161_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3142_);
                    v___x_3162_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__28),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__28_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28,
                    );
                    crate::leanh::lean_inc_ref(v_arg_3099_);
                    v___x_3163_ = l_Lean_mkNatAdd(v_arg_3099_, v___x_3162_);
                    crate::leanh::lean_inc_ref(v_arg_3103_);
                    v___x_3164_ = l_Lean_mkNatLE(v___x_3163_, v_arg_3103_);
                    v___x_3165_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__30),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__30_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30,
                    );
                    v___x_3166_ = l_Lean_mkAppB(v___x_3165_, v_arg_3103_, v_arg_3099_);
                    v___x_3167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3167_, 0, v___x_3166_);
                    v___x_3168_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3168_, 0, v___x_3164_);
                    crate::leanh::lean_ctor_set(v___x_3168_, 1, v___x_3167_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3168_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_3144_,
                    );
                    v___x_3169_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3169_, 0, v___x_3168_);
                    if v_isShared_3141_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3140_, 0, v___x_3169_);
                        v___x_3171_ = v___x_3140_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
                        v___x_3171_ = v_reuseFailAlloc_3172_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_3149_;
            }
            15 => {
                return v___x_3160_;
            }
            16 => {
                return v___x_3171_;
            }
            17 => {
                if v_isShared_3177_ == 0 {
                    v___x_3179_ = v___x_3176_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
                    v___x_3179_ = v_reuseFailAlloc_3180_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3179_;
            }
            19 => {
                v___x_3188_ = l_Lean_Expr_cleanupAnnotations(v_a_3184_);
                v___x_3189_ = l_Lean_Meta_Grind_simpEq___redArg___closed__30;
                v___x_3190_ = l_Lean_Expr_isConstOf(v___x_3188_, v___x_3189_);
                if v___x_3190_ == 0 {
                    v___x_3191_ = l_Lean_Meta_Grind_simpEq___redArg___closed__21;
                    v___x_3192_ = l_Lean_Expr_isConstOf(v___x_3188_, v___x_3191_);
                    crate::leanh::lean_dec_ref(v___x_3188_);
                    if v___x_3192_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3113_);
                        crate::leanh::lean_dec_ref(v_arg_3112_);
                        crate::leanh::lean_dec_ref(v_arg_3103_);
                        v___x_3193_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        if v_isShared_3187_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3186_, 0, v___x_3193_);
                            v___x_3195_ = v___x_3186_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_3196_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
                            v___x_3195_ = v_reuseFailAlloc_3196_;
                            state = 20;
                            continue;
                        }
                    } else {
                        v___x_3197_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__31
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__31_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__31,
                        );
                        crate::leanh::lean_inc_ref(v_arg_3103_);
                        v___x_3198_ =
                            l_Lean_mkApp3(v___x_3113_, v_arg_3112_, v_arg_3103_, v___x_3197_);
                        v___x_3199_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__34
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__34_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__34,
                        );
                        v___x_3200_ = l_Lean_Expr_app___override(v___x_3199_, v_arg_3103_);
                        v___x_3201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3201_, 0, v___x_3200_);
                        v___x_3202_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3202_, 0, v___x_3198_);
                        crate::leanh::lean_ctor_set(v___x_3202_, 1, v___x_3201_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3202_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_3115_,
                        );
                        v___x_3203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3203_, 0, v___x_3202_);
                        if v_isShared_3187_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3186_, 0, v___x_3203_);
                            v___x_3205_ = v___x_3186_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_3206_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
                            v___x_3205_ = v_reuseFailAlloc_3206_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3188_);
                    v___x_3207_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__22),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpEq___redArg___closed__22_once
                        ),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22,
                    );
                    crate::leanh::lean_inc_ref(v_arg_3103_);
                    v___x_3208_ = l_Lean_mkApp3(v___x_3113_, v_arg_3112_, v_arg_3103_, v___x_3207_);
                    v___x_3209_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__37),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__37_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__37,
                    );
                    v___x_3210_ = l_Lean_Expr_app___override(v___x_3209_, v_arg_3103_);
                    v___x_3211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3211_, 0, v___x_3210_);
                    v___x_3212_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3212_, 0, v___x_3208_);
                    crate::leanh::lean_ctor_set(v___x_3212_, 1, v___x_3211_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3212_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_3115_,
                    );
                    v___x_3213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3213_, 0, v___x_3212_);
                    if v_isShared_3187_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3186_, 0, v___x_3213_);
                        v___x_3215_ = v___x_3186_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_3216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
                        v___x_3215_ = v_reuseFailAlloc_3216_;
                        state = 22;
                        continue;
                    }
                }
            }
            20 => {
                return v___x_3195_;
            }
            21 => {
                return v___x_3205_;
            }
            22 => {
                return v___x_3215_;
            }
            23 => {
                if v_isShared_3221_ == 0 {
                    v___x_3223_ = v___x_3220_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
                    v___x_3223_ = v_reuseFailAlloc_3224_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3223_;
            }
            25 => {
                return v___x_3234_;
            }
            26 => {
                return v___x_3246_;
            }
            27 => {
                return v___x_3258_;
            }
            28 => {
                v___x_3271_ = l_Lean_Meta_Grind_pushNot___redArg___closed__53;
                v___x_3272_ = crate::leanh::lean_box(0);
                v___x_3273_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3273_, 0, v_a_3267_);
                crate::leanh::lean_ctor_set(v___x_3273_, 1, v___x_3272_);
                v___x_3274_ = l_Lean_mkConst(v___x_3271_, v___x_3273_);
                v___x_3275_ = l_Lean_mkAppB(v___x_3274_, v_arg_3103_, v_arg_3099_);
                v___x_3276_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3276_, 0, v___x_3275_);
                v___x_3277_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3277_, 0, v___x_3265_);
                crate::leanh::lean_ctor_set(v___x_3277_, 1, v___x_3276_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3277_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3106_,
                );
                v___x_3278_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3278_, 0, v___x_3277_);
                if v_isShared_3270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3269_, 0, v___x_3278_);
                    v___x_3280_ = v___x_3269_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3281_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
                    v___x_3280_ = v_reuseFailAlloc_3281_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3280_;
            }
            30 => {
                if v_isShared_3286_ == 0 {
                    v___x_3288_ = v___x_3285_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3288_;
            }
            32 => {
                return v___x_3297_;
            }
            33 => {
                return v___x_3304_;
            }
            34 => {
                return v___x_3311_;
            }
            35 => {
                if v_isShared_3317_ == 0 {
                    v___x_3319_ = v___x_3316_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
                    v___x_3319_ = v_reuseFailAlloc_3320_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3319_;
            }
            37 => {
                if v_isShared_3326_ == 0 {
                    v___x_3328_ = v___x_3325_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
                    v___x_3328_ = v_reuseFailAlloc_3329_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_pushNot___redArg___boxed(
    mut v_e_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3337_ =
        l_Lean_Meta_Grind_pushNot___redArg(v_e_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
    crate::leanh::lean_dec(v_a_3335_);
    crate::leanh::lean_dec_ref(v_a_3334_);
    crate::leanh::lean_dec(v_a_3333_);
    crate::leanh::lean_dec_ref(v_a_3332_);
    return v_res_3337_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNot(
    mut v_e_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3347_ =
        l_Lean_Meta_Grind_pushNot___redArg(v_e_3338_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
    return v___x_3347_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNot___boxed(
    mut v_e_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
    mut v_a_3350_: *mut crate::leanh::LeanObject,
    mut v_a_3351_: *mut crate::leanh::LeanObject,
    mut v_a_3352_: *mut crate::leanh::LeanObject,
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l_Lean_Meta_Grind_pushNot(
        v_e_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_,
    );
    crate::leanh::lean_dec(v_a_3355_);
    crate::leanh::lean_dec_ref(v_a_3354_);
    crate::leanh::lean_dec(v_a_3353_);
    crate::leanh::lean_dec_ref(v_a_3352_);
    crate::leanh::lean_dec(v_a_3351_);
    crate::leanh::lean_dec_ref(v_a_3350_);
    crate::leanh::lean_dec(v_a_3349_);
    return v_res_3357_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3374_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_;
    v___x_3375_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_;
    v___x_3376_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_pushNot___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3377_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3374_, v___x_3375_, v___x_3376_);
    return v___x_3377_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10____boxed(
    mut v_a_3378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3379_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_();
    return v_res_3379_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3385_ = crate::leanh::lean_box(0);
    v___x_3386_ = l_Lean_Meta_Grind_simpOr___redArg___closed__1;
    v___x_3387_ = l_Lean_mkConst(v___x_3386_, v___x_3385_);
    return v___x_3387_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = crate::leanh::lean_box(0);
    v___x_3394_ = l_Lean_Meta_Grind_simpOr___redArg___closed__4;
    v___x_3395_ = l_Lean_mkConst(v___x_3394_, v___x_3393_);
    return v___x_3395_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = crate::leanh::lean_box(0);
    v___x_3400_ = l_Lean_Meta_Grind_simpOr___redArg___closed__7;
    v___x_3401_ = l_Lean_mkConst(v___x_3400_, v___x_3399_);
    return v___x_3401_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3405_ = crate::leanh::lean_box(0);
    v___x_3406_ = l_Lean_Meta_Grind_simpOr___redArg___closed__10;
    v___x_3407_ = l_Lean_mkConst(v___x_3406_, v___x_3405_);
    return v___x_3407_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3413_ = crate::leanh::lean_box(0);
    v___x_3414_ = l_Lean_Meta_Grind_simpOr___redArg___closed__13;
    v___x_3415_ = l_Lean_mkConst(v___x_3414_, v___x_3413_);
    return v___x_3415_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3419_ = crate::leanh::lean_box(0);
    v___x_3420_ = l_Lean_Meta_Grind_simpOr___redArg___closed__16;
    v___x_3421_ = l_Lean_mkConst(v___x_3420_, v___x_3419_);
    return v___x_3421_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3425_ = crate::leanh::lean_box(0);
    v___x_3426_ = l_Lean_Meta_Grind_simpOr___redArg___closed__19;
    v___x_3427_ = l_Lean_mkConst(v___x_3426_, v___x_3425_);
    return v___x_3427_;
}
pub unsafe fn l_Lean_Meta_Grind_simpOr___redArg(
    mut v_e_3428_: *mut crate::leanh::LeanObject,
    mut v_a_3429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: u8 = 0;
    let mut v_arg_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v_arg_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3456_: u8 = 0;
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: u8 = 0;
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: u8 = 0;
    let mut v_arg_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v_arg_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: u8 = 0;
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_a_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u8 = 0;
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: u8 = 0;
    let mut v_arg_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: u8 = 0;
    let mut v_arg_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: u8 = 0;
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_a_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut v_a_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3434_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3428_, v_a_3429_);
                if crate::leanh::lean_obj_tag(v___x_3434_) == 0 {
                    v_a_3435_ = crate::leanh::lean_ctor_get(v___x_3434_, 0);
                    v_isSharedCheck_3581_ = (!crate::leanh::lean_is_exclusive(v___x_3434_)) as u8;
                    if v_isSharedCheck_3581_ == 0 {
                        v___x_3437_ = v___x_3434_;
                        v_isShared_3438_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3435_);
                        crate::leanh::lean_dec(v___x_3434_);
                        v___x_3437_ = crate::leanh::lean_box(0);
                        v_isShared_3438_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3582_ = crate::leanh::lean_ctor_get(v___x_3434_, 0);
                    v_isSharedCheck_3589_ = (!crate::leanh::lean_is_exclusive(v___x_3434_)) as u8;
                    if v_isSharedCheck_3589_ == 0 {
                        v___x_3584_ = v___x_3434_;
                        v_isShared_3585_ = v_isSharedCheck_3589_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3582_);
                        crate::leanh::lean_dec(v___x_3434_);
                        v___x_3584_ = crate::leanh::lean_box(0);
                        v_isShared_3585_ = v_isSharedCheck_3589_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3432_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                v___x_3433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3433_, 0, v___x_3432_);
                return v___x_3433_;
            }
            2 => {
                v___x_3444_ = l_Lean_Expr_cleanupAnnotations(v_a_3435_);
                v___x_3445_ = l_Lean_Expr_isApp(v___x_3444_);
                if v___x_3445_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3444_);
                    state = 3;
                    continue;
                } else {
                    v_arg_3446_ = crate::leanh::lean_ctor_get(v___x_3444_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3446_);
                    v___x_3447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3444_);
                    v___x_3448_ = l_Lean_Expr_isApp(v___x_3447_);
                    if v___x_3448_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3447_);
                        crate::leanh::lean_dec_ref(v_arg_3446_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_3449_ = crate::leanh::lean_ctor_get(v___x_3447_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3449_);
                        v___x_3526_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3447_);
                        v___x_3527_ = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
                        v___x_3528_ = l_Lean_Expr_isConstOf(v___x_3526_, v___x_3527_);
                        crate::leanh::lean_dec_ref(v___x_3526_);
                        if v___x_3528_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_3449_);
                            crate::leanh::lean_dec_ref(v_arg_3446_);
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_3437_);
                            crate::leanh::lean_inc_ref(v_arg_3449_);
                            v___x_3529_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                v_arg_3449_,
                                v_a_3429_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3529_) == 0 {
                                v_a_3530_ = crate::leanh::lean_ctor_get(v___x_3529_, 0);
                                v_isSharedCheck_3572_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3529_)) as u8;
                                if v_isSharedCheck_3572_ == 0 {
                                    v___x_3532_ = v___x_3529_;
                                    v_isShared_3533_ = v_isSharedCheck_3572_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3530_);
                                    crate::leanh::lean_dec(v___x_3529_);
                                    v___x_3532_ = crate::leanh::lean_box(0);
                                    v_isShared_3533_ = v_isSharedCheck_3572_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_arg_3449_);
                                crate::leanh::lean_dec_ref(v_arg_3446_);
                                v_a_3573_ = crate::leanh::lean_ctor_get(v___x_3529_, 0);
                                v_isSharedCheck_3580_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3529_)) as u8;
                                if v_isSharedCheck_3580_ == 0 {
                                    v___x_3575_ = v___x_3529_;
                                    v_isShared_3576_ = v_isSharedCheck_3580_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3573_);
                                    crate::leanh::lean_dec(v___x_3529_);
                                    v___x_3575_ = crate::leanh::lean_box(0);
                                    v_isShared_3576_ = v_isSharedCheck_3580_;
                                    state = 19;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_3440_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_3438_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3437_, 0, v___x_3440_);
                    v___x_3442_ = v___x_3437_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
                    v___x_3442_ = v_reuseFailAlloc_3443_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3442_;
            }
            5 => {
                crate::leanh::lean_inc_ref(v_arg_3446_);
                v___x_3452_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3446_, v___y_3451_);
                if crate::leanh::lean_obj_tag(v___x_3452_) == 0 {
                    v_a_3453_ = crate::leanh::lean_ctor_get(v___x_3452_, 0);
                    v_isSharedCheck_3517_ = (!crate::leanh::lean_is_exclusive(v___x_3452_)) as u8;
                    if v_isSharedCheck_3517_ == 0 {
                        v___x_3455_ = v___x_3452_;
                        v_isShared_3456_ = v_isSharedCheck_3517_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3453_);
                        crate::leanh::lean_dec(v___x_3452_);
                        v___x_3455_ = crate::leanh::lean_box(0);
                        v_isShared_3456_ = v_isSharedCheck_3517_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_3449_);
                    crate::leanh::lean_dec_ref(v_arg_3446_);
                    v_a_3518_ = crate::leanh::lean_ctor_get(v___x_3452_, 0);
                    v_isSharedCheck_3525_ = (!crate::leanh::lean_is_exclusive(v___x_3452_)) as u8;
                    if v_isSharedCheck_3525_ == 0 {
                        v___x_3520_ = v___x_3452_;
                        v_isShared_3521_ = v_isSharedCheck_3525_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3518_);
                        crate::leanh::lean_dec(v___x_3452_);
                        v___x_3520_ = crate::leanh::lean_box(0);
                        v_isShared_3521_ = v_isSharedCheck_3525_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3457_ = l_Lean_Expr_cleanupAnnotations(v_a_3453_);
                v___x_3458_ = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
                v___x_3459_ = l_Lean_Expr_isConstOf(v___x_3457_, v___x_3458_);
                if v___x_3459_ == 0 {
                    v___x_3460_ = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
                    v___x_3461_ = l_Lean_Expr_isConstOf(v___x_3457_, v___x_3460_);
                    if v___x_3461_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_3446_);
                        v___x_3462_ = l_Lean_Expr_isApp(v___x_3457_);
                        if v___x_3462_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3457_);
                            crate::leanh::lean_del_object(v___x_3455_);
                            crate::leanh::lean_dec_ref(v_arg_3449_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_3463_ = crate::leanh::lean_ctor_get(v___x_3457_, 1);
                            crate::leanh::lean_inc_ref(v_arg_3463_);
                            v___x_3464_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3457_);
                            v___x_3465_ = l_Lean_Expr_isApp(v___x_3464_);
                            if v___x_3465_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3464_);
                                crate::leanh::lean_dec_ref(v_arg_3463_);
                                crate::leanh::lean_del_object(v___x_3455_);
                                crate::leanh::lean_dec_ref(v_arg_3449_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_3466_ = crate::leanh::lean_ctor_get(v___x_3464_, 1);
                                crate::leanh::lean_inc_ref(v_arg_3466_);
                                v___x_3467_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3464_);
                                v___x_3468_ = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
                                v___x_3469_ = l_Lean_Expr_isConstOf(v___x_3467_, v___x_3468_);
                                crate::leanh::lean_dec_ref(v___x_3467_);
                                if v___x_3469_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_3466_);
                                    crate::leanh::lean_dec_ref(v_arg_3463_);
                                    crate::leanh::lean_del_object(v___x_3455_);
                                    crate::leanh::lean_dec_ref(v_arg_3449_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3470_ = l_Lean_Expr_isForall(v_arg_3449_);
                                    if v___x_3470_ == 0 {
                                        v___x_3471_ = l_Lean_Expr_isForall(v_arg_3466_);
                                        if v___x_3471_ == 0 {
                                            v___x_3472_ = l_Lean_Expr_isForall(v_arg_3463_);
                                            if v___x_3472_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_3466_);
                                                crate::leanh::lean_dec_ref(v_arg_3463_);
                                                crate::leanh::lean_dec_ref(v_arg_3449_);
                                                v___x_3473_ =
                                                    l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                if v_isShared_3456_ == 0 {
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3455_,
                                                        0,
                                                        v___x_3473_,
                                                    );
                                                    v___x_3475_ = v___x_3455_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3476_ =
                                                        crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3476_,
                                                        0,
                                                        v___x_3473_,
                                                    );
                                                    v___x_3475_ = v_reuseFailAlloc_3476_;
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_inc_ref(v_arg_3449_);
                                                crate::leanh::lean_inc_ref(v_arg_3466_);
                                                v___x_3477_ = l_Lean_mkOr(v_arg_3466_, v_arg_3449_);
                                                crate::leanh::lean_inc_ref(v_arg_3463_);
                                                v___x_3478_ = l_Lean_mkOr(v_arg_3463_, v___x_3477_);
                                                v___x_3479_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__2_once), _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2);
                                                v___x_3480_ = l_Lean_mkApp3(
                                                    v___x_3479_,
                                                    v_arg_3449_,
                                                    v_arg_3466_,
                                                    v_arg_3463_,
                                                );
                                                v___x_3481_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3481_,
                                                    0,
                                                    v___x_3480_,
                                                );
                                                v___x_3482_ =
                                                    crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3482_,
                                                    0,
                                                    v___x_3478_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3482_,
                                                    1,
                                                    v___x_3481_,
                                                );
                                                crate::leanh::lean_ctor_set_uint8(
                                                    v___x_3482_,
                                                    (core::mem::size_of::<
                                                        *mut crate::leanh::LeanObject,
                                                    >(
                                                    ) * 2)
                                                        as u32,
                                                    v___x_3469_,
                                                );
                                                v___x_3483_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3483_,
                                                    0,
                                                    v___x_3482_,
                                                );
                                                if v_isShared_3456_ == 0 {
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3455_,
                                                        0,
                                                        v___x_3483_,
                                                    );
                                                    v___x_3485_ = v___x_3455_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3486_ =
                                                        crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3486_,
                                                        0,
                                                        v___x_3483_,
                                                    );
                                                    v___x_3485_ = v_reuseFailAlloc_3486_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_inc_ref(v_arg_3463_);
                                            crate::leanh::lean_inc_ref(v_arg_3449_);
                                            v___x_3487_ = l_Lean_mkOr(v_arg_3449_, v_arg_3463_);
                                            crate::leanh::lean_inc_ref(v_arg_3466_);
                                            v___x_3488_ = l_Lean_mkOr(v_arg_3466_, v___x_3487_);
                                            v___x_3489_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__5_once), _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5);
                                            v___x_3490_ = l_Lean_mkApp3(
                                                v___x_3489_,
                                                v_arg_3449_,
                                                v_arg_3466_,
                                                v_arg_3463_,
                                            );
                                            v___x_3491_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3491_,
                                                0,
                                                v___x_3490_,
                                            );
                                            v___x_3492_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3492_,
                                                0,
                                                v___x_3488_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3492_,
                                                1,
                                                v___x_3491_,
                                            );
                                            crate::leanh::lean_ctor_set_uint8(
                                                v___x_3492_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 2)
                                                    as u32,
                                                v___x_3469_,
                                            );
                                            v___x_3493_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3493_,
                                                0,
                                                v___x_3492_,
                                            );
                                            if v_isShared_3456_ == 0 {
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3455_,
                                                    0,
                                                    v___x_3493_,
                                                );
                                                v___x_3495_ = v___x_3455_;
                                                state = 9;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3496_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_3496_,
                                                    0,
                                                    v___x_3493_,
                                                );
                                                v___x_3495_ = v_reuseFailAlloc_3496_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_3466_);
                                        crate::leanh::lean_dec_ref(v_arg_3463_);
                                        crate::leanh::lean_dec_ref(v_arg_3449_);
                                        v___x_3497_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                        if v_isShared_3456_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_3455_,
                                                0,
                                                v___x_3497_,
                                            );
                                            v___x_3499_ = v___x_3455_;
                                            state = 10;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3500_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3500_,
                                                0,
                                                v___x_3497_,
                                            );
                                            v___x_3499_ = v_reuseFailAlloc_3500_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3457_);
                        v___x_3501_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__8),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpOr___redArg___closed__8_once
                            ),
                            _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8,
                        );
                        v___x_3502_ = l_Lean_Expr_app___override(v___x_3501_, v_arg_3449_);
                        v___x_3503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3503_, 0, v___x_3502_);
                        v___x_3504_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3504_, 0, v_arg_3446_);
                        crate::leanh::lean_ctor_set(v___x_3504_, 1, v___x_3503_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3504_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_3461_,
                        );
                        v___x_3505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3505_, 0, v___x_3504_);
                        if v_isShared_3456_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3455_, 0, v___x_3505_);
                            v___x_3507_ = v___x_3455_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3508_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
                            v___x_3507_ = v_reuseFailAlloc_3508_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3457_);
                    crate::leanh::lean_dec_ref(v_arg_3446_);
                    v___x_3509_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__11),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpOr___redArg___closed__11_once
                        ),
                        _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11,
                    );
                    crate::leanh::lean_inc_ref(v_arg_3449_);
                    v___x_3510_ = l_Lean_Expr_app___override(v___x_3509_, v_arg_3449_);
                    v___x_3511_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3511_, 0, v___x_3510_);
                    v___x_3512_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3512_, 0, v_arg_3449_);
                    crate::leanh::lean_ctor_set(v___x_3512_, 1, v___x_3511_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3512_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_3459_,
                    );
                    v___x_3513_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3512_);
                    if v_isShared_3456_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3455_, 0, v___x_3513_);
                        v___x_3515_ = v___x_3455_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
                        v___x_3515_ = v_reuseFailAlloc_3516_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3475_;
            }
            8 => {
                return v___x_3485_;
            }
            9 => {
                return v___x_3495_;
            }
            10 => {
                return v___x_3499_;
            }
            11 => {
                return v___x_3507_;
            }
            12 => {
                return v___x_3515_;
            }
            13 => {
                if v_isShared_3521_ == 0 {
                    v___x_3523_ = v___x_3520_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
                    v___x_3523_ = v_reuseFailAlloc_3524_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3523_;
            }
            15 => {
                v___x_3534_ = l_Lean_Expr_cleanupAnnotations(v_a_3530_);
                v___x_3535_ = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
                v___x_3536_ = l_Lean_Expr_isConstOf(v___x_3534_, v___x_3535_);
                if v___x_3536_ == 0 {
                    v___x_3537_ = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
                    v___x_3538_ = l_Lean_Expr_isConstOf(v___x_3534_, v___x_3537_);
                    if v___x_3538_ == 0 {
                        v___x_3539_ = l_Lean_Expr_isApp(v___x_3534_);
                        if v___x_3539_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3534_);
                            crate::leanh::lean_del_object(v___x_3532_);
                            v___y_3451_ = v_a_3429_;
                            state = 5;
                            continue;
                        } else {
                            v_arg_3540_ = crate::leanh::lean_ctor_get(v___x_3534_, 1);
                            crate::leanh::lean_inc_ref(v_arg_3540_);
                            v___x_3541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3534_);
                            v___x_3542_ = l_Lean_Expr_isApp(v___x_3541_);
                            if v___x_3542_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3541_);
                                crate::leanh::lean_dec_ref(v_arg_3540_);
                                crate::leanh::lean_del_object(v___x_3532_);
                                v___y_3451_ = v_a_3429_;
                                state = 5;
                                continue;
                            } else {
                                v_arg_3543_ = crate::leanh::lean_ctor_get(v___x_3541_, 1);
                                crate::leanh::lean_inc_ref(v_arg_3543_);
                                v___x_3544_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3541_);
                                v___x_3545_ = l_Lean_Expr_isConstOf(v___x_3544_, v___x_3527_);
                                crate::leanh::lean_dec_ref(v___x_3544_);
                                if v___x_3545_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_3543_);
                                    crate::leanh::lean_dec_ref(v_arg_3540_);
                                    crate::leanh::lean_del_object(v___x_3532_);
                                    v___y_3451_ = v_a_3429_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_3449_);
                                    crate::leanh::lean_inc_ref(v_arg_3446_);
                                    crate::leanh::lean_inc_ref(v_arg_3540_);
                                    v___x_3546_ = l_Lean_mkOr(v_arg_3540_, v_arg_3446_);
                                    crate::leanh::lean_inc_ref(v_arg_3543_);
                                    v___x_3547_ = l_Lean_mkOr(v_arg_3543_, v___x_3546_);
                                    v___x_3548_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_simpOr___redArg___closed__14
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_simpOr___redArg___closed__14_once
                                        ),
                                        _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14,
                                    );
                                    v___x_3549_ = l_Lean_mkApp3(
                                        v___x_3548_,
                                        v_arg_3543_,
                                        v_arg_3540_,
                                        v_arg_3446_,
                                    );
                                    v___x_3550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3550_, 0, v___x_3549_);
                                    v___x_3551_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3551_, 0, v___x_3547_);
                                    crate::leanh::lean_ctor_set(v___x_3551_, 1, v___x_3550_);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_3551_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                                            as u32,
                                        v___x_3545_,
                                    );
                                    v___x_3552_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3552_, 0, v___x_3551_);
                                    if v_isShared_3533_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3532_, 0, v___x_3552_);
                                        v___x_3554_ = v___x_3532_;
                                        state = 16;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3555_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3555_,
                                            0,
                                            v___x_3552_,
                                        );
                                        v___x_3554_ = v_reuseFailAlloc_3555_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3534_);
                        v___x_3556_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__17),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpOr___redArg___closed__17_once
                            ),
                            _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17,
                        );
                        v___x_3557_ = l_Lean_Expr_app___override(v___x_3556_, v_arg_3446_);
                        v___x_3558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3558_, 0, v___x_3557_);
                        v___x_3559_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3559_, 0, v_arg_3449_);
                        crate::leanh::lean_ctor_set(v___x_3559_, 1, v___x_3558_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3559_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_3538_,
                        );
                        v___x_3560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3560_, 0, v___x_3559_);
                        if v_isShared_3533_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3532_, 0, v___x_3560_);
                            v___x_3562_ = v___x_3532_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_3563_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
                            v___x_3562_ = v_reuseFailAlloc_3563_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3534_);
                    crate::leanh::lean_dec_ref(v_arg_3449_);
                    v___x_3564_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__20),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpOr___redArg___closed__20_once
                        ),
                        _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20,
                    );
                    crate::leanh::lean_inc_ref(v_arg_3446_);
                    v___x_3565_ = l_Lean_Expr_app___override(v___x_3564_, v_arg_3446_);
                    v___x_3566_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3566_, 0, v___x_3565_);
                    v___x_3567_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3567_, 0, v_arg_3446_);
                    crate::leanh::lean_ctor_set(v___x_3567_, 1, v___x_3566_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3567_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_3536_,
                    );
                    v___x_3568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3568_, 0, v___x_3567_);
                    if v_isShared_3533_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3532_, 0, v___x_3568_);
                        v___x_3570_ = v___x_3532_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
                        v___x_3570_ = v_reuseFailAlloc_3571_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_3554_;
            }
            17 => {
                return v___x_3562_;
            }
            18 => {
                return v___x_3570_;
            }
            19 => {
                if v_isShared_3576_ == 0 {
                    v___x_3578_ = v___x_3575_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
                    v___x_3578_ = v_reuseFailAlloc_3579_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3578_;
            }
            21 => {
                if v_isShared_3585_ == 0 {
                    v___x_3587_ = v___x_3584_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
                    v___x_3587_ = v_reuseFailAlloc_3588_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_simpOr___redArg___boxed(
    mut v_e_3590_: *mut crate::leanh::LeanObject,
    mut v_a_3591_: *mut crate::leanh::LeanObject,
    mut v_a_3592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3593_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_3590_, v_a_3591_);
    crate::leanh::lean_dec(v_a_3591_);
    return v_res_3593_;
}
pub unsafe fn l_Lean_Meta_Grind_simpOr(
    mut v_e_3594_: *mut crate::leanh::LeanObject,
    mut v_a_3595_: *mut crate::leanh::LeanObject,
    mut v_a_3596_: *mut crate::leanh::LeanObject,
    mut v_a_3597_: *mut crate::leanh::LeanObject,
    mut v_a_3598_: *mut crate::leanh::LeanObject,
    mut v_a_3599_: *mut crate::leanh::LeanObject,
    mut v_a_3600_: *mut crate::leanh::LeanObject,
    mut v_a_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_3594_, v_a_3599_);
    return v___x_3603_;
}
pub unsafe fn l_Lean_Meta_Grind_simpOr___boxed(
    mut v_e_3604_: *mut crate::leanh::LeanObject,
    mut v_a_3605_: *mut crate::leanh::LeanObject,
    mut v_a_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
    mut v_a_3608_: *mut crate::leanh::LeanObject,
    mut v_a_3609_: *mut crate::leanh::LeanObject,
    mut v_a_3610_: *mut crate::leanh::LeanObject,
    mut v_a_3611_: *mut crate::leanh::LeanObject,
    mut v_a_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_Meta_Grind_simpOr(
        v_e_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_,
    );
    crate::leanh::lean_dec(v_a_3611_);
    crate::leanh::lean_dec_ref(v_a_3610_);
    crate::leanh::lean_dec(v_a_3609_);
    crate::leanh::lean_dec_ref(v_a_3608_);
    crate::leanh::lean_dec(v_a_3607_);
    crate::leanh::lean_dec_ref(v_a_3606_);
    crate::leanh::lean_dec(v_a_3605_);
    return v_res_3613_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3631_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_;
    v___x_3632_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_;
    v___x_3633_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_simpOr___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3634_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3631_, v___x_3632_, v___x_3633_);
    return v___x_3634_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11____boxed(
    mut v_a_3635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3636_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_();
    return v_res_3636_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0() -> u64 {
    let mut v___x_3637_: u8 = 0;
    let mut v___x_3638_: u64 = 0;
    v___x_3637_ = 1;
    v___x_3638_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3637_);
    return v___x_3638_;
}
pub unsafe fn l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(
    mut v___x_3639_: u8,
    mut v___x_3640_: u8,
    mut v_h_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
    mut v___y_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
    mut v___y_3648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3666_: u8 = 0;
    let mut v_ctxApprox_3667_: u8 = 0;
    let mut v_quasiPatternApprox_3668_: u8 = 0;
    let mut v_constApprox_3669_: u8 = 0;
    let mut v_isDefEqStuckEx_3670_: u8 = 0;
    let mut v_unificationHints_3671_: u8 = 0;
    let mut v_proofIrrelevance_3672_: u8 = 0;
    let mut v_assignSyntheticOpaque_3673_: u8 = 0;
    let mut v_offsetCnstrs_3674_: u8 = 0;
    let mut v_etaStruct_3675_: u8 = 0;
    let mut v_univApprox_3676_: u8 = 0;
    let mut v_iota_3677_: u8 = 0;
    let mut v_beta_3678_: u8 = 0;
    let mut v_proj_3679_: u8 = 0;
    let mut v_zeta_3680_: u8 = 0;
    let mut v_zetaDelta_3681_: u8 = 0;
    let mut v_zetaUnused_3682_: u8 = 0;
    let mut v_zetaHave_3683_: u8 = 0;
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v_trackZetaDelta_3687_: u8 = 0;
    let mut v_zetaDeltaSet_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3694_: u8 = 0;
    let mut v_inTypeClassResolution_3695_: u8 = 0;
    let mut v_cacheInferType_3696_: u8 = 0;
    let mut v___x_3697_: u8 = 0;
    let mut v_config_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: u64 = 0;
    let mut v___x_3701_: u64 = 0;
    let mut v___x_3702_: u64 = 0;
    let mut v___x_3703_: u64 = 0;
    let mut v___x_3704_: u64 = 0;
    let mut v_key_3705_: u64 = 0;
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3718_: u8 = 0;
    let mut v_reuseFailAlloc_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_a_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v_a_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3732_: u8 = 0;
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3650_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__9_once),
                    _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9,
                );
                crate::leanh::lean_inc_ref(v_h_3641_);
                v___x_3657_ = l_Lean_Meta_mkNoConfusion(
                    v___x_3650_,
                    v_h_3641_,
                    v___y_3645_,
                    v___y_3646_,
                    v___y_3647_,
                    v___y_3648_,
                );
                if crate::leanh::lean_obj_tag(v___x_3657_) == 0 {
                    v_a_3658_ = crate::leanh::lean_ctor_get(v___x_3657_, 0);
                    crate::leanh::lean_inc(v_a_3658_);
                    crate::leanh::lean_dec_ref_known(v___x_3657_, 1);
                    v___x_3659_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3660_ = lean_mk_empty_array_with_capacity(v___x_3659_);
                    v___x_3661_ = lean_array_push(v___x_3660_, v_h_3641_);
                    v___x_3662_ = 1;
                    v___x_3663_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_3661_,
                        v_a_3658_,
                        v___x_3639_,
                        v___x_3640_,
                        v___x_3639_,
                        v___x_3640_,
                        v___x_3662_,
                        v___y_3645_,
                        v___y_3646_,
                        v___y_3647_,
                        v___y_3648_,
                    );
                    crate::leanh::lean_dec_ref(v___x_3661_);
                    if crate::leanh::lean_obj_tag(v___x_3663_) == 0 {
                        v_a_3664_ = crate::leanh::lean_ctor_get(v___x_3663_, 0);
                        crate::leanh::lean_inc(v_a_3664_);
                        crate::leanh::lean_dec_ref_known(v___x_3663_, 1);
                        v___x_3665_ = l_Lean_Meta_Context_config(v___y_3645_);
                        v_foApprox_3666_ = crate::leanh::lean_ctor_get_uint8(v___x_3665_, 0 as u32);
                        v_ctxApprox_3667_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 1 as u32);
                        v_quasiPatternApprox_3668_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 2 as u32);
                        v_constApprox_3669_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 3 as u32);
                        v_isDefEqStuckEx_3670_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 4 as u32);
                        v_unificationHints_3671_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 5 as u32);
                        v_proofIrrelevance_3672_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 6 as u32);
                        v_assignSyntheticOpaque_3673_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 7 as u32);
                        v_offsetCnstrs_3674_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 8 as u32);
                        v_etaStruct_3675_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 10 as u32);
                        v_univApprox_3676_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 11 as u32);
                        v_iota_3677_ = crate::leanh::lean_ctor_get_uint8(v___x_3665_, 12 as u32);
                        v_beta_3678_ = crate::leanh::lean_ctor_get_uint8(v___x_3665_, 13 as u32);
                        v_proj_3679_ = crate::leanh::lean_ctor_get_uint8(v___x_3665_, 14 as u32);
                        v_zeta_3680_ = crate::leanh::lean_ctor_get_uint8(v___x_3665_, 15 as u32);
                        v_zetaDelta_3681_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 16 as u32);
                        v_zetaUnused_3682_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 17 as u32);
                        v_zetaHave_3683_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3665_, 18 as u32);
                        v_isSharedCheck_3720_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3665_)) as u8;
                        if v_isSharedCheck_3720_ == 0 {
                            v___x_3685_ = v___x_3665_;
                            v_isShared_3686_ = v_isSharedCheck_3720_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3665_);
                            v___x_3685_ = crate::leanh::lean_box(0);
                            v_isShared_3686_ = v_isSharedCheck_3720_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3721_ = crate::leanh::lean_ctor_get(v___x_3663_, 0);
                        v_isSharedCheck_3728_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3663_)) as u8;
                        if v_isSharedCheck_3728_ == 0 {
                            v___x_3723_ = v___x_3663_;
                            v_isShared_3724_ = v_isSharedCheck_3728_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3721_);
                            crate::leanh::lean_dec(v___x_3663_);
                            v___x_3723_ = crate::leanh::lean_box(0);
                            v_isShared_3724_ = v_isSharedCheck_3728_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_3641_);
                    v_a_3729_ = crate::leanh::lean_ctor_get(v___x_3657_, 0);
                    v_isSharedCheck_3736_ = (!crate::leanh::lean_is_exclusive(v___x_3657_)) as u8;
                    if v_isSharedCheck_3736_ == 0 {
                        v___x_3731_ = v___x_3657_;
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3729_);
                        crate::leanh::lean_dec(v___x_3657_);
                        v___x_3731_ = crate::leanh::lean_box(0);
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3653_, 0, v_a_3652_);
                v___x_3654_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3654_, 0, v___x_3650_);
                crate::leanh::lean_ctor_set(v___x_3654_, 1, v___x_3653_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3654_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3640_,
                );
                v___x_3655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3655_, 0, v___x_3654_);
                v___x_3656_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3656_, 0, v___x_3655_);
                return v___x_3656_;
            }
            2 => {
                v_trackZetaDelta_3687_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3688_ = crate::leanh::lean_ctor_get(v___y_3645_, 1);
                v_lctx_3689_ = crate::leanh::lean_ctor_get(v___y_3645_, 2);
                v_localInstances_3690_ = crate::leanh::lean_ctor_get(v___y_3645_, 3);
                v_defEqCtx_x3f_3691_ = crate::leanh::lean_ctor_get(v___y_3645_, 4);
                v_synthPendingDepth_3692_ = crate::leanh::lean_ctor_get(v___y_3645_, 5);
                v_canUnfold_x3f_3693_ = crate::leanh::lean_ctor_get(v___y_3645_, 6);
                v_univApprox_3694_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3695_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3696_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3697_ = 1;
                if v_isShared_3686_ == 0 {
                    v_config_3699_ = v___x_3685_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        0 as u32,
                        v_foApprox_3666_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        1 as u32,
                        v_ctxApprox_3667_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        2 as u32,
                        v_quasiPatternApprox_3668_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        3 as u32,
                        v_constApprox_3669_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        4 as u32,
                        v_isDefEqStuckEx_3670_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        5 as u32,
                        v_unificationHints_3671_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        6 as u32,
                        v_proofIrrelevance_3672_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        7 as u32,
                        v_assignSyntheticOpaque_3673_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        8 as u32,
                        v_offsetCnstrs_3674_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        10 as u32,
                        v_etaStruct_3675_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        11 as u32,
                        v_univApprox_3676_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        12 as u32,
                        v_iota_3677_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        13 as u32,
                        v_beta_3678_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        14 as u32,
                        v_proj_3679_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        15 as u32,
                        v_zeta_3680_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        16 as u32,
                        v_zetaDelta_3681_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        17 as u32,
                        v_zetaUnused_3682_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        18 as u32,
                        v_zetaHave_3683_,
                    );
                    v_config_3699_ = v_reuseFailAlloc_3719_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(v_config_3699_, 9 as u32, v___x_3697_);
                v___x_3700_ = l_Lean_Meta_Context_configKey(v___y_3645_);
                v___x_3701_ = 3u64;
                v___x_3702_ = lean_uint64_shift_right(v___x_3700_, v___x_3701_);
                v___x_3703_ = lean_uint64_shift_left(v___x_3702_, v___x_3701_);
                v___x_3704_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0_once
                    ),
                    _init_l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0,
                );
                v_key_3705_ = lean_uint64_lor(v___x_3703_, v___x_3704_);
                v___x_3706_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_3706_, 0, v_config_3699_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_3706_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_3705_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_3693_);
                crate::leanh::lean_inc(v_synthPendingDepth_3692_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_3691_);
                crate::leanh::lean_inc_ref(v_localInstances_3690_);
                crate::leanh::lean_inc_ref(v_lctx_3689_);
                crate::leanh::lean_inc(v_zetaDeltaSet_3688_);
                v___x_3707_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_3707_, 0, v___x_3706_);
                crate::leanh::lean_ctor_set(v___x_3707_, 1, v_zetaDeltaSet_3688_);
                crate::leanh::lean_ctor_set(v___x_3707_, 2, v_lctx_3689_);
                crate::leanh::lean_ctor_set(v___x_3707_, 3, v_localInstances_3690_);
                crate::leanh::lean_ctor_set(v___x_3707_, 4, v_defEqCtx_x3f_3691_);
                crate::leanh::lean_ctor_set(v___x_3707_, 5, v_synthPendingDepth_3692_);
                crate::leanh::lean_ctor_set(v___x_3707_, 6, v_canUnfold_x3f_3693_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3687_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3694_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3695_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3696_,
                );
                v___x_3708_ = l_Lean_Meta_mkEqFalse_x27(
                    v_a_3664_,
                    v___x_3707_,
                    v___y_3646_,
                    v___y_3647_,
                    v___y_3648_,
                );
                crate::leanh::lean_dec_ref_known(v___x_3707_, 7);
                if crate::leanh::lean_obj_tag(v___x_3708_) == 0 {
                    v_a_3709_ = crate::leanh::lean_ctor_get(v___x_3708_, 0);
                    crate::leanh::lean_inc(v_a_3709_);
                    crate::leanh::lean_dec_ref_known(v___x_3708_, 1);
                    v_a_3652_ = v_a_3709_;
                    state = 1;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3708_) == 0 {
                        v_a_3710_ = crate::leanh::lean_ctor_get(v___x_3708_, 0);
                        crate::leanh::lean_inc(v_a_3710_);
                        crate::leanh::lean_dec_ref_known(v___x_3708_, 1);
                        v_a_3652_ = v_a_3710_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3711_ = crate::leanh::lean_ctor_get(v___x_3708_, 0);
                        v_isSharedCheck_3718_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3708_)) as u8;
                        if v_isSharedCheck_3718_ == 0 {
                            v___x_3713_ = v___x_3708_;
                            v_isShared_3714_ = v_isSharedCheck_3718_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3711_);
                            crate::leanh::lean_dec(v___x_3708_);
                            v___x_3713_ = crate::leanh::lean_box(0);
                            v_isShared_3714_ = v_isSharedCheck_3718_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3714_ == 0 {
                    v___x_3716_ = v___x_3713_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
                    v___x_3716_ = v_reuseFailAlloc_3717_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3716_;
            }
            6 => {
                if v_isShared_3724_ == 0 {
                    v___x_3726_ = v___x_3723_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
                    v___x_3726_ = v_reuseFailAlloc_3727_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3726_;
            }
            8 => {
                if v_isShared_3732_ == 0 {
                    v___x_3734_ = v___x_3731_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
                    v___x_3734_ = v_reuseFailAlloc_3735_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed(
    mut v___x_3737_: *mut crate::leanh::LeanObject,
    mut v___x_3738_: *mut crate::leanh::LeanObject,
    mut v_h_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
    mut v___y_3741_: *mut crate::leanh::LeanObject,
    mut v___y_3742_: *mut crate::leanh::LeanObject,
    mut v___y_3743_: *mut crate::leanh::LeanObject,
    mut v___y_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_18057__boxed_3748_: u8 = 0;
    let mut v___x_18058__boxed_3749_: u8 = 0;
    let mut v_res_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_18057__boxed_3748_ = (crate::leanh::lean_unbox(v___x_3737_) as u8);
    v___x_18058__boxed_3749_ = (crate::leanh::lean_unbox(v___x_3738_) as u8);
    v_res_3750_ = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(
        v___x_18057__boxed_3748_,
        v___x_18058__boxed_3749_,
        v_h_3739_,
        v___y_3740_,
        v___y_3741_,
        v___y_3742_,
        v___y_3743_,
        v___y_3744_,
        v___y_3745_,
        v___y_3746_,
    );
    crate::leanh::lean_dec(v___y_3746_);
    crate::leanh::lean_dec_ref(v___y_3745_);
    crate::leanh::lean_dec(v___y_3744_);
    crate::leanh::lean_dec_ref(v___y_3743_);
    crate::leanh::lean_dec(v___y_3742_);
    crate::leanh::lean_dec_ref(v___y_3741_);
    crate::leanh::lean_dec(v___y_3740_);
    return v_res_3750_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(
    mut v_k_3751_: *mut crate::leanh::LeanObject,
    mut v___y_3752_: *mut crate::leanh::LeanObject,
    mut v___y_3753_: *mut crate::leanh::LeanObject,
    mut v___y_3754_: *mut crate::leanh::LeanObject,
    mut v_b_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3759_);
    crate::leanh::lean_inc_ref(v___y_3758_);
    crate::leanh::lean_inc(v___y_3757_);
    crate::leanh::lean_inc_ref(v___y_3756_);
    crate::leanh::lean_inc(v___y_3754_);
    crate::leanh::lean_inc_ref(v___y_3753_);
    crate::leanh::lean_inc(v___y_3752_);
    v___x_3761_ = crate::leanh::lean_apply_9(
        v_k_3751_,
        v_b_3755_,
        v___y_3752_,
        v___y_3753_,
        v___y_3754_,
        v___y_3756_,
        v___y_3757_,
        v___y_3758_,
        v___y_3759_,
        crate::leanh::lean_box(0),
    );
    return v___x_3761_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
    mut v___y_3765_: *mut crate::leanh::LeanObject,
    mut v_b_3766_: *mut crate::leanh::LeanObject,
    mut v___y_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
    mut v___y_3771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(v_k_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v_b_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
    crate::leanh::lean_dec(v___y_3770_);
    crate::leanh::lean_dec_ref(v___y_3769_);
    crate::leanh::lean_dec(v___y_3768_);
    crate::leanh::lean_dec_ref(v___y_3767_);
    crate::leanh::lean_dec(v___y_3765_);
    crate::leanh::lean_dec_ref(v___y_3764_);
    crate::leanh::lean_dec(v___y_3763_);
    return v_res_3772_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(
    mut v_name_3773_: *mut crate::leanh::LeanObject,
    mut v_bi_3774_: u8,
    mut v_type_3775_: *mut crate::leanh::LeanObject,
    mut v_k_3776_: *mut crate::leanh::LeanObject,
    mut v_kind_3777_: u8,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
    mut v___y_3784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3780_);
                crate::leanh::lean_inc_ref(v___y_3779_);
                crate::leanh::lean_inc(v___y_3778_);
                v___f_3786_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                crate::leanh::lean_closure_set(v___f_3786_, 0, v_k_3776_);
                crate::leanh::lean_closure_set(v___f_3786_, 1, v___y_3778_);
                crate::leanh::lean_closure_set(v___f_3786_, 2, v___y_3779_);
                crate::leanh::lean_closure_set(v___f_3786_, 3, v___y_3780_);
                v___x_3787_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3773_,
                    v_bi_3774_,
                    v_type_3775_,
                    v___f_3786_,
                    v_kind_3777_,
                    v___y_3781_,
                    v___y_3782_,
                    v___y_3783_,
                    v___y_3784_,
                );
                if crate::leanh::lean_obj_tag(v___x_3787_) == 0 {
                    return v___x_3787_;
                } else {
                    v_a_3788_ = crate::leanh::lean_ctor_get(v___x_3787_, 0);
                    v_isSharedCheck_3795_ = (!crate::leanh::lean_is_exclusive(v___x_3787_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v___x_3790_ = v___x_3787_;
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3788_);
                        crate::leanh::lean_dec(v___x_3787_);
                        v___x_3790_ = crate::leanh::lean_box(0);
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3791_ == 0 {
                    v___x_3793_ = v___x_3790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
                    v___x_3793_ = v_reuseFailAlloc_3794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___boxed(
    mut v_name_3796_: *mut crate::leanh::LeanObject,
    mut v_bi_3797_: *mut crate::leanh::LeanObject,
    mut v_type_3798_: *mut crate::leanh::LeanObject,
    mut v_k_3799_: *mut crate::leanh::LeanObject,
    mut v_kind_3800_: *mut crate::leanh::LeanObject,
    mut v___y_3801_: *mut crate::leanh::LeanObject,
    mut v___y_3802_: *mut crate::leanh::LeanObject,
    mut v___y_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
    mut v___y_3805_: *mut crate::leanh::LeanObject,
    mut v___y_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
    mut v___y_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3809_: u8 = 0;
    let mut v_kind_boxed_3810_: u8 = 0;
    let mut v_res_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3809_ = (crate::leanh::lean_unbox(v_bi_3797_) as u8);
    v_kind_boxed_3810_ = (crate::leanh::lean_unbox(v_kind_3800_) as u8);
    v_res_3811_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_3796_, v_bi_boxed_3809_, v_type_3798_, v_k_3799_, v_kind_boxed_3810_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
    crate::leanh::lean_dec(v___y_3807_);
    crate::leanh::lean_dec_ref(v___y_3806_);
    crate::leanh::lean_dec(v___y_3805_);
    crate::leanh::lean_dec_ref(v___y_3804_);
    crate::leanh::lean_dec(v___y_3803_);
    crate::leanh::lean_dec_ref(v___y_3802_);
    crate::leanh::lean_dec(v___y_3801_);
    return v_res_3811_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(
    mut v_name_3812_: *mut crate::leanh::LeanObject,
    mut v_type_3813_: *mut crate::leanh::LeanObject,
    mut v_k_3814_: *mut crate::leanh::LeanObject,
    mut v___y_3815_: *mut crate::leanh::LeanObject,
    mut v___y_3816_: *mut crate::leanh::LeanObject,
    mut v___y_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
    mut v___y_3821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = 0;
    v___x_3824_ = 0;
    v___x_3825_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_3812_, v___x_3823_, v_type_3813_, v_k_3814_, v___x_3824_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
    return v___x_3825_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg___boxed(
    mut v_name_3826_: *mut crate::leanh::LeanObject,
    mut v_type_3827_: *mut crate::leanh::LeanObject,
    mut v_k_3828_: *mut crate::leanh::LeanObject,
    mut v___y_3829_: *mut crate::leanh::LeanObject,
    mut v___y_3830_: *mut crate::leanh::LeanObject,
    mut v___y_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
    mut v___y_3835_: *mut crate::leanh::LeanObject,
    mut v___y_3836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3837_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(
            v_name_3826_,
            v_type_3827_,
            v_k_3828_,
            v___y_3829_,
            v___y_3830_,
            v___y_3831_,
            v___y_3832_,
            v___y_3833_,
            v___y_3834_,
            v___y_3835_,
        );
    crate::leanh::lean_dec(v___y_3835_);
    crate::leanh::lean_dec_ref(v___y_3834_);
    crate::leanh::lean_dec(v___y_3833_);
    crate::leanh::lean_dec_ref(v___y_3832_);
    crate::leanh::lean_dec(v___y_3831_);
    crate::leanh::lean_dec_ref(v___y_3830_);
    crate::leanh::lean_dec(v___y_3829_);
    return v_res_3837_;
}
pub unsafe fn l_Lean_Meta_Grind_reduceCtorEqCheap(
    mut v_e_3841_: *mut crate::leanh::LeanObject,
    mut v_a_3842_: *mut crate::leanh::LeanObject,
    mut v_a_3843_: *mut crate::leanh::LeanObject,
    mut v_a_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
    mut v_a_3846_: *mut crate::leanh::LeanObject,
    mut v_a_3847_: *mut crate::leanh::LeanObject,
    mut v_a_3848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3854_: u8 = 0;
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: u8 = 0;
    let mut v_arg_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v_arg_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: u8 = 0;
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3875_: u8 = 0;
    let mut v_val_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3881_: u8 = 0;
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: u8 = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut v_a_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v_a_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3919_: u8 = 0;
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3923_: u8 = 0;
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_a_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3841_);
                v___x_3850_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3841_, v_a_3846_);
                if crate::leanh::lean_obj_tag(v___x_3850_) == 0 {
                    v_a_3851_ = crate::leanh::lean_ctor_get(v___x_3850_, 0);
                    v_isSharedCheck_3924_ = (!crate::leanh::lean_is_exclusive(v___x_3850_)) as u8;
                    if v_isSharedCheck_3924_ == 0 {
                        v___x_3853_ = v___x_3850_;
                        v_isShared_3854_ = v_isSharedCheck_3924_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3851_);
                        crate::leanh::lean_dec(v___x_3850_);
                        v___x_3853_ = crate::leanh::lean_box(0);
                        v_isShared_3854_ = v_isSharedCheck_3924_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3841_);
                    v_a_3925_ = crate::leanh::lean_ctor_get(v___x_3850_, 0);
                    v_isSharedCheck_3932_ = (!crate::leanh::lean_is_exclusive(v___x_3850_)) as u8;
                    if v_isSharedCheck_3932_ == 0 {
                        v___x_3927_ = v___x_3850_;
                        v_isShared_3928_ = v_isSharedCheck_3932_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3925_);
                        crate::leanh::lean_dec(v___x_3850_);
                        v___x_3927_ = crate::leanh::lean_box(0);
                        v_isShared_3928_ = v_isSharedCheck_3932_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3860_ = l_Lean_Expr_cleanupAnnotations(v_a_3851_);
                v___x_3861_ = l_Lean_Expr_isApp(v___x_3860_);
                if v___x_3861_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3860_);
                    crate::leanh::lean_dec_ref(v_e_3841_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3862_ = crate::leanh::lean_ctor_get(v___x_3860_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3862_);
                    v___x_3863_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3860_);
                    v___x_3864_ = l_Lean_Expr_isApp(v___x_3863_);
                    if v___x_3864_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3863_);
                        crate::leanh::lean_dec_ref(v_arg_3862_);
                        crate::leanh::lean_dec_ref(v_e_3841_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_3865_ = crate::leanh::lean_ctor_get(v___x_3863_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3865_);
                        v___x_3866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3863_);
                        v___x_3867_ = l_Lean_Expr_isApp(v___x_3866_);
                        if v___x_3867_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3866_);
                            crate::leanh::lean_dec_ref(v_arg_3865_);
                            crate::leanh::lean_dec_ref(v_arg_3862_);
                            crate::leanh::lean_dec_ref(v_e_3841_);
                            state = 2;
                            continue;
                        } else {
                            v___x_3868_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3866_);
                            v___x_3869_ = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
                            v___x_3870_ = l_Lean_Expr_isConstOf(v___x_3868_, v___x_3869_);
                            crate::leanh::lean_dec_ref(v___x_3868_);
                            if v___x_3870_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_3865_);
                                crate::leanh::lean_dec_ref(v_arg_3862_);
                                crate::leanh::lean_dec_ref(v_e_3841_);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_3853_);
                                v___x_3871_ = l_Lean_Meta_isConstructorApp_x3f(
                                    v_arg_3865_,
                                    v_a_3845_,
                                    v_a_3846_,
                                    v_a_3847_,
                                    v_a_3848_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3871_) == 0 {
                                    v_a_3872_ = crate::leanh::lean_ctor_get(v___x_3871_, 0);
                                    v_isSharedCheck_3915_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3871_)) as u8;
                                    if v_isSharedCheck_3915_ == 0 {
                                        v___x_3874_ = v___x_3871_;
                                        v_isShared_3875_ = v_isSharedCheck_3915_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3872_);
                                        crate::leanh::lean_dec(v___x_3871_);
                                        v___x_3874_ = crate::leanh::lean_box(0);
                                        v_isShared_3875_ = v_isSharedCheck_3915_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_3862_);
                                    crate::leanh::lean_dec_ref(v_e_3841_);
                                    v_a_3916_ = crate::leanh::lean_ctor_get(v___x_3871_, 0);
                                    v_isSharedCheck_3923_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3871_)) as u8;
                                    if v_isSharedCheck_3923_ == 0 {
                                        v___x_3918_ = v___x_3871_;
                                        v_isShared_3919_ = v_isSharedCheck_3923_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3916_);
                                        crate::leanh::lean_dec(v___x_3871_);
                                        v___x_3918_ = crate::leanh::lean_box(0);
                                        v_isShared_3919_ = v_isSharedCheck_3923_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3856_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_3854_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3853_, 0, v___x_3856_);
                    v___x_3858_ = v___x_3853_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3859_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
                    v___x_3858_ = v_reuseFailAlloc_3859_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3858_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_3872_) == 1 {
                    v_val_3876_ = crate::leanh::lean_ctor_get(v_a_3872_, 0);
                    crate::leanh::lean_inc(v_val_3876_);
                    crate::leanh::lean_dec_ref_known(v_a_3872_, 1);
                    v___x_3877_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_arg_3862_,
                        v_a_3845_,
                        v_a_3846_,
                        v_a_3847_,
                        v_a_3848_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3877_) == 0 {
                        v_a_3878_ = crate::leanh::lean_ctor_get(v___x_3877_, 0);
                        v_isSharedCheck_3902_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3877_)) as u8;
                        if v_isSharedCheck_3902_ == 0 {
                            v___x_3880_ = v___x_3877_;
                            v_isShared_3881_ = v_isSharedCheck_3902_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3878_);
                            crate::leanh::lean_dec(v___x_3877_);
                            v___x_3880_ = crate::leanh::lean_box(0);
                            v_isShared_3881_ = v_isSharedCheck_3902_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3876_);
                        crate::leanh::lean_del_object(v___x_3874_);
                        crate::leanh::lean_dec_ref(v_e_3841_);
                        v_a_3903_ = crate::leanh::lean_ctor_get(v___x_3877_, 0);
                        v_isSharedCheck_3910_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3877_)) as u8;
                        if v_isSharedCheck_3910_ == 0 {
                            v___x_3905_ = v___x_3877_;
                            v_isShared_3906_ = v_isSharedCheck_3910_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3903_);
                            crate::leanh::lean_dec(v___x_3877_);
                            v___x_3905_ = crate::leanh::lean_box(0);
                            v_isShared_3906_ = v_isSharedCheck_3910_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3872_);
                    crate::leanh::lean_dec_ref(v_arg_3862_);
                    crate::leanh::lean_dec_ref(v_e_3841_);
                    v___x_3911_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    if v_isShared_3875_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3874_, 0, v___x_3911_);
                        v___x_3913_ = v___x_3874_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
                        v___x_3913_ = v_reuseFailAlloc_3914_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_3878_) == 1 {
                    crate::leanh::lean_del_object(v___x_3874_);
                    v_toConstantVal_3887_ = crate::leanh::lean_ctor_get(v_val_3876_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_3887_);
                    crate::leanh::lean_dec(v_val_3876_);
                    v_val_3888_ = crate::leanh::lean_ctor_get(v_a_3878_, 0);
                    crate::leanh::lean_inc(v_val_3888_);
                    crate::leanh::lean_dec_ref_known(v_a_3878_, 1);
                    v_toConstantVal_3889_ = crate::leanh::lean_ctor_get(v_val_3888_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_3889_);
                    crate::leanh::lean_dec(v_val_3888_);
                    v_name_3890_ = crate::leanh::lean_ctor_get(v_toConstantVal_3887_, 0);
                    crate::leanh::lean_inc(v_name_3890_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_3887_);
                    v_name_3891_ = crate::leanh::lean_ctor_get(v_toConstantVal_3889_, 0);
                    crate::leanh::lean_inc(v_name_3891_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_3889_);
                    v___x_3892_ = lean_name_eq(v_name_3890_, v_name_3891_);
                    crate::leanh::lean_dec(v_name_3891_);
                    crate::leanh::lean_dec(v_name_3890_);
                    if v___x_3892_ == 0 {
                        if v___x_3870_ == 0 {
                            crate::leanh::lean_dec_ref(v_e_3841_);
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_3880_);
                            v___x_3893_ = crate::leanh::lean_box((v___x_3892_) as usize);
                            v___x_3894_ = crate::leanh::lean_box((v___x_3870_) as usize);
                            v___f_3895_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                2,
                            );
                            crate::leanh::lean_closure_set(v___f_3895_, 0, v___x_3893_);
                            crate::leanh::lean_closure_set(v___f_3895_, 1, v___x_3894_);
                            v___x_3896_ = l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1;
                            v___x_3897_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v___x_3896_, v_e_3841_, v___f_3895_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
                            return v___x_3897_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3841_);
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3880_);
                    crate::leanh::lean_dec(v_a_3878_);
                    crate::leanh::lean_dec(v_val_3876_);
                    crate::leanh::lean_dec_ref(v_e_3841_);
                    v___x_3898_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    if v_isShared_3875_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3874_, 0, v___x_3898_);
                        v___x_3900_ = v___x_3874_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
                        v___x_3900_ = v_reuseFailAlloc_3901_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3883_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_3881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3880_, 0, v___x_3883_);
                    v___x_3885_ = v___x_3880_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
                    v___x_3885_ = v_reuseFailAlloc_3886_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3885_;
            }
            8 => {
                return v___x_3900_;
            }
            9 => {
                if v_isShared_3906_ == 0 {
                    v___x_3908_ = v___x_3905_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
                    v___x_3908_ = v_reuseFailAlloc_3909_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3908_;
            }
            11 => {
                return v___x_3913_;
            }
            12 => {
                if v_isShared_3919_ == 0 {
                    v___x_3921_ = v___x_3918_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3922_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
                    v___x_3921_ = v_reuseFailAlloc_3922_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3921_;
            }
            14 => {
                if v_isShared_3928_ == 0 {
                    v___x_3930_ = v___x_3927_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
                    v___x_3930_ = v_reuseFailAlloc_3931_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_reduceCtorEqCheap___boxed(
    mut v_e_3933_: *mut crate::leanh::LeanObject,
    mut v_a_3934_: *mut crate::leanh::LeanObject,
    mut v_a_3935_: *mut crate::leanh::LeanObject,
    mut v_a_3936_: *mut crate::leanh::LeanObject,
    mut v_a_3937_: *mut crate::leanh::LeanObject,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
    mut v_a_3941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3942_ = l_Lean_Meta_Grind_reduceCtorEqCheap(
        v_e_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_,
    );
    crate::leanh::lean_dec(v_a_3940_);
    crate::leanh::lean_dec_ref(v_a_3939_);
    crate::leanh::lean_dec(v_a_3938_);
    crate::leanh::lean_dec_ref(v_a_3937_);
    crate::leanh::lean_dec(v_a_3936_);
    crate::leanh::lean_dec_ref(v_a_3935_);
    crate::leanh::lean_dec(v_a_3934_);
    return v_res_3942_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(
    mut v_00_u03b1_3943_: *mut crate::leanh::LeanObject,
    mut v_name_3944_: *mut crate::leanh::LeanObject,
    mut v_bi_3945_: u8,
    mut v_type_3946_: *mut crate::leanh::LeanObject,
    mut v_k_3947_: *mut crate::leanh::LeanObject,
    mut v_kind_3948_: u8,
    mut v___y_3949_: *mut crate::leanh::LeanObject,
    mut v___y_3950_: *mut crate::leanh::LeanObject,
    mut v___y_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3957_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_3944_, v_bi_3945_, v_type_3946_, v_k_3947_, v_kind_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    return v___x_3957_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___boxed(
    mut v_00_u03b1_3958_: *mut crate::leanh::LeanObject,
    mut v_name_3959_: *mut crate::leanh::LeanObject,
    mut v_bi_3960_: *mut crate::leanh::LeanObject,
    mut v_type_3961_: *mut crate::leanh::LeanObject,
    mut v_k_3962_: *mut crate::leanh::LeanObject,
    mut v_kind_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
    mut v___y_3968_: *mut crate::leanh::LeanObject,
    mut v___y_3969_: *mut crate::leanh::LeanObject,
    mut v___y_3970_: *mut crate::leanh::LeanObject,
    mut v___y_3971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3972_: u8 = 0;
    let mut v_kind_boxed_3973_: u8 = 0;
    let mut v_res_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3972_ = (crate::leanh::lean_unbox(v_bi_3960_) as u8);
    v_kind_boxed_3973_ = (crate::leanh::lean_unbox(v_kind_3963_) as u8);
    v_res_3974_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(v_00_u03b1_3958_, v_name_3959_, v_bi_boxed_3972_, v_type_3961_, v_k_3962_, v_kind_boxed_3973_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
    crate::leanh::lean_dec(v___y_3970_);
    crate::leanh::lean_dec_ref(v___y_3969_);
    crate::leanh::lean_dec(v___y_3968_);
    crate::leanh::lean_dec_ref(v___y_3967_);
    crate::leanh::lean_dec(v___y_3966_);
    crate::leanh::lean_dec_ref(v___y_3965_);
    crate::leanh::lean_dec(v___y_3964_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(
    mut v_00_u03b1_3975_: *mut crate::leanh::LeanObject,
    mut v_name_3976_: *mut crate::leanh::LeanObject,
    mut v_type_3977_: *mut crate::leanh::LeanObject,
    mut v_k_3978_: *mut crate::leanh::LeanObject,
    mut v___y_3979_: *mut crate::leanh::LeanObject,
    mut v___y_3980_: *mut crate::leanh::LeanObject,
    mut v___y_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3987_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(
            v_name_3976_,
            v_type_3977_,
            v_k_3978_,
            v___y_3979_,
            v___y_3980_,
            v___y_3981_,
            v___y_3982_,
            v___y_3983_,
            v___y_3984_,
            v___y_3985_,
        );
    return v___x_3987_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___boxed(
    mut v_00_u03b1_3988_: *mut crate::leanh::LeanObject,
    mut v_name_3989_: *mut crate::leanh::LeanObject,
    mut v_type_3990_: *mut crate::leanh::LeanObject,
    mut v_k_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
    mut v___y_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
    mut v___y_3996_: *mut crate::leanh::LeanObject,
    mut v___y_3997_: *mut crate::leanh::LeanObject,
    mut v___y_3998_: *mut crate::leanh::LeanObject,
    mut v___y_3999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4000_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(
        v_00_u03b1_3988_,
        v_name_3989_,
        v_type_3990_,
        v_k_3991_,
        v___y_3992_,
        v___y_3993_,
        v___y_3994_,
        v___y_3995_,
        v___y_3996_,
        v___y_3997_,
        v___y_3998_,
    );
    crate::leanh::lean_dec(v___y_3998_);
    crate::leanh::lean_dec_ref(v___y_3997_);
    crate::leanh::lean_dec(v___y_3996_);
    crate::leanh::lean_dec_ref(v___y_3995_);
    crate::leanh::lean_dec(v___y_3994_);
    crate::leanh::lean_dec_ref(v___y_3993_);
    crate::leanh::lean_dec(v___y_3992_);
    return v_res_4000_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4008_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_;
    v___x_4009_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
    v___x_4010_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_reduceCtorEqCheap___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4011_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4008_, v___x_4009_, v___x_4010_);
    return v___x_4011_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13____boxed(
    mut v_a_4012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4013_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_();
    return v_res_4013_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(
    mut v_e_4014_: *mut crate::leanh::LeanObject,
    mut v_a_4015_: *mut crate::leanh::LeanObject,
    mut v_a_4016_: *mut crate::leanh::LeanObject,
    mut v_a_4017_: *mut crate::leanh::LeanObject,
    mut v_a_4018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4020_ =
        l_Lean_Meta_Sym_unfoldReducibleStep(v_e_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
    return v___x_4020_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg___boxed(
    mut v_e_4021_: *mut crate::leanh::LeanObject,
    mut v_a_4022_: *mut crate::leanh::LeanObject,
    mut v_a_4023_: *mut crate::leanh::LeanObject,
    mut v_a_4024_: *mut crate::leanh::LeanObject,
    mut v_a_4025_: *mut crate::leanh::LeanObject,
    mut v_a_4026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4027_ = l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(
        v_e_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_,
    );
    crate::leanh::lean_dec(v_a_4025_);
    crate::leanh::lean_dec_ref(v_a_4024_);
    crate::leanh::lean_dec(v_a_4023_);
    crate::leanh::lean_dec_ref(v_a_4022_);
    return v_res_4027_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc(
    mut v_e_4028_: *mut crate::leanh::LeanObject,
    mut v_a_4029_: *mut crate::leanh::LeanObject,
    mut v_a_4030_: *mut crate::leanh::LeanObject,
    mut v_a_4031_: *mut crate::leanh::LeanObject,
    mut v_a_4032_: *mut crate::leanh::LeanObject,
    mut v_a_4033_: *mut crate::leanh::LeanObject,
    mut v_a_4034_: *mut crate::leanh::LeanObject,
    mut v_a_4035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4037_ =
        l_Lean_Meta_Sym_unfoldReducibleStep(v_e_4028_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
    return v___x_4037_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc___boxed(
    mut v_e_4038_: *mut crate::leanh::LeanObject,
    mut v_a_4039_: *mut crate::leanh::LeanObject,
    mut v_a_4040_: *mut crate::leanh::LeanObject,
    mut v_a_4041_: *mut crate::leanh::LeanObject,
    mut v_a_4042_: *mut crate::leanh::LeanObject,
    mut v_a_4043_: *mut crate::leanh::LeanObject,
    mut v_a_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_a_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4047_ = l_Lean_Meta_Grind_unfoldReducibleSimproc(
        v_e_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_,
    );
    crate::leanh::lean_dec(v_a_4045_);
    crate::leanh::lean_dec_ref(v_a_4044_);
    crate::leanh::lean_dec(v_a_4043_);
    crate::leanh::lean_dec_ref(v_a_4042_);
    crate::leanh::lean_dec(v_a_4041_);
    crate::leanh::lean_dec_ref(v_a_4040_);
    crate::leanh::lean_dec(v_a_4039_);
    return v_res_4047_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_(
    mut v___y_4048_: *mut crate::leanh::LeanObject,
    mut v___y_4049_: *mut crate::leanh::LeanObject,
    mut v___y_4050_: *mut crate::leanh::LeanObject,
    mut v___y_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4057_ = l_Lean_Meta_Sym_unfoldReducibleStep(
        v___y_4048_,
        v___y_4052_,
        v___y_4053_,
        v___y_4054_,
        v___y_4055_,
    );
    return v___x_4057_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9____boxed(
    mut v___y_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
    mut v___y_4062_: *mut crate::leanh::LeanObject,
    mut v___y_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4067_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_(v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
    crate::leanh::lean_dec(v___y_4065_);
    crate::leanh::lean_dec_ref(v___y_4064_);
    crate::leanh::lean_dec(v___y_4063_);
    crate::leanh::lean_dec_ref(v___y_4062_);
    crate::leanh::lean_dec(v___y_4061_);
    crate::leanh::lean_dec_ref(v___y_4060_);
    crate::leanh::lean_dec(v___y_4059_);
    return v_res_4067_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4080_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
    v___x_4081_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
    v___x_4082_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
    v___x_4083_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4081_, v___x_4082_, v___f_4080_);
    return v___x_4083_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9____boxed(
    mut v_a_4084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4085_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_();
    return v_res_4085_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs___redArg(
    mut v_a_4094_: *mut crate::leanh::LeanObject,
    mut v_a_4095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut v_a_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v_a_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4172_: u8 = 0;
    let mut v_a_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4180_: u8 = 0;
    let mut v_a_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4184_: u8 = 0;
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4188_: u8 = 0;
    let mut v_a_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4196_: u8 = 0;
    let mut v_a_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v_a_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4208_: u8 = 0;
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_a_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v_a_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4097_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_4095_);
                if crate::leanh::lean_obj_tag(v___x_4097_) == 0 {
                    v_a_4098_ = crate::leanh::lean_ctor_get(v___x_4097_, 0);
                    crate::leanh::lean_inc(v_a_4098_);
                    crate::leanh::lean_dec_ref_known(v___x_4097_, 1);
                    v___x_4099_ = l_Lean_Meta_Grind_getSimprocs___redArg___closed__2;
                    v___x_4100_ = l_Lean_Meta_Simp_Simprocs_erase(v_a_4098_, v___x_4099_);
                    v___x_4101_ = l_Lean_Meta_Grind_getSimprocs___redArg___closed__4;
                    v___x_4102_ = l_Lean_Meta_Simp_Simprocs_erase(v___x_4100_, v___x_4101_);
                    v___x_4103_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_;
                    v___x_4104_ = 1;
                    v___x_4105_ = l_Lean_Meta_Simp_Simprocs_add(
                        v___x_4102_,
                        v___x_4103_,
                        v___x_4104_,
                        v_a_4094_,
                        v_a_4095_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4105_) == 0 {
                        v_a_4106_ = crate::leanh::lean_ctor_get(v___x_4105_, 0);
                        crate::leanh::lean_inc(v_a_4106_);
                        crate::leanh::lean_dec_ref_known(v___x_4105_, 1);
                        v___x_4107_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(
                            v_a_4106_, v_a_4094_, v_a_4095_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4107_) == 0 {
                            v_a_4108_ = crate::leanh::lean_ctor_get(v___x_4107_, 0);
                            crate::leanh::lean_inc(v_a_4108_);
                            crate::leanh::lean_dec_ref_known(v___x_4107_, 1);
                            v___x_4109_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(
                                v_a_4108_, v_a_4094_, v_a_4095_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4109_) == 0 {
                                v_a_4110_ = crate::leanh::lean_ctor_get(v___x_4109_, 0);
                                crate::leanh::lean_inc(v_a_4110_);
                                crate::leanh::lean_dec_ref_known(v___x_4109_, 1);
                                v___x_4111_ = l_Lean_Meta_Grind_Arith_addSimproc(
                                    v_a_4110_, v_a_4094_, v_a_4095_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4111_) == 0 {
                                    v_a_4112_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
                                    crate::leanh::lean_inc(v_a_4112_);
                                    crate::leanh::lean_dec_ref_known(v___x_4111_, 1);
                                    v___x_4113_ = l_Lean_Meta_Grind_addForallSimproc(
                                        v_a_4112_, v_a_4094_, v_a_4095_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4113_) == 0 {
                                        v_a_4114_ = crate::leanh::lean_ctor_get(v___x_4113_, 0);
                                        crate::leanh::lean_inc(v_a_4114_);
                                        crate::leanh::lean_dec_ref_known(v___x_4113_, 1);
                                        v___x_4115_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
                                        v___x_4116_ = l_Lean_Meta_Simp_Simprocs_add(
                                            v_a_4114_,
                                            v___x_4115_,
                                            v___x_4104_,
                                            v_a_4094_,
                                            v_a_4095_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_4116_) == 0 {
                                            v_a_4117_ = crate::leanh::lean_ctor_get(v___x_4116_, 0);
                                            crate::leanh::lean_inc(v_a_4117_);
                                            crate::leanh::lean_dec_ref_known(v___x_4116_, 1);
                                            v___x_4118_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_;
                                            v___x_4119_ = l_Lean_Meta_Simp_Simprocs_add(
                                                v_a_4117_,
                                                v___x_4118_,
                                                v___x_4104_,
                                                v_a_4094_,
                                                v_a_4095_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_4119_) == 0 {
                                                v_a_4120_ =
                                                    crate::leanh::lean_ctor_get(v___x_4119_, 0);
                                                crate::leanh::lean_inc(v_a_4120_);
                                                crate::leanh::lean_dec_ref_known(v___x_4119_, 1);
                                                v___x_4121_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_;
                                                v___x_4122_ = l_Lean_Meta_Simp_Simprocs_add(
                                                    v_a_4120_,
                                                    v___x_4121_,
                                                    v___x_4104_,
                                                    v_a_4094_,
                                                    v_a_4095_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_4122_) == 0 {
                                                    v_a_4123_ =
                                                        crate::leanh::lean_ctor_get(v___x_4122_, 0);
                                                    crate::leanh::lean_inc(v_a_4123_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_4122_,
                                                        1,
                                                    );
                                                    v___x_4124_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_;
                                                    v___x_4125_ = 0;
                                                    v___x_4126_ = l_Lean_Meta_Simp_Simprocs_add(
                                                        v_a_4123_,
                                                        v___x_4124_,
                                                        v___x_4125_,
                                                        v_a_4094_,
                                                        v_a_4095_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_4126_) == 0
                                                    {
                                                        v_a_4127_ = crate::leanh::lean_ctor_get(
                                                            v___x_4126_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_4127_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_4126_,
                                                            1,
                                                        );
                                                        v___x_4128_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
                                                        v___x_4129_ = l_Lean_Meta_Simp_Simprocs_add(
                                                            v_a_4127_,
                                                            v___x_4128_,
                                                            v___x_4125_,
                                                            v_a_4094_,
                                                            v_a_4095_,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v___x_4129_)
                                                            == 0
                                                        {
                                                            v_a_4130_ = crate::leanh::lean_ctor_get(
                                                                v___x_4129_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4140_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_4129_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_4140_ == 0 {
                                                                v___x_4132_ = v___x_4129_;
                                                                v_isShared_4133_ =
                                                                    v_isSharedCheck_4140_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_4130_);
                                                                crate::leanh::lean_dec(v___x_4129_);
                                                                v___x_4132_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_4133_ =
                                                                    v_isSharedCheck_4140_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_4141_ = crate::leanh::lean_ctor_get(
                                                                v___x_4129_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4148_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_4129_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_4148_ == 0 {
                                                                v___x_4143_ = v___x_4129_;
                                                                v_isShared_4144_ =
                                                                    v_isSharedCheck_4148_;
                                                                state = 3;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_4141_);
                                                                crate::leanh::lean_dec(v___x_4129_);
                                                                v___x_4143_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_4144_ =
                                                                    v_isSharedCheck_4148_;
                                                                state = 3;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        v_a_4149_ = crate::leanh::lean_ctor_get(
                                                            v___x_4126_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4156_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_4126_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4156_ == 0 {
                                                            v___x_4151_ = v___x_4126_;
                                                            v_isShared_4152_ =
                                                                v_isSharedCheck_4156_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_4149_);
                                                            crate::leanh::lean_dec(v___x_4126_);
                                                            v___x_4151_ = crate::leanh::lean_box(0);
                                                            v_isShared_4152_ =
                                                                v_isSharedCheck_4156_;
                                                            state = 5;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    v_a_4157_ =
                                                        crate::leanh::lean_ctor_get(v___x_4122_, 0);
                                                    v_isSharedCheck_4164_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_4122_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4164_ == 0 {
                                                        v___x_4159_ = v___x_4122_;
                                                        v_isShared_4160_ = v_isSharedCheck_4164_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_4157_);
                                                        crate::leanh::lean_dec(v___x_4122_);
                                                        v___x_4159_ = crate::leanh::lean_box(0);
                                                        v_isShared_4160_ = v_isSharedCheck_4164_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                v_a_4165_ =
                                                    crate::leanh::lean_ctor_get(v___x_4119_, 0);
                                                v_isSharedCheck_4172_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4119_))
                                                        as u8;
                                                if v_isSharedCheck_4172_ == 0 {
                                                    v___x_4167_ = v___x_4119_;
                                                    v_isShared_4168_ = v_isSharedCheck_4172_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4165_);
                                                    crate::leanh::lean_dec(v___x_4119_);
                                                    v___x_4167_ = crate::leanh::lean_box(0);
                                                    v_isShared_4168_ = v_isSharedCheck_4172_;
                                                    state = 9;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v_a_4173_ = crate::leanh::lean_ctor_get(v___x_4116_, 0);
                                            v_isSharedCheck_4180_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4116_))
                                                    as u8;
                                            if v_isSharedCheck_4180_ == 0 {
                                                v___x_4175_ = v___x_4116_;
                                                v_isShared_4176_ = v_isSharedCheck_4180_;
                                                state = 11;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4173_);
                                                crate::leanh::lean_dec(v___x_4116_);
                                                v___x_4175_ = crate::leanh::lean_box(0);
                                                v_isShared_4176_ = v_isSharedCheck_4180_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v_a_4181_ = crate::leanh::lean_ctor_get(v___x_4113_, 0);
                                        v_isSharedCheck_4188_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4113_)) as u8;
                                        if v_isSharedCheck_4188_ == 0 {
                                            v___x_4183_ = v___x_4113_;
                                            v_isShared_4184_ = v_isSharedCheck_4188_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4181_);
                                            crate::leanh::lean_dec(v___x_4113_);
                                            v___x_4183_ = crate::leanh::lean_box(0);
                                            v_isShared_4184_ = v_isSharedCheck_4188_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_a_4189_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
                                    v_isSharedCheck_4196_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4111_)) as u8;
                                    if v_isSharedCheck_4196_ == 0 {
                                        v___x_4191_ = v___x_4111_;
                                        v_isShared_4192_ = v_isSharedCheck_4196_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4189_);
                                        crate::leanh::lean_dec(v___x_4111_);
                                        v___x_4191_ = crate::leanh::lean_box(0);
                                        v_isShared_4192_ = v_isSharedCheck_4196_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_4197_ = crate::leanh::lean_ctor_get(v___x_4109_, 0);
                                v_isSharedCheck_4204_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4109_)) as u8;
                                if v_isSharedCheck_4204_ == 0 {
                                    v___x_4199_ = v___x_4109_;
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4197_);
                                    crate::leanh::lean_dec(v___x_4109_);
                                    v___x_4199_ = crate::leanh::lean_box(0);
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4205_ = crate::leanh::lean_ctor_get(v___x_4107_, 0);
                            v_isSharedCheck_4212_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4107_)) as u8;
                            if v_isSharedCheck_4212_ == 0 {
                                v___x_4207_ = v___x_4107_;
                                v_isShared_4208_ = v_isSharedCheck_4212_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4205_);
                                crate::leanh::lean_dec(v___x_4107_);
                                v___x_4207_ = crate::leanh::lean_box(0);
                                v_isShared_4208_ = v_isSharedCheck_4212_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        v_a_4213_ = crate::leanh::lean_ctor_get(v___x_4105_, 0);
                        v_isSharedCheck_4220_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4105_)) as u8;
                        if v_isSharedCheck_4220_ == 0 {
                            v___x_4215_ = v___x_4105_;
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4213_);
                            crate::leanh::lean_dec(v___x_4105_);
                            v___x_4215_ = crate::leanh::lean_box(0);
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    v_a_4221_ = crate::leanh::lean_ctor_get(v___x_4097_, 0);
                    v_isSharedCheck_4228_ = (!crate::leanh::lean_is_exclusive(v___x_4097_)) as u8;
                    if v_isSharedCheck_4228_ == 0 {
                        v___x_4223_ = v___x_4097_;
                        v_isShared_4224_ = v_isSharedCheck_4228_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4221_);
                        crate::leanh::lean_dec(v___x_4097_);
                        v___x_4223_ = crate::leanh::lean_box(0);
                        v_isShared_4224_ = v_isSharedCheck_4228_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4134_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4135_ = lean_mk_empty_array_with_capacity(v___x_4134_);
                v___x_4136_ = lean_array_push(v___x_4135_, v_a_4130_);
                if v_isShared_4133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4132_, 0, v___x_4136_);
                    v___x_4138_ = v___x_4132_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
                    v___x_4138_ = v_reuseFailAlloc_4139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4138_;
            }
            3 => {
                if v_isShared_4144_ == 0 {
                    v___x_4146_ = v___x_4143_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
                    v___x_4146_ = v_reuseFailAlloc_4147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4146_;
            }
            5 => {
                if v_isShared_4152_ == 0 {
                    v___x_4154_ = v___x_4151_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4154_;
            }
            7 => {
                if v_isShared_4160_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4162_;
            }
            9 => {
                if v_isShared_4168_ == 0 {
                    v___x_4170_ = v___x_4167_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4171_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
                    v___x_4170_ = v_reuseFailAlloc_4171_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4170_;
            }
            11 => {
                if v_isShared_4176_ == 0 {
                    v___x_4178_ = v___x_4175_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
                    v___x_4178_ = v_reuseFailAlloc_4179_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4178_;
            }
            13 => {
                if v_isShared_4184_ == 0 {
                    v___x_4186_ = v___x_4183_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
                    v___x_4186_ = v_reuseFailAlloc_4187_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4186_;
            }
            15 => {
                if v_isShared_4192_ == 0 {
                    v___x_4194_ = v___x_4191_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4195_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
                    v___x_4194_ = v_reuseFailAlloc_4195_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4194_;
            }
            17 => {
                if v_isShared_4200_ == 0 {
                    v___x_4202_ = v___x_4199_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
                    v___x_4202_ = v_reuseFailAlloc_4203_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4202_;
            }
            19 => {
                if v_isShared_4208_ == 0 {
                    v___x_4210_ = v___x_4207_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
                    v___x_4210_ = v_reuseFailAlloc_4211_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4210_;
            }
            21 => {
                if v_isShared_4216_ == 0 {
                    v___x_4218_ = v___x_4215_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
                    v___x_4218_ = v_reuseFailAlloc_4219_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4218_;
            }
            23 => {
                if v_isShared_4224_ == 0 {
                    v___x_4226_ = v___x_4223_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
                    v___x_4226_ = v_reuseFailAlloc_4227_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs___redArg___boxed(
    mut v_a_4229_: *mut crate::leanh::LeanObject,
    mut v_a_4230_: *mut crate::leanh::LeanObject,
    mut v_a_4231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4232_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_4229_, v_a_4230_);
    crate::leanh::lean_dec(v_a_4230_);
    crate::leanh::lean_dec_ref(v_a_4229_);
    return v_res_4232_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs(
    mut v_a_4233_: *mut crate::leanh::LeanObject,
    mut v_a_4234_: *mut crate::leanh::LeanObject,
    mut v_a_4235_: *mut crate::leanh::LeanObject,
    mut v_a_4236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4238_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_4235_, v_a_4236_);
    return v___x_4238_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs___boxed(
    mut v_a_4239_: *mut crate::leanh::LeanObject,
    mut v_a_4240_: *mut crate::leanh::LeanObject,
    mut v_a_4241_: *mut crate::leanh::LeanObject,
    mut v_a_4242_: *mut crate::leanh::LeanObject,
    mut v_a_4243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4244_ = l_Lean_Meta_Grind_getSimprocs(v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
    crate::leanh::lean_dec(v_a_4242_);
    crate::leanh::lean_dec_ref(v_a_4241_);
    crate::leanh::lean_dec(v_a_4240_);
    crate::leanh::lean_dec_ref(v_a_4239_);
    return v_res_4244_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
    mut v_s_4245_: *mut crate::leanh::LeanObject,
    mut v_declName_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
    mut v_a_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: u8 = 0;
    v___x_4252_ = lean_st_ref_get(v_a_4250_);
    v_env_4253_ = crate::leanh::lean_ctor_get(v___x_4252_, 0);
    crate::leanh::lean_inc_ref(v_env_4253_);
    crate::leanh::lean_dec(v___x_4252_);
    v___x_4254_ = 1;
    crate::leanh::lean_inc(v_declName_4246_);
    v___x_4255_ = l_Lean_Environment_contains(v_env_4253_, v_declName_4246_, v___x_4254_);
    if v___x_4255_ == 0 {
        let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_declName_4246_);
        v___x_4256_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4256_, 0, v_s_4245_);
        return v___x_4256_;
    } else {
        let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4257_ = l_Lean_Meta_SimpTheorems_addDeclToUnfold(
            v_s_4245_,
            v_declName_4246_,
            v_a_4247_,
            v_a_4248_,
            v_a_4249_,
            v_a_4250_,
        );
        return v___x_4257_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold___boxed(
    mut v_s_4258_: *mut crate::leanh::LeanObject,
    mut v_declName_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4265_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
        v_s_4258_,
        v_declName_4259_,
        v_a_4260_,
        v_a_4261_,
        v_a_4262_,
        v_a_4263_,
    );
    crate::leanh::lean_dec(v_a_4263_);
    crate::leanh::lean_dec_ref(v_a_4262_);
    crate::leanh::lean_dec(v_a_4261_);
    crate::leanh::lean_dec_ref(v_a_4260_);
    return v_res_4265_;
}
pub unsafe fn l_Lean_Meta_Grind_getNormTheorems(
    mut v_a_4287_: *mut crate::leanh::LeanObject,
    mut v_a_4288_: *mut crate::leanh::LeanObject,
    mut v_a_4289_: *mut crate::leanh::LeanObject,
    mut v_a_4290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_Lean_Meta_Grind_normExt;
    v___x_4293_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_4292_, v_a_4290_);
    if crate::leanh::lean_obj_tag(v___x_4293_) == 0 {
        let mut v_a_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4294_ = crate::leanh::lean_ctor_get(v___x_4293_, 0);
        crate::leanh::lean_inc(v_a_4294_);
        crate::leanh::lean_dec_ref_known(v___x_4293_, 1);
        v___x_4295_ = l_Lean_Meta_Grind_getNormTheorems___closed__2;
        v___x_4296_ =
            l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
                v_a_4294_,
                v___x_4295_,
                v_a_4287_,
                v_a_4288_,
                v_a_4289_,
                v_a_4290_,
            );
        if crate::leanh::lean_obj_tag(v___x_4296_) == 0 {
            let mut v_a_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_4297_ = crate::leanh::lean_ctor_get(v___x_4296_, 0);
            crate::leanh::lean_inc(v_a_4297_);
            crate::leanh::lean_dec_ref_known(v___x_4296_, 1);
            v___x_4298_ = l_Lean_Meta_Grind_getNormTheorems___closed__5;
            v___x_4299_ =
                l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
                    v_a_4297_,
                    v___x_4298_,
                    v_a_4287_,
                    v_a_4288_,
                    v_a_4289_,
                    v_a_4290_,
                );
            if crate::leanh::lean_obj_tag(v___x_4299_) == 0 {
                let mut v_a_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_4300_ = crate::leanh::lean_ctor_get(v___x_4299_, 0);
                crate::leanh::lean_inc(v_a_4300_);
                crate::leanh::lean_dec_ref_known(v___x_4299_, 1);
                v___x_4301_ = l_Lean_Meta_Grind_getNormTheorems___closed__7;
                v___x_4302_ =
                    l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
                        v_a_4300_,
                        v___x_4301_,
                        v_a_4287_,
                        v_a_4288_,
                        v_a_4289_,
                        v_a_4290_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4302_) == 0 {
                    let mut v_a_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_a_4303_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                    crate::leanh::lean_inc(v_a_4303_);
                    crate::leanh::lean_dec_ref_known(v___x_4302_, 1);
                    v___x_4304_ = l_Lean_Meta_Grind_getNormTheorems___closed__9;
                    v___x_4305_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_4303_, v___x_4304_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
                    if crate::leanh::lean_obj_tag(v___x_4305_) == 0 {
                        let mut v_a_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_a_4306_ = crate::leanh::lean_ctor_get(v___x_4305_, 0);
                        crate::leanh::lean_inc(v_a_4306_);
                        crate::leanh::lean_dec_ref_known(v___x_4305_, 1);
                        v___x_4307_ = l_Lean_Meta_Grind_getNormTheorems___closed__11;
                        v___x_4308_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_4306_, v___x_4307_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
                        return v___x_4308_;
                    } else {
                        return v___x_4305_;
                    }
                } else {
                    return v___x_4302_;
                }
            } else {
                return v___x_4299_;
            }
        } else {
            return v___x_4296_;
        }
    } else {
        return v___x_4293_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_getNormTheorems___boxed(
    mut v_a_4309_: *mut crate::leanh::LeanObject,
    mut v_a_4310_: *mut crate::leanh::LeanObject,
    mut v_a_4311_: *mut crate::leanh::LeanObject,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
    mut v_a_4313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4314_ = l_Lean_Meta_Grind_getNormTheorems(v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
    crate::leanh::lean_dec(v_a_4312_);
    crate::leanh::lean_dec_ref(v_a_4311_);
    crate::leanh::lean_dec(v_a_4310_);
    crate::leanh::lean_dec_ref(v_a_4309_);
    return v_res_4314_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimpContext(
    mut v_config_4315_: *mut crate::leanh::LeanObject,
    mut v_a_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
    mut v_a_4318_: *mut crate::leanh::LeanObject,
    mut v_a_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDelta_4325_: u8 = 0;
    let mut v_zeta_4326_: u8 = 0;
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: u8 = 0;
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_a_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4350_: u8 = 0;
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4321_ =
                    l_Lean_Meta_Grind_getNormTheorems(v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_);
                if crate::leanh::lean_obj_tag(v___x_4321_) == 0 {
                    v_a_4322_ = crate::leanh::lean_ctor_get(v___x_4321_, 0);
                    crate::leanh::lean_inc(v_a_4322_);
                    crate::leanh::lean_dec_ref_known(v___x_4321_, 1);
                    v___x_4323_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_4319_);
                    if crate::leanh::lean_obj_tag(v___x_4323_) == 0 {
                        v_a_4324_ = crate::leanh::lean_ctor_get(v___x_4323_, 0);
                        crate::leanh::lean_inc(v_a_4324_);
                        crate::leanh::lean_dec_ref_known(v___x_4323_, 1);
                        v_zetaDelta_4325_ = crate::leanh::lean_ctor_get_uint8(
                            v_config_4315_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 19)
                                as u32,
                        );
                        v_zeta_4326_ = crate::leanh::lean_ctor_get_uint8(
                            v_config_4315_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 20)
                                as u32,
                        );
                        v___x_4327_ = crate::leanh::lean_unsigned_to_nat(100000);
                        v___x_4328_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_4329_ = 0;
                        v___x_4330_ = 1;
                        v___x_4331_ = 0;
                        v___x_4332_ = crate::leanh::lean_box(0);
                        v___x_4333_ = crate::leanh::lean_alloc_ctor(0, 3, (29) as u32);
                        crate::leanh::lean_ctor_set(v___x_4333_, 0, v___x_4327_);
                        crate::leanh::lean_ctor_set(v___x_4333_, 1, v___x_4328_);
                        crate::leanh::lean_ctor_set(v___x_4333_, 2, v___x_4332_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                            v_zeta_4326_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
                            v___x_4331_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 7) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 9) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 10) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 11) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 12) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 13) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 14) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 15) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                            v_zetaDelta_4325_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 17) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 18) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 19) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 20) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 21) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 22) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 23) as u32,
                            v___x_4330_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 24) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 26) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 27) as u32,
                            v___x_4329_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 28) as u32,
                            v___x_4329_,
                        );
                        v___x_4334_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4335_ = lean_mk_empty_array_with_capacity(v___x_4334_);
                        v___x_4336_ = lean_array_push(v___x_4335_, v_a_4322_);
                        v___x_4337_ = l_Lean_Options_empty;
                        v___x_4338_ = l_Lean_Meta_Simp_mkContext___redArg(
                            v___x_4333_,
                            v___x_4336_,
                            v_a_4324_,
                            v___x_4337_,
                            v_a_4316_,
                            v_a_4318_,
                            v_a_4319_,
                        );
                        return v___x_4338_;
                    } else {
                        crate::leanh::lean_dec(v_a_4322_);
                        v_a_4339_ = crate::leanh::lean_ctor_get(v___x_4323_, 0);
                        v_isSharedCheck_4346_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4323_)) as u8;
                        if v_isSharedCheck_4346_ == 0 {
                            v___x_4341_ = v___x_4323_;
                            v_isShared_4342_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4339_);
                            crate::leanh::lean_dec(v___x_4323_);
                            v___x_4341_ = crate::leanh::lean_box(0);
                            v_isShared_4342_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_4347_ = crate::leanh::lean_ctor_get(v___x_4321_, 0);
                    v_isSharedCheck_4354_ = (!crate::leanh::lean_is_exclusive(v___x_4321_)) as u8;
                    if v_isSharedCheck_4354_ == 0 {
                        v___x_4349_ = v___x_4321_;
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4347_);
                        crate::leanh::lean_dec(v___x_4321_);
                        v___x_4349_ = crate::leanh::lean_box(0);
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4342_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
                    v___x_4344_ = v_reuseFailAlloc_4345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4344_;
            }
            3 => {
                if v_isShared_4350_ == 0 {
                    v___x_4352_ = v___x_4349_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
                    v___x_4352_ = v_reuseFailAlloc_4353_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getSimpContext___boxed(
    mut v_config_4355_: *mut crate::leanh::LeanObject,
    mut v_a_4356_: *mut crate::leanh::LeanObject,
    mut v_a_4357_: *mut crate::leanh::LeanObject,
    mut v_a_4358_: *mut crate::leanh::LeanObject,
    mut v_a_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4361_ = l_Lean_Meta_Grind_getSimpContext(
        v_config_4355_,
        v_a_4356_,
        v_a_4357_,
        v_a_4358_,
        v_a_4359_,
    );
    crate::leanh::lean_dec(v_a_4359_);
    crate::leanh::lean_dec_ref(v_a_4358_);
    crate::leanh::lean_dec(v_a_4357_);
    crate::leanh::lean_dec_ref(v_a_4356_);
    crate::leanh::lean_dec_ref(v_config_4355_);
    return v_res_4361_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4362_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4362_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4363_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__0_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__0,
    );
    v___x_4364_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4364_, 0, v___x_4363_);
    return v___x_4364_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4365_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4366_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__1,
    );
    v___x_4367_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4367_, 0, v___x_4366_);
    crate::leanh::lean_ctor_set(v___x_4367_, 1, v___x_4365_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4368_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4369_ = lean_mk_empty_array_with_capacity(v___x_4368_);
    v___x_4370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4370_, 0, v___x_4369_);
    return v___x_4370_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4371_: usize = 0;
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4371_ = 5usize;
    v___x_4372_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4373_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4374_ = lean_mk_empty_array_with_capacity(v___x_4373_);
    v___x_4375_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__3_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__3,
    );
    v___x_4376_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4376_, 0, v___x_4375_);
    crate::leanh::lean_ctor_set(v___x_4376_, 1, v___x_4374_);
    crate::leanh::lean_ctor_set(v___x_4376_, 2, v___x_4372_);
    crate::leanh::lean_ctor_set(v___x_4376_, 3, v___x_4372_);
    crate::leanh::lean_ctor_set_usize(v___x_4376_, 4, v___x_4371_);
    return v___x_4376_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4377_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__4_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__4,
    );
    v___x_4378_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__1,
    );
    v___x_4379_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4379_, 0, v___x_4378_);
    crate::leanh::lean_ctor_set(v___x_4379_, 1, v___x_4378_);
    crate::leanh::lean_ctor_set(v___x_4379_, 2, v___x_4378_);
    crate::leanh::lean_ctor_set(v___x_4379_, 3, v___x_4377_);
    return v___x_4379_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__5_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__5,
    );
    v___x_4381_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__2_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__2,
    );
    v___x_4382_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4382_, 0, v___x_4381_);
    crate::leanh::lean_ctor_set(v___x_4382_, 1, v___x_4380_);
    return v___x_4382_;
}
pub unsafe fn lean_grind_normalize(
    mut v_e_4383_: *mut crate::leanh::LeanObject,
    mut v_config_4384_: *mut crate::leanh::LeanObject,
    mut v_a_4385_: *mut crate::leanh::LeanObject,
    mut v_a_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v_fst_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v_a_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v_a_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_a_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4426_: u8 = 0;
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4390_ = l_Lean_Meta_Grind_getSimpContext(
                    v_config_4384_,
                    v_a_4385_,
                    v_a_4386_,
                    v_a_4387_,
                    v_a_4388_,
                );
                crate::leanh::lean_dec_ref(v_config_4384_);
                if crate::leanh::lean_obj_tag(v___x_4390_) == 0 {
                    v_a_4391_ = crate::leanh::lean_ctor_get(v___x_4390_, 0);
                    crate::leanh::lean_inc(v_a_4391_);
                    crate::leanh::lean_dec_ref_known(v___x_4390_, 1);
                    v___x_4392_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_4387_, v_a_4388_);
                    if crate::leanh::lean_obj_tag(v___x_4392_) == 0 {
                        v_a_4393_ = crate::leanh::lean_ctor_get(v___x_4392_, 0);
                        crate::leanh::lean_inc(v_a_4393_);
                        crate::leanh::lean_dec_ref_known(v___x_4392_, 1);
                        v___x_4394_ = crate::leanh::lean_box(0);
                        v___x_4395_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_normalizeImp___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_normalizeImp___closed__6,
                        );
                        v___x_4396_ = l_Lean_Meta_simp(
                            v_e_4383_,
                            v_a_4391_,
                            v_a_4393_,
                            v___x_4394_,
                            v___x_4395_,
                            v_a_4385_,
                            v_a_4386_,
                            v_a_4387_,
                            v_a_4388_,
                        );
                        crate::leanh::lean_dec(v_a_4388_);
                        crate::leanh::lean_dec_ref(v_a_4387_);
                        crate::leanh::lean_dec(v_a_4386_);
                        crate::leanh::lean_dec_ref(v_a_4385_);
                        if crate::leanh::lean_obj_tag(v___x_4396_) == 0 {
                            v_a_4397_ = crate::leanh::lean_ctor_get(v___x_4396_, 0);
                            v_isSharedCheck_4406_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4396_)) as u8;
                            if v_isSharedCheck_4406_ == 0 {
                                v___x_4399_ = v___x_4396_;
                                v_isShared_4400_ = v_isSharedCheck_4406_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4397_);
                                crate::leanh::lean_dec(v___x_4396_);
                                v___x_4399_ = crate::leanh::lean_box(0);
                                v_isShared_4400_ = v_isSharedCheck_4406_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4407_ = crate::leanh::lean_ctor_get(v___x_4396_, 0);
                            v_isSharedCheck_4414_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4396_)) as u8;
                            if v_isSharedCheck_4414_ == 0 {
                                v___x_4409_ = v___x_4396_;
                                v_isShared_4410_ = v_isSharedCheck_4414_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4407_);
                                crate::leanh::lean_dec(v___x_4396_);
                                v___x_4409_ = crate::leanh::lean_box(0);
                                v_isShared_4410_ = v_isSharedCheck_4414_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4391_);
                        crate::leanh::lean_dec(v_a_4388_);
                        crate::leanh::lean_dec_ref(v_a_4387_);
                        crate::leanh::lean_dec(v_a_4386_);
                        crate::leanh::lean_dec_ref(v_a_4385_);
                        crate::leanh::lean_dec_ref(v_e_4383_);
                        v_a_4415_ = crate::leanh::lean_ctor_get(v___x_4392_, 0);
                        v_isSharedCheck_4422_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4392_)) as u8;
                        if v_isSharedCheck_4422_ == 0 {
                            v___x_4417_ = v___x_4392_;
                            v_isShared_4418_ = v_isSharedCheck_4422_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4415_);
                            crate::leanh::lean_dec(v___x_4392_);
                            v___x_4417_ = crate::leanh::lean_box(0);
                            v_isShared_4418_ = v_isSharedCheck_4422_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4388_);
                    crate::leanh::lean_dec_ref(v_a_4387_);
                    crate::leanh::lean_dec(v_a_4386_);
                    crate::leanh::lean_dec_ref(v_a_4385_);
                    crate::leanh::lean_dec_ref(v_e_4383_);
                    v_a_4423_ = crate::leanh::lean_ctor_get(v___x_4390_, 0);
                    v_isSharedCheck_4430_ = (!crate::leanh::lean_is_exclusive(v___x_4390_)) as u8;
                    if v_isSharedCheck_4430_ == 0 {
                        v___x_4425_ = v___x_4390_;
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4423_);
                        crate::leanh::lean_dec(v___x_4390_);
                        v___x_4425_ = crate::leanh::lean_box(0);
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4401_ = crate::leanh::lean_ctor_get(v_a_4397_, 0);
                crate::leanh::lean_inc(v_fst_4401_);
                crate::leanh::lean_dec(v_a_4397_);
                v_expr_4402_ = crate::leanh::lean_ctor_get(v_fst_4401_, 0);
                crate::leanh::lean_inc_ref(v_expr_4402_);
                crate::leanh::lean_dec(v_fst_4401_);
                if v_isShared_4400_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4399_, 0, v_expr_4402_);
                    v___x_4404_ = v___x_4399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_expr_4402_);
                    v___x_4404_ = v_reuseFailAlloc_4405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4404_;
            }
            3 => {
                if v_isShared_4410_ == 0 {
                    v___x_4412_ = v___x_4409_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
                    v___x_4412_ = v_reuseFailAlloc_4413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4412_;
            }
            5 => {
                if v_isShared_4418_ == 0 {
                    v___x_4420_ = v___x_4417_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
                    v___x_4420_ = v_reuseFailAlloc_4421_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4420_;
            }
            7 => {
                if v_isShared_4426_ == 0 {
                    v___x_4428_ = v___x_4425_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4429_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
                    v___x_4428_ = v_reuseFailAlloc_4429_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_normalizeImp___boxed(
    mut v_e_4431_: *mut crate::leanh::LeanObject,
    mut v_config_4432_: *mut crate::leanh::LeanObject,
    mut v_a_4433_: *mut crate::leanh::LeanObject,
    mut v_a_4434_: *mut crate::leanh::LeanObject,
    mut v_a_4435_: *mut crate::leanh::LeanObject,
    mut v_a_4436_: *mut crate::leanh::LeanObject,
    mut v_a_4437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4438_ = lean_grind_normalize(
        v_e_4431_,
        v_config_4432_,
        v_a_4433_,
        v_a_4434_,
        v_a_4435_,
        v_a_4436_,
    );
    return v_res_4438_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Norm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_SimpUtil(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_SimpUtil(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Norm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
}
