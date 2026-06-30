// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SimpUtil
// Imports: Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.ForallProp Lean.Meta.Tactic.Grind.Arith.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs.List Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core Lean.Meta.Tactic.Grind.Util Lean.Meta.Sym.Util Init.Grind.Norm Init.Grind.Config Init.ByCases Lean.Meta.Tactic.Simp.Main
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_expr_eqv,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_to_int, lean_st_ref_get,
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_usize_add,
    lean_usize_dec_lt,
};
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
pub static l_Lean_Meta_Grind_registerNormTheorems___closed__0_value:
    leanh::LeanStringObject<61> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_registerNormTheorems___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_registerNormTheorems___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_registerNormTheorems___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_registerNormTheorems___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value) as *mut leanh::LeanObject,1655553077289932752 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [98, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value) as *mut leanh::LeanObject,16093780639914376387 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value) as *mut leanh::LeanObject,9753356465987597394 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value) as *mut leanh::LeanObject,4342836574150310743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value) as *mut leanh::LeanObject,15998082856370921488 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value) as *mut leanh::LeanObject,6148012076188572320 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value) as *mut leanh::LeanObject,13145409667090857818 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__1_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            11870096045526947150 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__7_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            907667957179513571 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__10_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__11_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__12_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__13_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__12_value)
                as *mut leanh::LeanObject,
            11584624889955424335 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__15_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__15_value)
                as *mut leanh::LeanObject,
            6518306046597794916 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__18_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__19_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__18_value)
                as *mut leanh::LeanObject,
            12181656444938130656 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__20_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__20_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__21_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__21_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__20_value)
                as *mut leanh::LeanObject,
            9255189395584251158 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__23_value: leanh::LeanStringObject<
    16,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__23_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__24_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__23_value)
                as *mut leanh::LeanObject,
            12040479670535018831 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__24_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__26_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__26_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__27_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__26_value)
                as *mut leanh::LeanObject,
            3966638278125175059 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__29_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__29_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__30_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__30_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__30_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__29_value)
                as *mut leanh::LeanObject,
            15761733860085307253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__30_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut leanh::LeanObject,15218882539576375456 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject,8256812394612487643 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__2_value) as *mut leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: leanh::LeanArrayObject<4> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            8391571994004792969 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            18356704233129443855 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            14630272000144361786 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 68, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut leanh::LeanObject,15218882539576375456 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut leanh::LeanObject,11972642169564782543 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value) as *mut leanh::LeanObject,((( 5 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: leanh::LeanArrayObject<6> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            16612019923665488825 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            5086165725197901121 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__4_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            1910603056246669445 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__6_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__6_value)
                as *mut leanh::LeanObject,
            4878178320848305550 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__9_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            14181099489592536354 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__11_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            9743492140944907313 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__13_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__14_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__15_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__13_value)
            as *mut leanh::LeanObject,
        8347582161988589016 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__15_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__14_value)
                as *mut leanh::LeanObject,
            7316284823769321069 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__16_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__16_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__17_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__16_value)
                as *mut leanh::LeanObject,
            10012160887734445444 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__19_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__20_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
                as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__21_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__22_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__21_value)
                as *mut leanh::LeanObject,
            7009148538150066493 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__22_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__25_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__25_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__26_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__21_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__26_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__26_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__25_value)
                as *mut leanh::LeanObject,
            5162611250653448781 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__26_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Grind_pushNot___redArg___closed__29_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__29_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__29_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__25_value)
                as *mut leanh::LeanObject,
            4324381115663783915 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__29_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__31_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__31: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__32_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__32_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__33_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__33_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__33_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__32_value)
                as *mut leanh::LeanObject,
            11675589336077694177 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__33_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__35_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__35_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__36_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__36_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__36_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__35_value)
                as *mut leanh::LeanObject,
            2183596451816792659 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__36_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__37_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__37: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__38_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__38_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__39_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__38_value)
                as *mut leanh::LeanObject,
            14629220074354903389 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__39_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__40_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__41_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__41: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__42_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__42: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__42_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__43_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__42_value)
                as *mut leanh::LeanObject,
            1943741726499332591 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__43: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__43_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__45_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__45: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__46_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__46: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__46_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__47_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__46_value)
                as *mut leanh::LeanObject,
            2778442929519348459 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__47: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__47_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__48_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__48: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__49_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__49: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__49_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__50_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__49_value)
                as *mut leanh::LeanObject,
            7839396180116328695 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__50: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__50_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__51_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__51: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__52_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__52: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__52_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__53_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__52_value)
                as *mut leanh::LeanObject,
            14364261837424776314 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__53: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__53_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__54_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__54: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__54_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__55_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__54_value)
                as *mut leanh::LeanObject,
            1433178546513579301 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__55: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__55_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__56_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__56: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__57_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__57: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__57_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__58_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__57_value)
                as *mut leanh::LeanObject,
            13154267707496524221 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__58: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__58_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__59_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__59: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__60_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__60: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__61_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__61: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__61_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__62_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__61_value)
                as *mut leanh::LeanObject,
            1591550254088102176 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__62: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__62_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__63_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__63: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__64_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__64: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 117, 115, 104, 78, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut leanh::LeanObject,15218882539576375456 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut leanh::LeanObject,14132401962984515005 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            7325503363791193584 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__3_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            3950801501127104890 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__6_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__6_value)
                as *mut leanh::LeanObject,
            15885495678138479146 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__9_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            14011086014131787929 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__12_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__13_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__12_value)
                as *mut leanh::LeanObject,
            8641488168956777649 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__15_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__15_value)
                as *mut leanh::LeanObject,
            3037741586801491095 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__18_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__19_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__18_value)
                as *mut leanh::LeanObject,
            7030941873239652894 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 79, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut leanh::LeanObject,15218882539576375456 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut leanh::LeanObject,11712137666541898468 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__10_value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: leanh::LeanArrayObject<3> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0: u64 = 0;
pub static l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value)
                as *mut leanh::LeanObject,
            8738205681931236784 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 69, 113, 67, 104, 101, 97, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut leanh::LeanObject,15218882539576375456 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value) as *mut leanh::LeanObject,7640757303824383266 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [117, 110, 102, 111, 108, 100, 82, 101, 100, 117, 99, 105, 98, 108, 101, 83, 105, 109, 112, 114, 111, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut leanh::LeanObject,15218882539576375456 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut leanh::LeanObject,18075408319424519475 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: leanh::LeanArrayObject<1> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        4445492996492257536 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        233589347272681201 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__0_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getNormTheorems___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__1_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getNormTheorems___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__0_value)
                as *mut leanh::LeanObject,
            1755019837031360842 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__1_value)
                as *mut leanh::LeanObject,
            5555145617058846791 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__3_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getNormTheorems___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__4_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getNormTheorems___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__3_value)
                as *mut leanh::LeanObject,
            2272833755566510320 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__4_value)
                as *mut leanh::LeanObject,
            9426339939459091439 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__6_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getNormTheorems___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
                as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__6_value)
                as *mut leanh::LeanObject,
            8075995802451307795 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__8_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getNormTheorems___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__9_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__8_value)
                as *mut leanh::LeanObject,
            10425341760733586335 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__10_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_getNormTheorems___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__10_value)
                as *mut leanh::LeanObject,
            6695605208187598753 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_normalizeImp___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_normalizeImp___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(
    mut v_x_2220_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2221_: u8 = 0;
    v___x_2221_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2220_);
    return v___x_2221_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(
    mut v_x_2222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2223_: u8 = 0;
    let mut v_r_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2223_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v_x_2222_);
    leanh::lean_dec_ref(v_x_2222_);
    v_r_2224_ = leanh::lean_box((v_res_2223_) as usize);
    return v_r_2224_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(
    mut v_00_u03b2_2225_: *mut leanh::LeanObject,
    mut v_x_2226_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2227_: u8 = 0;
    v___x_2227_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2226_);
    return v___x_2227_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(
    mut v_00_u03b2_2228_: *mut leanh::LeanObject,
    mut v_x_2229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2230_: u8 = 0;
    let mut v_r_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2230_ =
        l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(
            v_00_u03b2_2228_,
            v_x_2229_,
        );
    leanh::lean_dec_ref(v_x_2229_);
    v_r_2231_ = leanh::lean_box((v_res_2230_) as usize);
    return v_r_2231_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(
    mut v_msgData_2232_: *mut leanh::LeanObject,
    mut v___y_2233_: *mut leanh::LeanObject,
    mut v___y_2234_: *mut leanh::LeanObject,
    mut v___y_2235_: *mut leanh::LeanObject,
    mut v___y_2236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = lean_st_ref_get(v___y_2236_);
    v_env_2239_ = leanh::lean_ctor_get(v___x_2238_, 0);
    leanh::lean_inc_ref(v_env_2239_);
    leanh::lean_dec(v___x_2238_);
    v___x_2240_ = lean_st_ref_get(v___y_2234_);
    v_mctx_2241_ = leanh::lean_ctor_get(v___x_2240_, 0);
    leanh::lean_inc_ref(v_mctx_2241_);
    leanh::lean_dec(v___x_2240_);
    v_lctx_2242_ = leanh::lean_ctor_get(v___y_2233_, 2);
    v_options_2243_ = leanh::lean_ctor_get(v___y_2235_, 2);
    leanh::lean_inc_ref(v_options_2243_);
    leanh::lean_inc_ref(v_lctx_2242_);
    v___x_2244_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2244_, 0, v_env_2239_);
    leanh::lean_ctor_set(v___x_2244_, 1, v_mctx_2241_);
    leanh::lean_ctor_set(v___x_2244_, 2, v_lctx_2242_);
    leanh::lean_ctor_set(v___x_2244_, 3, v_options_2243_);
    v___x_2245_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    leanh::lean_ctor_set(v___x_2245_, 1, v_msgData_2232_);
    v___x_2246_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2246_, 0, v___x_2245_);
    return v___x_2246_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3___boxed(
    mut v_msgData_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(v_msgData_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
    leanh::lean_dec(v___y_2251_);
    leanh::lean_dec_ref(v___y_2250_);
    leanh::lean_dec(v___y_2249_);
    leanh::lean_dec_ref(v___y_2248_);
    return v_res_2253_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(
    mut v_msg_2254_: *mut leanh::LeanObject,
    mut v___y_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
    mut v___y_2257_: *mut leanh::LeanObject,
    mut v___y_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2260_ = leanh::lean_ctor_get(v___y_2257_, 5);
                v___x_2261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(v_msg_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
                v_a_2262_ = leanh::lean_ctor_get(v___x_2261_, 0);
                v_isSharedCheck_2270_ = (!leanh::lean_is_exclusive(v___x_2261_)) as u8;
                if v_isSharedCheck_2270_ == 0 {
                    v___x_2264_ = v___x_2261_;
                    v_isShared_2265_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2262_);
                    leanh::lean_dec(v___x_2261_);
                    v___x_2264_ = leanh::lean_box(0);
                    v_isShared_2265_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2260_);
                v___x_2266_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2266_, 0, v_ref_2260_);
                leanh::lean_ctor_set(v___x_2266_, 1, v_a_2262_);
                if v_isShared_2265_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2264_, 1);
                    leanh::lean_ctor_set(v___x_2264_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
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
    mut v_msg_2271_: *mut leanh::LeanObject,
    mut v___y_2272_: *mut leanh::LeanObject,
    mut v___y_2273_: *mut leanh::LeanObject,
    mut v___y_2274_: *mut leanh::LeanObject,
    mut v___y_2275_: *mut leanh::LeanObject,
    mut v___y_2276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(
        v_msg_2271_,
        v___y_2272_,
        v___y_2273_,
        v___y_2274_,
        v___y_2275_,
    );
    leanh::lean_dec(v___y_2275_);
    leanh::lean_dec_ref(v___y_2274_);
    leanh::lean_dec(v___y_2273_);
    leanh::lean_dec_ref(v___y_2272_);
    return v_res_2277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(
    mut v_as_2278_: *mut leanh::LeanObject,
    mut v_sz_2279_: usize,
    mut v_i_2280_: usize,
    mut v_b_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
    mut v___y_2283_: *mut leanh::LeanObject,
    mut v___y_2284_: *mut leanh::LeanObject,
    mut v___y_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: usize = 0;
    let mut v___x_2297_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2287_ = lean_usize_dec_lt(v_i_2280_, v_sz_2279_);
                if v___x_2287_ == 0 {
                    v___x_2288_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2288_, 0, v_b_2281_);
                    return v___x_2288_;
                } else {
                    v___x_2289_ = l_Lean_Meta_Grind_normExt;
                    v_a_2290_ = lean_array_uget_borrowed(v_as_2278_, v_i_2280_);
                    v___x_2291_ = 0;
                    v___x_2292_ = 0;
                    v___x_2293_ = leanh::lean_unsigned_to_nat(1000);
                    leanh::lean_inc(v_a_2290_);
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
                    if leanh::lean_obj_tag(v___x_2294_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2294_, 1);
                        v___x_2295_ = leanh::lean_box(0);
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
    mut v_as_2299_: *mut leanh::LeanObject,
    mut v_sz_2300_: *mut leanh::LeanObject,
    mut v_i_2301_: *mut leanh::LeanObject,
    mut v_b_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
    mut v___y_2304_: *mut leanh::LeanObject,
    mut v___y_2305_: *mut leanh::LeanObject,
    mut v___y_2306_: *mut leanh::LeanObject,
    mut v___y_2307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2308_: usize = 0;
    let mut v_i_boxed_2309_: usize = 0;
    let mut v_res_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2308_ = leanh::lean_unbox_usize(v_sz_2300_);
    leanh::lean_dec(v_sz_2300_);
    v_i_boxed_2309_ = leanh::lean_unbox_usize(v_i_2301_);
    leanh::lean_dec(v_i_2301_);
    v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_as_2299_, v_sz_boxed_2308_, v_i_boxed_2309_, v_b_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
    leanh::lean_dec(v___y_2306_);
    leanh::lean_dec_ref(v___y_2305_);
    leanh::lean_dec(v___y_2304_);
    leanh::lean_dec_ref(v___y_2303_);
    leanh::lean_dec_ref(v_as_2299_);
    return v_res_2310_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(
    mut v_as_2311_: *mut leanh::LeanObject,
    mut v_sz_2312_: usize,
    mut v_i_2313_: usize,
    mut v_b_2314_: *mut leanh::LeanObject,
    mut v___y_2315_: *mut leanh::LeanObject,
    mut v___y_2316_: *mut leanh::LeanObject,
    mut v___y_2317_: *mut leanh::LeanObject,
    mut v___y_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2320_ = lean_usize_dec_lt(v_i_2313_, v_sz_2312_);
                if v___x_2320_ == 0 {
                    v___x_2321_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2321_, 0, v_b_2314_);
                    return v___x_2321_;
                } else {
                    v___x_2322_ = l_Lean_Meta_Grind_normExt;
                    v_a_2323_ = lean_array_uget_borrowed(v_as_2311_, v_i_2313_);
                    v___x_2324_ = 0;
                    v___x_2325_ = 0;
                    v___x_2326_ = leanh::lean_unsigned_to_nat(1000);
                    leanh::lean_inc(v_a_2323_);
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
                    if leanh::lean_obj_tag(v___x_2327_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2327_, 1);
                        v___x_2328_ = leanh::lean_box(0);
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
    mut v_as_2332_: *mut leanh::LeanObject,
    mut v_sz_2333_: *mut leanh::LeanObject,
    mut v_i_2334_: *mut leanh::LeanObject,
    mut v_b_2335_: *mut leanh::LeanObject,
    mut v___y_2336_: *mut leanh::LeanObject,
    mut v___y_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2341_: usize = 0;
    let mut v_i_boxed_2342_: usize = 0;
    let mut v_res_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2341_ = leanh::lean_unbox_usize(v_sz_2333_);
    leanh::lean_dec(v_sz_2333_);
    v_i_boxed_2342_ = leanh::lean_unbox_usize(v_i_2334_);
    leanh::lean_dec(v_i_2334_);
    v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_as_2332_, v_sz_boxed_2341_, v_i_boxed_2342_, v_b_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
    leanh::lean_dec(v___y_2339_);
    leanh::lean_dec_ref(v___y_2338_);
    leanh::lean_dec(v___y_2337_);
    leanh::lean_dec_ref(v___y_2336_);
    leanh::lean_dec_ref(v_as_2332_);
    return v_res_2343_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2345_ = l_Lean_Meta_Grind_registerNormTheorems___closed__0;
    v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
    return v___x_2346_;
}
pub unsafe fn l_Lean_Meta_Grind_registerNormTheorems(
    mut v_preDeclNames_2347_: *mut leanh::LeanObject,
    mut v_postDeclNames_2348_: *mut leanh::LeanObject,
    mut v_a_2349_: *mut leanh::LeanObject,
    mut v_a_2350_: *mut leanh::LeanObject,
    mut v_a_2351_: *mut leanh::LeanObject,
    mut v_a_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2360_: usize = 0;
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2363_: usize = 0;
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2367_: u8 = 0;
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_unused_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmaNames_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2373_ = l_Lean_Meta_Grind_normExt;
                v___x_2374_ =
                    l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_2373_, v_a_2352_);
                if leanh::lean_obj_tag(v___x_2374_) == 0 {
                    v_a_2375_ = leanh::lean_ctor_get(v___x_2374_, 0);
                    leanh::lean_inc(v_a_2375_);
                    leanh::lean_dec_ref_known(v___x_2374_, 1);
                    v_lemmaNames_2376_ = leanh::lean_ctor_get(v_a_2375_, 2);
                    leanh::lean_inc_ref(v_lemmaNames_2376_);
                    leanh::lean_dec(v_a_2375_);
                    v___x_2377_ =
                        l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_lemmaNames_2376_);
                    leanh::lean_dec_ref(v_lemmaNames_2376_);
                    if v___x_2377_ == 0 {
                        v___x_2378_ = leanh::lean_obj_once(
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
                    v_a_2380_ = leanh::lean_ctor_get(v___x_2374_, 0);
                    v_isSharedCheck_2387_ = (!leanh::lean_is_exclusive(v___x_2374_)) as u8;
                    if v_isSharedCheck_2387_ == 0 {
                        v___x_2382_ = v___x_2374_;
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2380_);
                        leanh::lean_dec(v___x_2374_);
                        v___x_2382_ = leanh::lean_box(0);
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2359_ = leanh::lean_box(0);
                v_sz_2360_ = lean_array_size(v_preDeclNames_2347_);
                v___x_2361_ = 0usize;
                v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_preDeclNames_2347_, v_sz_2360_, v___x_2361_, v___x_2359_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
                if leanh::lean_obj_tag(v___x_2362_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2362_, 1);
                    v_sz_2363_ = lean_array_size(v_postDeclNames_2348_);
                    v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_postDeclNames_2348_, v_sz_2363_, v___x_2361_, v___x_2359_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
                    if leanh::lean_obj_tag(v___x_2364_) == 0 {
                        v_isSharedCheck_2371_ =
                            (!leanh::lean_is_exclusive(v___x_2364_)) as u8;
                        if v_isSharedCheck_2371_ == 0 {
                            v_unused_2372_ = leanh::lean_ctor_get(v___x_2364_, 0);
                            leanh::lean_dec(v_unused_2372_);
                            v___x_2366_ = v___x_2364_;
                            v_isShared_2367_ = v_isSharedCheck_2371_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2364_);
                            v___x_2366_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2366_, 0, v___x_2359_);
                    v___x_2369_ = v___x_2366_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2359_);
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
                    v_reuseFailAlloc_2386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
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
    mut v_preDeclNames_2388_: *mut leanh::LeanObject,
    mut v_postDeclNames_2389_: *mut leanh::LeanObject,
    mut v_a_2390_: *mut leanh::LeanObject,
    mut v_a_2391_: *mut leanh::LeanObject,
    mut v_a_2392_: *mut leanh::LeanObject,
    mut v_a_2393_: *mut leanh::LeanObject,
    mut v_a_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Lean_Meta_Grind_registerNormTheorems(
        v_preDeclNames_2388_,
        v_postDeclNames_2389_,
        v_a_2390_,
        v_a_2391_,
        v_a_2392_,
        v_a_2393_,
    );
    leanh::lean_dec(v_a_2393_);
    leanh::lean_dec_ref(v_a_2392_);
    leanh::lean_dec(v_a_2391_);
    leanh::lean_dec_ref(v_a_2390_);
    leanh::lean_dec_ref(v_postDeclNames_2389_);
    leanh::lean_dec_ref(v_preDeclNames_2388_);
    return v_res_2395_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(
    mut v_00_u03b1_2396_: *mut leanh::LeanObject,
    mut v_msg_2397_: *mut leanh::LeanObject,
    mut v___y_2398_: *mut leanh::LeanObject,
    mut v___y_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2404_: *mut leanh::LeanObject,
    mut v_msg_2405_: *mut leanh::LeanObject,
    mut v___y_2406_: *mut leanh::LeanObject,
    mut v___y_2407_: *mut leanh::LeanObject,
    mut v___y_2408_: *mut leanh::LeanObject,
    mut v___y_2409_: *mut leanh::LeanObject,
    mut v___y_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(
        v_00_u03b1_2404_,
        v_msg_2405_,
        v___y_2406_,
        v___y_2407_,
        v___y_2408_,
        v___y_2409_,
    );
    leanh::lean_dec(v___y_2409_);
    leanh::lean_dec_ref(v___y_2408_);
    leanh::lean_dec(v___y_2407_);
    leanh::lean_dec_ref(v___y_2406_);
    return v_res_2411_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(
    mut v_declName_2435_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_2437_: u8 = 0;
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u8 = 0;
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_declName_2448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2449_: u8 = 0;
    let mut v_r_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2449_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(
        v_declName_2448_,
    );
    leanh::lean_dec(v_declName_2448_);
    v_r_2450_ = leanh::lean_box((v_res_2449_) as usize);
    return v_r_2450_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = leanh::lean_box(0);
    v___x_2462_ = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
    v___x_2463_ = l_Lean_mkConst(v___x_2462_, v___x_2461_);
    return v___x_2463_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2467_ = leanh::lean_box(0);
    v___x_2468_ = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
    v___x_2469_ = l_Lean_mkConst(v___x_2468_, v___x_2467_);
    return v___x_2469_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14() -> *mut leanh::LeanObject
{
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = leanh::lean_box(0);
    v___x_2478_ = l_Lean_Meta_Grind_simpEq___redArg___closed__13;
    v___x_2479_ = l_Lean_mkConst(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17() -> *mut leanh::LeanObject
{
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ = leanh::lean_box(0);
    v___x_2486_ = l_Lean_Meta_Grind_simpEq___redArg___closed__16;
    v___x_2487_ = l_Lean_mkConst(v___x_2486_, v___x_2485_);
    return v___x_2487_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22() -> *mut leanh::LeanObject
{
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2495_ = leanh::lean_box(0);
    v___x_2496_ = l_Lean_Meta_Grind_simpEq___redArg___closed__21;
    v___x_2497_ = l_Lean_mkConst(v___x_2496_, v___x_2495_);
    return v___x_2497_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25() -> *mut leanh::LeanObject
{
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2503_ = leanh::lean_box(0);
    v___x_2504_ = l_Lean_Meta_Grind_simpEq___redArg___closed__24;
    v___x_2505_ = l_Lean_mkConst(v___x_2504_, v___x_2503_);
    return v___x_2505_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28() -> *mut leanh::LeanObject
{
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2511_ = leanh::lean_box(0);
    v___x_2512_ = l_Lean_Meta_Grind_simpEq___redArg___closed__27;
    v___x_2513_ = l_Lean_mkConst(v___x_2512_, v___x_2511_);
    return v___x_2513_;
}
pub unsafe fn l_Lean_Meta_Grind_simpEq___redArg(
    mut v_e_2518_: *mut leanh::LeanObject,
    mut v_a_2519_: *mut leanh::LeanObject,
    mut v_a_2520_: *mut leanh::LeanObject,
    mut v_a_2521_: *mut leanh::LeanObject,
    mut v_a_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2528_: u8 = 0;
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v_arg_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    let mut v_arg_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v_arg_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2550_: u8 = 0;
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: u8 = 0;
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: u8 = 0;
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: u8 = 0;
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2595_: u8 = 0;
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut v_a_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut v___y_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2627_: u8 = 0;
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2638_: u8 = 0;
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: u8 = 0;
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u8 = 0;
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: u8 = 0;
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_a_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2659_: u8 = 0;
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2663_: u8 = 0;
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut v_a_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2524_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2518_, v_a_2520_);
                if leanh::lean_obj_tag(v___x_2524_) == 0 {
                    v_a_2525_ = leanh::lean_ctor_get(v___x_2524_, 0);
                    v_isSharedCheck_2664_ = (!leanh::lean_is_exclusive(v___x_2524_)) as u8;
                    if v_isSharedCheck_2664_ == 0 {
                        v___x_2527_ = v___x_2524_;
                        v_isShared_2528_ = v_isSharedCheck_2664_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2525_);
                        leanh::lean_dec(v___x_2524_);
                        v___x_2527_ = leanh::lean_box(0);
                        v_isShared_2528_ = v_isSharedCheck_2664_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2665_ = leanh::lean_ctor_get(v___x_2524_, 0);
                    v_isSharedCheck_2672_ = (!leanh::lean_is_exclusive(v___x_2524_)) as u8;
                    if v_isSharedCheck_2672_ == 0 {
                        v___x_2667_ = v___x_2524_;
                        v_isShared_2668_ = v_isSharedCheck_2672_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2665_);
                        leanh::lean_dec(v___x_2524_);
                        v___x_2667_ = leanh::lean_box(0);
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
                    leanh::lean_dec_ref(v___x_2534_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2536_ = leanh::lean_ctor_get(v___x_2534_, 1);
                    leanh::lean_inc_ref(v_arg_2536_);
                    v___x_2537_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2534_);
                    v___x_2538_ = l_Lean_Expr_isApp(v___x_2537_);
                    if v___x_2538_ == 0 {
                        leanh::lean_dec_ref(v___x_2537_);
                        leanh::lean_dec_ref(v_arg_2536_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2539_ = leanh::lean_ctor_get(v___x_2537_, 1);
                        leanh::lean_inc_ref(v_arg_2539_);
                        v___x_2540_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2537_);
                        v___x_2541_ = l_Lean_Expr_isApp(v___x_2540_);
                        if v___x_2541_ == 0 {
                            leanh::lean_dec_ref(v___x_2540_);
                            leanh::lean_dec_ref(v_arg_2539_);
                            leanh::lean_dec_ref(v_arg_2536_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2542_ = leanh::lean_ctor_get(v___x_2540_, 1);
                            leanh::lean_inc_ref(v_arg_2542_);
                            v___x_2543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2540_);
                            v___x_2544_ = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
                            v___x_2545_ = l_Lean_Expr_isConstOf(v___x_2543_, v___x_2544_);
                            if v___x_2545_ == 0 {
                                leanh::lean_dec_ref(v___x_2543_);
                                leanh::lean_dec_ref(v_arg_2542_);
                                leanh::lean_dec_ref(v_arg_2539_);
                                leanh::lean_dec_ref(v_arg_2536_);
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2527_);
                                leanh::lean_inc_ref(v_arg_2542_);
                                v___x_2546_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                    v_arg_2542_,
                                    v_a_2520_,
                                );
                                if leanh::lean_obj_tag(v___x_2546_) == 0 {
                                    v_a_2547_ = leanh::lean_ctor_get(v___x_2546_, 0);
                                    v_isSharedCheck_2655_ =
                                        (!leanh::lean_is_exclusive(v___x_2546_)) as u8;
                                    if v_isSharedCheck_2655_ == 0 {
                                        v___x_2549_ = v___x_2546_;
                                        v_isShared_2550_ = v_isSharedCheck_2655_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2547_);
                                        leanh::lean_dec(v___x_2546_);
                                        v___x_2549_ = leanh::lean_box(0);
                                        v_isShared_2550_ = v_isSharedCheck_2655_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_2543_);
                                    leanh::lean_dec_ref(v_arg_2542_);
                                    leanh::lean_dec_ref(v_arg_2539_);
                                    leanh::lean_dec_ref(v_arg_2536_);
                                    v_a_2656_ = leanh::lean_ctor_get(v___x_2546_, 0);
                                    v_isSharedCheck_2663_ =
                                        (!leanh::lean_is_exclusive(v___x_2546_)) as u8;
                                    if v_isSharedCheck_2663_ == 0 {
                                        v___x_2658_ = v___x_2546_;
                                        v_isShared_2659_ = v_isSharedCheck_2663_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2656_);
                                        leanh::lean_dec(v___x_2546_);
                                        v___x_2658_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2527_, 0, v___x_2530_);
                    v___x_2532_ = v___x_2527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
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
                leanh::lean_dec_ref(v___x_2551_);
                if v___x_2553_ == 0 {
                    v___x_2554_ = lean_expr_eqv(v_arg_2539_, v_arg_2536_);
                    if v___x_2554_ == 0 {
                        leanh::lean_dec_ref(v___x_2543_);
                        leanh::lean_dec_ref(v_arg_2542_);
                        v___x_2555_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpEq___redArg___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6,
                        );
                        v___x_2556_ = lean_expr_eqv(v_arg_2536_, v___x_2555_);
                        if v___x_2556_ == 0 {
                            v___x_2557_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__9_once
                                ),
                                _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9,
                            );
                            v___x_2558_ = lean_expr_eqv(v_arg_2536_, v___x_2557_);
                            leanh::lean_dec_ref(v_arg_2536_);
                            if v___x_2558_ == 0 {
                                leanh::lean_dec_ref(v_arg_2539_);
                                v___x_2559_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                if v_isShared_2550_ == 0 {
                                    leanh::lean_ctor_set(v___x_2549_, 0, v___x_2559_);
                                    v___x_2561_ = v___x_2549_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2562_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2562_,
                                        0,
                                        v___x_2559_,
                                    );
                                    v___x_2561_ = v_reuseFailAlloc_2562_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_inc_ref(v_arg_2539_);
                                v___x_2563_ = l_Lean_mkNot(v_arg_2539_);
                                v___x_2564_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_simpEq___redArg___closed__14
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_simpEq___redArg___closed__14_once
                                    ),
                                    _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14,
                                );
                                v___x_2565_ = l_Lean_Expr_app___override(v___x_2564_, v_arg_2539_);
                                v___x_2566_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2566_, 0, v___x_2565_);
                                v___x_2567_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                leanh::lean_ctor_set(v___x_2567_, 0, v___x_2563_);
                                leanh::lean_ctor_set(v___x_2567_, 1, v___x_2566_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_2567_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                        as u32,
                                    v___x_2545_,
                                );
                                v___x_2568_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2568_, 0, v___x_2567_);
                                if v_isShared_2550_ == 0 {
                                    leanh::lean_ctor_set(v___x_2549_, 0, v___x_2568_);
                                    v___x_2570_ = v___x_2549_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2571_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
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
                            leanh::lean_dec_ref(v_arg_2536_);
                            v___x_2572_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__17
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__17_once
                                ),
                                _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17,
                            );
                            leanh::lean_inc_ref(v_arg_2539_);
                            v___x_2573_ = l_Lean_Expr_app___override(v___x_2572_, v_arg_2539_);
                            v___x_2574_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2574_, 0, v___x_2573_);
                            v___x_2575_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            leanh::lean_ctor_set(v___x_2575_, 0, v_arg_2539_);
                            leanh::lean_ctor_set(v___x_2575_, 1, v___x_2574_);
                            leanh::lean_ctor_set_uint8(
                                v___x_2575_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                                v___x_2545_,
                            );
                            v___x_2576_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2576_, 0, v___x_2575_);
                            if v_isShared_2550_ == 0 {
                                leanh::lean_ctor_set(v___x_2549_, 0, v___x_2576_);
                                v___x_2578_ = v___x_2549_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_2579_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
                                v___x_2578_ = v_reuseFailAlloc_2579_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_2536_);
                        v___x_2580_ = l_Lean_Expr_constLevels_x21(v___x_2543_);
                        leanh::lean_dec_ref(v___x_2543_);
                        v___x_2581_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpEq___redArg___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6,
                        );
                        v___x_2582_ = l_Lean_Meta_Grind_simpEq___redArg___closed__19;
                        v___x_2583_ = l_Lean_mkConst(v___x_2582_, v___x_2580_);
                        v___x_2584_ = l_Lean_mkAppB(v___x_2583_, v_arg_2542_, v_arg_2539_);
                        v___x_2585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2585_, 0, v___x_2584_);
                        v___x_2586_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        leanh::lean_ctor_set(v___x_2586_, 0, v___x_2581_);
                        leanh::lean_ctor_set(v___x_2586_, 1, v___x_2585_);
                        leanh::lean_ctor_set_uint8(
                            v___x_2586_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v___x_2545_,
                        );
                        v___x_2587_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2587_, 0, v___x_2586_);
                        if v_isShared_2550_ == 0 {
                            leanh::lean_ctor_set(v___x_2549_, 0, v___x_2587_);
                            v___x_2589_ = v___x_2549_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_2590_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
                            v___x_2589_ = v_reuseFailAlloc_2590_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_2591_ = l_Lean_Expr_getAppFn(v_arg_2536_);
                    if leanh::lean_obj_tag(v___x_2591_) == 4 {
                        v_declName_2592_ = leanh::lean_ctor_get(v___x_2591_, 0);
                        leanh::lean_inc(v_declName_2592_);
                        leanh::lean_dec_ref_known(v___x_2591_, 2);
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
                        leanh::lean_dec_ref(v___x_2591_);
                        leanh::lean_dec_ref(v___x_2543_);
                        leanh::lean_dec_ref(v_arg_2542_);
                        leanh::lean_dec_ref(v_arg_2539_);
                        leanh::lean_dec_ref(v_arg_2536_);
                        v___x_2651_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        if v_isShared_2550_ == 0 {
                            leanh::lean_ctor_set(v___x_2549_, 0, v___x_2651_);
                            v___x_2653_ = v___x_2549_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_2654_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
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
                    leanh::lean_dec_ref(v___x_2543_);
                    leanh::lean_dec_ref(v_arg_2542_);
                    leanh::lean_dec_ref(v_arg_2539_);
                    leanh::lean_dec_ref(v_arg_2536_);
                    v___x_2596_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    if v_isShared_2550_ == 0 {
                        leanh::lean_ctor_set(v___x_2549_, 0, v___x_2596_);
                        v___x_2598_ = v___x_2549_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
                        v___x_2598_ = v_reuseFailAlloc_2599_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2549_);
                    v___x_2600_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__22),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpEq___redArg___closed__22_once
                        ),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22,
                    );
                    leanh::lean_inc_ref(v_arg_2539_);
                    leanh::lean_inc_ref(v_arg_2542_);
                    leanh::lean_inc_ref(v___x_2543_);
                    v___x_2601_ = l_Lean_mkApp3(v___x_2543_, v_arg_2542_, v_arg_2539_, v___x_2600_);
                    leanh::lean_inc_ref(v_arg_2536_);
                    v___x_2602_ = l_Lean_mkApp3(v___x_2543_, v_arg_2542_, v_arg_2536_, v___x_2600_);
                    v___x_2603_ = l_Lean_Meta_mkEq(
                        v___x_2601_,
                        v___x_2602_,
                        v_a_2519_,
                        v_a_2520_,
                        v_a_2521_,
                        v_a_2522_,
                    );
                    if leanh::lean_obj_tag(v___x_2603_) == 0 {
                        v_a_2604_ = leanh::lean_ctor_get(v___x_2603_, 0);
                        v_isSharedCheck_2616_ =
                            (!leanh::lean_is_exclusive(v___x_2603_)) as u8;
                        if v_isSharedCheck_2616_ == 0 {
                            v___x_2606_ = v___x_2603_;
                            v_isShared_2607_ = v_isSharedCheck_2616_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2604_);
                            leanh::lean_dec(v___x_2603_);
                            v___x_2606_ = leanh::lean_box(0);
                            v_isShared_2607_ = v_isSharedCheck_2616_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_2539_);
                        leanh::lean_dec_ref(v_arg_2536_);
                        v_a_2617_ = leanh::lean_ctor_get(v___x_2603_, 0);
                        v_isSharedCheck_2624_ =
                            (!leanh::lean_is_exclusive(v___x_2603_)) as u8;
                        if v_isSharedCheck_2624_ == 0 {
                            v___x_2619_ = v___x_2603_;
                            v_isShared_2620_ = v_isSharedCheck_2624_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2617_);
                            leanh::lean_dec(v___x_2603_);
                            v___x_2619_ = leanh::lean_box(0);
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
                v___x_2608_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__25),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__25_once),
                    _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25,
                );
                v___x_2609_ = l_Lean_mkAppB(v___x_2608_, v_arg_2539_, v_arg_2536_);
                v___x_2610_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2610_, 0, v___x_2609_);
                v___x_2611_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_2611_, 0, v_a_2604_);
                leanh::lean_ctor_set(v___x_2611_, 1, v___x_2610_);
                leanh::lean_ctor_set_uint8(
                    v___x_2611_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_2553_,
                );
                v___x_2612_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2612_, 0, v___x_2611_);
                if v_isShared_2607_ == 0 {
                    leanh::lean_ctor_set(v___x_2606_, 0, v___x_2612_);
                    v___x_2614_ = v___x_2606_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2615_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
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
                    v_reuseFailAlloc_2623_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
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
                    leanh::lean_dec(v___y_2626_);
                    if v___x_2628_ == 0 {
                        v___x_2629_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_2592_);
                        leanh::lean_dec(v_declName_2592_);
                        v___y_2595_ = v___x_2629_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v_declName_2592_);
                        v___y_2595_ = v___x_2628_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_2626_);
                    leanh::lean_dec(v_declName_2592_);
                    leanh::lean_del_object(v___x_2549_);
                    leanh::lean_inc_ref(v_arg_2539_);
                    leanh::lean_inc_ref(v_arg_2536_);
                    v___x_2630_ = l_Lean_mkApp3(v___x_2543_, v_arg_2542_, v_arg_2536_, v_arg_2539_);
                    v___x_2631_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__28),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpEq___redArg___closed__28_once
                        ),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28,
                    );
                    v___x_2632_ = l_Lean_mkAppB(v___x_2631_, v_arg_2539_, v_arg_2536_);
                    v___x_2633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2633_, 0, v___x_2632_);
                    v___x_2634_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_2634_, 0, v___x_2630_);
                    leanh::lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2634_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_2553_,
                    );
                    v___x_2635_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2635_, 0, v___x_2634_);
                    v___x_2636_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2636_, 0, v___x_2635_);
                    return v___x_2636_;
                }
            }
            16 => {
                if v___y_2638_ == 0 {
                    v___x_2639_ = l_Lean_Expr_getAppFn(v_arg_2539_);
                    if leanh::lean_obj_tag(v___x_2639_) == 4 {
                        v_declName_2640_ = leanh::lean_ctor_get(v___x_2639_, 0);
                        leanh::lean_inc(v_declName_2640_);
                        leanh::lean_dec_ref_known(v___x_2639_, 2);
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
                        leanh::lean_dec_ref(v___x_2639_);
                        leanh::lean_dec(v_declName_2592_);
                        leanh::lean_del_object(v___x_2549_);
                        leanh::lean_dec_ref(v___x_2543_);
                        leanh::lean_dec_ref(v_arg_2542_);
                        leanh::lean_dec_ref(v_arg_2539_);
                        leanh::lean_dec_ref(v_arg_2536_);
                        v___x_2644_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        v___x_2645_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2645_, 0, v___x_2644_);
                        return v___x_2645_;
                    }
                } else {
                    leanh::lean_dec(v_declName_2592_);
                    leanh::lean_del_object(v___x_2549_);
                    leanh::lean_dec_ref(v___x_2543_);
                    leanh::lean_dec_ref(v_arg_2542_);
                    leanh::lean_dec_ref(v_arg_2539_);
                    leanh::lean_dec_ref(v_arg_2536_);
                    v___x_2646_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    v___x_2647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2647_, 0, v___x_2646_);
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
                    v_reuseFailAlloc_2662_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
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
                    v_reuseFailAlloc_2671_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
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
    mut v_e_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
    mut v_a_2675_: *mut leanh::LeanObject,
    mut v_a_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
    mut v_a_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ =
        l_Lean_Meta_Grind_simpEq___redArg(v_e_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
    leanh::lean_dec(v_a_2677_);
    leanh::lean_dec_ref(v_a_2676_);
    leanh::lean_dec(v_a_2675_);
    leanh::lean_dec_ref(v_a_2674_);
    return v_res_2679_;
}
pub unsafe fn l_Lean_Meta_Grind_simpEq(
    mut v_e_2680_: *mut leanh::LeanObject,
    mut v_a_2681_: *mut leanh::LeanObject,
    mut v_a_2682_: *mut leanh::LeanObject,
    mut v_a_2683_: *mut leanh::LeanObject,
    mut v_a_2684_: *mut leanh::LeanObject,
    mut v_a_2685_: *mut leanh::LeanObject,
    mut v_a_2686_: *mut leanh::LeanObject,
    mut v_a_2687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2689_ =
        l_Lean_Meta_Grind_simpEq___redArg(v_e_2680_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
    return v___x_2689_;
}
pub unsafe fn l_Lean_Meta_Grind_simpEq___boxed(
    mut v_e_2690_: *mut leanh::LeanObject,
    mut v_a_2691_: *mut leanh::LeanObject,
    mut v_a_2692_: *mut leanh::LeanObject,
    mut v_a_2693_: *mut leanh::LeanObject,
    mut v_a_2694_: *mut leanh::LeanObject,
    mut v_a_2695_: *mut leanh::LeanObject,
    mut v_a_2696_: *mut leanh::LeanObject,
    mut v_a_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2699_ = l_Lean_Meta_Grind_simpEq(
        v_e_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_,
    );
    leanh::lean_dec(v_a_2697_);
    leanh::lean_dec_ref(v_a_2696_);
    leanh::lean_dec(v_a_2695_);
    leanh::lean_dec_ref(v_a_2694_);
    leanh::lean_dec(v_a_2693_);
    leanh::lean_dec_ref(v_a_2692_);
    leanh::lean_dec(v_a_2691_);
    return v_res_2699_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_()
-> *mut leanh::LeanObject {
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2719_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
    v___x_2720_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
    v___x_2721_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_simpEq___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2722_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2719_, v___x_2720_, v___x_2721_);
    return v___x_2722_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12____boxed(
    mut v_a_2723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2724_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_();
    return v_res_2724_;
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte___redArg(
    mut v_e_2734_: *mut leanh::LeanObject,
    mut v_a_2735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: u8 = 0;
    let mut v_arg_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    let mut v_arg_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: u8 = 0;
    let mut v_arg_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: u8 = 0;
    let mut v_arg_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v_arg_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: u8 = 0;
    let mut v_body_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: u8 = 0;
    let mut v_body_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut v_a_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2737_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2734_, v_a_2735_);
                if leanh::lean_obj_tag(v___x_2737_) == 0 {
                    v_a_2738_ = leanh::lean_ctor_get(v___x_2737_, 0);
                    v_isSharedCheck_2788_ = (!leanh::lean_is_exclusive(v___x_2737_)) as u8;
                    if v_isSharedCheck_2788_ == 0 {
                        v___x_2740_ = v___x_2737_;
                        v_isShared_2741_ = v_isSharedCheck_2788_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2738_);
                        leanh::lean_dec(v___x_2737_);
                        v___x_2740_ = leanh::lean_box(0);
                        v_isShared_2741_ = v_isSharedCheck_2788_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2789_ = leanh::lean_ctor_get(v___x_2737_, 0);
                    v_isSharedCheck_2796_ = (!leanh::lean_is_exclusive(v___x_2737_)) as u8;
                    if v_isSharedCheck_2796_ == 0 {
                        v___x_2791_ = v___x_2737_;
                        v_isShared_2792_ = v_isSharedCheck_2796_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2789_);
                        leanh::lean_dec(v___x_2737_);
                        v___x_2791_ = leanh::lean_box(0);
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
                    leanh::lean_dec_ref(v___x_2747_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2749_ = leanh::lean_ctor_get(v___x_2747_, 1);
                    leanh::lean_inc_ref(v_arg_2749_);
                    v___x_2750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2747_);
                    v___x_2751_ = l_Lean_Expr_isApp(v___x_2750_);
                    if v___x_2751_ == 0 {
                        leanh::lean_dec_ref(v___x_2750_);
                        leanh::lean_dec_ref(v_arg_2749_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2752_ = leanh::lean_ctor_get(v___x_2750_, 1);
                        leanh::lean_inc_ref(v_arg_2752_);
                        v___x_2753_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2750_);
                        v___x_2754_ = l_Lean_Expr_isApp(v___x_2753_);
                        if v___x_2754_ == 0 {
                            leanh::lean_dec_ref(v___x_2753_);
                            leanh::lean_dec_ref(v_arg_2752_);
                            leanh::lean_dec_ref(v_arg_2749_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2755_ = leanh::lean_ctor_get(v___x_2753_, 1);
                            leanh::lean_inc_ref(v_arg_2755_);
                            v___x_2756_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2753_);
                            v___x_2757_ = l_Lean_Expr_isApp(v___x_2756_);
                            if v___x_2757_ == 0 {
                                leanh::lean_dec_ref(v___x_2756_);
                                leanh::lean_dec_ref(v_arg_2755_);
                                leanh::lean_dec_ref(v_arg_2752_);
                                leanh::lean_dec_ref(v_arg_2749_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_2758_ = leanh::lean_ctor_get(v___x_2756_, 1);
                                leanh::lean_inc_ref(v_arg_2758_);
                                v___x_2759_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2756_);
                                v___x_2760_ = l_Lean_Expr_isApp(v___x_2759_);
                                if v___x_2760_ == 0 {
                                    leanh::lean_dec_ref(v___x_2759_);
                                    leanh::lean_dec_ref(v_arg_2758_);
                                    leanh::lean_dec_ref(v_arg_2755_);
                                    leanh::lean_dec_ref(v_arg_2752_);
                                    leanh::lean_dec_ref(v_arg_2749_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_2761_ = leanh::lean_ctor_get(v___x_2759_, 1);
                                    leanh::lean_inc_ref(v_arg_2761_);
                                    v___x_2762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2759_);
                                    v___x_2763_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__1;
                                    v___x_2764_ = l_Lean_Expr_isConstOf(v___x_2762_, v___x_2763_);
                                    if v___x_2764_ == 0 {
                                        leanh::lean_dec_ref(v___x_2762_);
                                        leanh::lean_dec_ref(v_arg_2761_);
                                        leanh::lean_dec_ref(v_arg_2758_);
                                        leanh::lean_dec_ref(v_arg_2755_);
                                        leanh::lean_dec_ref(v_arg_2752_);
                                        leanh::lean_dec_ref(v_arg_2749_);
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_del_object(v___x_2740_);
                                        if leanh::lean_obj_tag(v_arg_2752_) == 6 {
                                            v_body_2765_ =
                                                leanh::lean_ctor_get(v_arg_2752_, 2);
                                            leanh::lean_inc_ref(v_body_2765_);
                                            leanh::lean_dec_ref_known(v_arg_2752_, 3);
                                            v___x_2766_ = l_Lean_Expr_hasLooseBVars(v_body_2765_);
                                            if v___x_2766_ == 0 {
                                                if leanh::lean_obj_tag(v_arg_2749_) == 6 {
                                                    v_body_2767_ =
                                                        leanh::lean_ctor_get(v_arg_2749_, 2);
                                                    leanh::lean_inc_ref(v_body_2767_);
                                                    leanh::lean_dec_ref_known(
                                                        v_arg_2749_,
                                                        3,
                                                    );
                                                    v___x_2768_ =
                                                        l_Lean_Expr_hasLooseBVars(v_body_2767_);
                                                    if v___x_2768_ == 0 {
                                                        v___x_2769_ = l_Lean_Expr_constLevels_x21(
                                                            v___x_2762_,
                                                        );
                                                        leanh::lean_dec_ref(v___x_2762_);
                                                        v___x_2770_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__3;
                                                        leanh::lean_inc(v___x_2769_);
                                                        v___x_2771_ = l_Lean_mkConst(
                                                            v___x_2770_,
                                                            v___x_2769_,
                                                        );
                                                        leanh::lean_inc_ref(v_body_2767_);
                                                        leanh::lean_inc_ref(v_body_2765_);
                                                        leanh::lean_inc_ref(v_arg_2755_);
                                                        leanh::lean_inc_ref(v_arg_2758_);
                                                        leanh::lean_inc_ref(v_arg_2761_);
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
                                                        v___x_2776_ = leanh::lean_alloc_ctor(
                                                            1,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_2776_,
                                                            0,
                                                            v___x_2775_,
                                                        );
                                                        v___x_2777_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (1) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_2777_,
                                                            0,
                                                            v___x_2772_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_2777_,
                                                            1,
                                                            v___x_2776_,
                                                        );
                                                        leanh::lean_ctor_set_uint8(
                                                            v___x_2777_,
                                                            (core::mem::size_of::<
                                                                *mut leanh::LeanObject,
                                                            >(
                                                            ) * 2)
                                                                as u32,
                                                            v___x_2764_,
                                                        );
                                                        v___x_2778_ = leanh::lean_alloc_ctor(
                                                            1,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_2778_,
                                                            0,
                                                            v___x_2777_,
                                                        );
                                                        v___x_2779_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_2779_,
                                                            0,
                                                            v___x_2778_,
                                                        );
                                                        return v___x_2779_;
                                                    } else {
                                                        leanh::lean_dec_ref(v_body_2767_);
                                                        leanh::lean_dec_ref(v_body_2765_);
                                                        leanh::lean_dec_ref(v___x_2762_);
                                                        leanh::lean_dec_ref(v_arg_2761_);
                                                        leanh::lean_dec_ref(v_arg_2758_);
                                                        leanh::lean_dec_ref(v_arg_2755_);
                                                        v___x_2780_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                        v___x_2781_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_2781_,
                                                            0,
                                                            v___x_2780_,
                                                        );
                                                        return v___x_2781_;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v_body_2765_);
                                                    leanh::lean_dec_ref(v___x_2762_);
                                                    leanh::lean_dec_ref(v_arg_2761_);
                                                    leanh::lean_dec_ref(v_arg_2758_);
                                                    leanh::lean_dec_ref(v_arg_2755_);
                                                    leanh::lean_dec_ref(v_arg_2749_);
                                                    v___x_2782_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                    v___x_2783_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_2783_,
                                                        0,
                                                        v___x_2782_,
                                                    );
                                                    return v___x_2783_;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v_body_2765_);
                                                leanh::lean_dec_ref(v___x_2762_);
                                                leanh::lean_dec_ref(v_arg_2761_);
                                                leanh::lean_dec_ref(v_arg_2758_);
                                                leanh::lean_dec_ref(v_arg_2755_);
                                                leanh::lean_dec_ref(v_arg_2749_);
                                                v___x_2784_ =
                                                    l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                v___x_2785_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_2785_,
                                                    0,
                                                    v___x_2784_,
                                                );
                                                return v___x_2785_;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_2762_);
                                            leanh::lean_dec_ref(v_arg_2761_);
                                            leanh::lean_dec_ref(v_arg_2758_);
                                            leanh::lean_dec_ref(v_arg_2755_);
                                            leanh::lean_dec_ref(v_arg_2752_);
                                            leanh::lean_dec_ref(v_arg_2749_);
                                            v___x_2786_ =
                                                l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                            v___x_2787_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(
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
                    leanh::lean_ctor_set(v___x_2740_, 0, v___x_2743_);
                    v___x_2745_ = v___x_2740_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
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
                    v_reuseFailAlloc_2795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
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
    mut v_e_2797_: *mut leanh::LeanObject,
    mut v_a_2798_: *mut leanh::LeanObject,
    mut v_a_2799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2800_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_2797_, v_a_2798_);
    leanh::lean_dec(v_a_2798_);
    return v_res_2800_;
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte(
    mut v_e_2801_: *mut leanh::LeanObject,
    mut v_a_2802_: *mut leanh::LeanObject,
    mut v_a_2803_: *mut leanh::LeanObject,
    mut v_a_2804_: *mut leanh::LeanObject,
    mut v_a_2805_: *mut leanh::LeanObject,
    mut v_a_2806_: *mut leanh::LeanObject,
    mut v_a_2807_: *mut leanh::LeanObject,
    mut v_a_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2810_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_2801_, v_a_2806_);
    return v___x_2810_;
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte___boxed(
    mut v_e_2811_: *mut leanh::LeanObject,
    mut v_a_2812_: *mut leanh::LeanObject,
    mut v_a_2813_: *mut leanh::LeanObject,
    mut v_a_2814_: *mut leanh::LeanObject,
    mut v_a_2815_: *mut leanh::LeanObject,
    mut v_a_2816_: *mut leanh::LeanObject,
    mut v_a_2817_: *mut leanh::LeanObject,
    mut v_a_2818_: *mut leanh::LeanObject,
    mut v_a_2819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2820_ = l_Lean_Meta_Grind_simpDIte(
        v_e_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_,
    );
    leanh::lean_dec(v_a_2818_);
    leanh::lean_dec_ref(v_a_2817_);
    leanh::lean_dec(v_a_2816_);
    leanh::lean_dec_ref(v_a_2815_);
    leanh::lean_dec(v_a_2814_);
    leanh::lean_dec_ref(v_a_2813_);
    leanh::lean_dec(v_a_2812_);
    return v_res_2820_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_;
    v___x_2842_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_;
    v___x_2843_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_simpDIte___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2844_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2841_, v___x_2842_, v___x_2843_);
    return v___x_2844_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13____boxed(
    mut v_a_2845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2846_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_();
    return v_res_2846_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2863_ = leanh::lean_box(0);
    v___x_2864_ = l_Lean_Meta_Grind_pushNot___redArg___closed__7;
    v___x_2865_ = l_Lean_mkConst(v___x_2864_, v___x_2863_);
    return v___x_2865_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ = leanh::lean_box(0);
    v___x_2883_ = l_Lean_Meta_Grind_pushNot___redArg___closed__17;
    v___x_2884_ = l_Lean_mkConst(v___x_2883_, v___x_2882_);
    return v___x_2884_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2891_ = leanh::lean_unsigned_to_nat(1);
    v___x_2892_ = lean_nat_to_int(v___x_2891_);
    return v___x_2892_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2893_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__23_once),
        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23,
    );
    v___x_2894_ = l_Lean_mkIntLit(v___x_2893_);
    return v___x_2894_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2899_ = leanh::lean_box(0);
    v___x_2900_ = l_Lean_Meta_Grind_pushNot___redArg___closed__26;
    v___x_2901_ = l_Lean_mkConst(v___x_2900_, v___x_2899_);
    return v___x_2901_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = leanh::lean_unsigned_to_nat(1);
    v___x_2903_ = l_Lean_mkNatLit(v___x_2902_);
    return v___x_2903_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2907_ = leanh::lean_box(0);
    v___x_2908_ = l_Lean_Meta_Grind_pushNot___redArg___closed__29;
    v___x_2909_ = l_Lean_mkConst(v___x_2908_, v___x_2907_);
    return v___x_2909_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2910_ = leanh::lean_box(0);
    v___x_2911_ = l_Lean_Meta_Grind_simpEq___redArg___closed__30;
    v___x_2912_ = l_Lean_mkConst(v___x_2911_, v___x_2910_);
    return v___x_2912_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = leanh::lean_box(0);
    v___x_2918_ = l_Lean_Meta_Grind_pushNot___redArg___closed__33;
    v___x_2919_ = l_Lean_mkConst(v___x_2918_, v___x_2917_);
    return v___x_2919_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2924_ = leanh::lean_box(0);
    v___x_2925_ = l_Lean_Meta_Grind_pushNot___redArg___closed__36;
    v___x_2926_ = l_Lean_mkConst(v___x_2925_, v___x_2924_);
    return v___x_2926_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2932_ = leanh::lean_box(0);
    v___x_2933_ = l_Lean_Meta_Grind_pushNot___redArg___closed__39;
    v___x_2934_ = l_Lean_mkConst(v___x_2933_, v___x_2932_);
    return v___x_2934_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2935_ = leanh::lean_box(0);
    v___x_2936_ = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
    v___x_2937_ = l_Lean_mkConst(v___x_2936_, v___x_2935_);
    return v___x_2937_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2943_ = leanh::lean_box(0);
    v___x_2944_ = l_Lean_Meta_Grind_pushNot___redArg___closed__43;
    v___x_2945_ = l_Lean_mkConst(v___x_2944_, v___x_2943_);
    return v___x_2945_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2946_ = leanh::lean_box(0);
    v___x_2947_ = l_Lean_Meta_Grind_pushNot___redArg___closed__12;
    v___x_2948_ = l_Lean_mkConst(v___x_2947_, v___x_2946_);
    return v___x_2948_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__48()
-> *mut leanh::LeanObject {
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2954_ = leanh::lean_box(0);
    v___x_2955_ = l_Lean_Meta_Grind_pushNot___redArg___closed__47;
    v___x_2956_ = l_Lean_mkConst(v___x_2955_, v___x_2954_);
    return v___x_2956_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51()
-> *mut leanh::LeanObject {
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2960_ = leanh::lean_unsigned_to_nat(0);
    v___x_2961_ = l_Lean_mkBVar(v___x_2960_);
    return v___x_2961_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__56()
-> *mut leanh::LeanObject {
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2972_ = leanh::lean_box(0);
    v___x_2973_ = l_Lean_Meta_Grind_pushNot___redArg___closed__55;
    v___x_2974_ = l_Lean_mkConst(v___x_2973_, v___x_2972_);
    return v___x_2974_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59()
-> *mut leanh::LeanObject {
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2980_ = leanh::lean_box(0);
    v___x_2981_ = l_Lean_Meta_Grind_pushNot___redArg___closed__58;
    v___x_2982_ = l_Lean_mkConst(v___x_2981_, v___x_2980_);
    return v___x_2982_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__60()
-> *mut leanh::LeanObject {
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2983_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__59),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__59_once),
        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59,
    );
    v___x_2984_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2984_, 0, v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__63()
-> *mut leanh::LeanObject {
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2990_ = leanh::lean_box(0);
    v___x_2991_ = l_Lean_Meta_Grind_pushNot___redArg___closed__62;
    v___x_2992_ = l_Lean_mkConst(v___x_2991_, v___x_2990_);
    return v___x_2992_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__64()
-> *mut leanh::LeanObject {
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2993_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__63),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__63_once),
        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__63,
    );
    v___x_2994_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2994_, 0, v___x_2993_);
    return v___x_2994_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNot___redArg(
    mut v_e_2995_: *mut leanh::LeanObject,
    mut v_a_2996_: *mut leanh::LeanObject,
    mut v_a_2997_: *mut leanh::LeanObject,
    mut v_a_2998_: *mut leanh::LeanObject,
    mut v_a_2999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v_arg_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: u8 = 0;
    let mut v___y_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3025_: u8 = 0;
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_a_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut v___y_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3065_: u8 = 0;
    let mut v___y_3066_: u8 = 0;
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3083_: u8 = 0;
    let mut v___x_3084_: u8 = 0;
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3092_: u8 = 0;
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: u8 = 0;
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: u8 = 0;
    let mut v_arg_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: u8 = 0;
    let mut v_arg_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: u8 = 0;
    let mut v___x_3111_: u8 = 0;
    let mut v_arg_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: u8 = 0;
    let mut v_arg_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: u8 = 0;
    let mut v___x_3121_: u8 = 0;
    let mut v_arg_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: u8 = 0;
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3141_: u8 = 0;
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: u8 = 0;
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_a_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v___x_3182_: u8 = 0;
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: u8 = 0;
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3217_: u8 = 0;
    let mut v_a_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut v_a_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3286_: u8 = 0;
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_a_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut v_isSharedCheck_3322_: u8 = 0;
    let mut v_a_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_2995_);
                v___x_3001_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2995_, v_a_2997_);
                if leanh::lean_obj_tag(v___x_3001_) == 0 {
                    v_a_3002_ = leanh::lean_ctor_get(v___x_3001_, 0);
                    v_isSharedCheck_3322_ = (!leanh::lean_is_exclusive(v___x_3001_)) as u8;
                    if v_isSharedCheck_3322_ == 0 {
                        v___x_3004_ = v___x_3001_;
                        v_isShared_3005_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3002_);
                        leanh::lean_dec(v___x_3001_);
                        v___x_3004_ = leanh::lean_box(0);
                        v_isShared_3005_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_2995_);
                    v_a_3323_ = leanh::lean_ctor_get(v___x_3001_, 0);
                    v_isSharedCheck_3330_ = (!leanh::lean_is_exclusive(v___x_3001_)) as u8;
                    if v_isSharedCheck_3330_ == 0 {
                        v___x_3325_ = v___x_3001_;
                        v_isShared_3326_ = v_isSharedCheck_3330_;
                        state = 37;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3323_);
                        leanh::lean_dec(v___x_3001_);
                        v___x_3325_ = leanh::lean_box(0);
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
                    leanh::lean_dec_ref(v___x_3011_);
                    leanh::lean_dec_ref(v_e_2995_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3013_ = leanh::lean_ctor_get(v___x_3011_, 1);
                    leanh::lean_inc_ref(v_arg_3013_);
                    v___x_3014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3011_);
                    v___x_3015_ = l_Lean_Meta_Grind_pushNot___redArg___closed__1;
                    v___x_3016_ = l_Lean_Expr_isConstOf(v___x_3014_, v___x_3015_);
                    leanh::lean_dec_ref(v___x_3014_);
                    if v___x_3016_ == 0 {
                        leanh::lean_dec_ref(v_arg_3013_);
                        leanh::lean_dec_ref(v_e_2995_);
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_3004_);
                        v___x_3088_ =
                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3013_, v_a_2997_);
                        if leanh::lean_obj_tag(v___x_3088_) == 0 {
                            v_a_3089_ = leanh::lean_ctor_get(v___x_3088_, 0);
                            v_isSharedCheck_3313_ =
                                (!leanh::lean_is_exclusive(v___x_3088_)) as u8;
                            if v_isSharedCheck_3313_ == 0 {
                                v___x_3091_ = v___x_3088_;
                                v_isShared_3092_ = v_isSharedCheck_3313_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3089_);
                                leanh::lean_dec(v___x_3088_);
                                v___x_3091_ = leanh::lean_box(0);
                                v_isShared_3092_ = v_isSharedCheck_3313_;
                                state = 11;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_2995_);
                            v_a_3314_ = leanh::lean_ctor_get(v___x_3088_, 0);
                            v_isSharedCheck_3321_ =
                                (!leanh::lean_is_exclusive(v___x_3088_)) as u8;
                            if v_isSharedCheck_3321_ == 0 {
                                v___x_3316_ = v___x_3088_;
                                v_isShared_3317_ = v_isSharedCheck_3321_;
                                state = 35;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3314_);
                                leanh::lean_dec(v___x_3088_);
                                v___x_3316_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3004_, 0, v___x_3007_);
                    v___x_3009_ = v___x_3004_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
                    v___x_3009_ = v_reuseFailAlloc_3010_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3009_;
            }
            4 => {
                leanh::lean_inc_ref(v___y_3022_);
                leanh::lean_inc_ref_n(v___y_3023_, 3);
                leanh::lean_inc(v___y_3024_);
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
                if leanh::lean_obj_tag(v___x_3029_) == 0 {
                    v_a_3030_ = leanh::lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3048_ = (!leanh::lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3048_ == 0 {
                        v___x_3032_ = v___x_3029_;
                        v_isShared_3033_ = v_isSharedCheck_3048_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3030_);
                        leanh::lean_dec(v___x_3029_);
                        v___x_3032_ = leanh::lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3048_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3028_);
                    leanh::lean_dec_ref(v___x_3026_);
                    leanh::lean_dec_ref(v___y_3023_);
                    v_a_3049_ = leanh::lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3056_ = (!leanh::lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3056_ == 0 {
                        v___x_3051_ = v___x_3029_;
                        v_isShared_3052_ = v_isSharedCheck_3056_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3049_);
                        leanh::lean_dec(v___x_3029_);
                        v___x_3051_ = leanh::lean_box(0);
                        v_isShared_3052_ = v_isSharedCheck_3056_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3034_ = l_Lean_Meta_Grind_pushNot___redArg___closed__3;
                v___x_3035_ = leanh::lean_box(0);
                v___x_3036_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3036_, 0, v_a_3030_);
                leanh::lean_ctor_set(v___x_3036_, 1, v___x_3035_);
                leanh::lean_inc_ref(v___x_3036_);
                v___x_3037_ = l_Lean_mkConst(v___x_3034_, v___x_3036_);
                leanh::lean_inc_ref(v___y_3023_);
                v___x_3038_ = l_Lean_mkAppB(v___x_3037_, v___y_3023_, v___x_3028_);
                v___x_3039_ = l_Lean_Meta_Grind_pushNot___redArg___closed__5;
                v___x_3040_ = l_Lean_mkConst(v___x_3039_, v___x_3036_);
                v___x_3041_ = l_Lean_mkAppB(v___x_3040_, v___y_3023_, v___x_3026_);
                v___x_3042_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3042_, 0, v___x_3041_);
                v___x_3043_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3043_, 0, v___x_3038_);
                leanh::lean_ctor_set(v___x_3043_, 1, v___x_3042_);
                leanh::lean_ctor_set_uint8(
                    v___x_3043_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3016_,
                );
                v___x_3044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3044_, 0, v___x_3043_);
                if v_isShared_3033_ == 0 {
                    leanh::lean_ctor_set(v___x_3032_, 0, v___x_3044_);
                    v___x_3046_ = v___x_3032_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
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
                    v_reuseFailAlloc_3055_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
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
                    leanh::lean_dec(v___y_3063_);
                    leanh::lean_inc_ref(v___y_3061_);
                    v___x_3067_ = l_Lean_mkNot(v___y_3061_);
                    leanh::lean_inc_ref(v___y_3064_);
                    v___x_3068_ = l_Lean_mkAnd(v___y_3064_, v___x_3067_);
                    v___x_3069_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__8),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__8_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8,
                    );
                    v___x_3070_ = l_Lean_mkAppB(v___x_3069_, v___y_3064_, v___y_3061_);
                    v___x_3071_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3071_, 0, v___x_3070_);
                    v___x_3072_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3072_, 0, v___x_3068_);
                    leanh::lean_ctor_set(v___x_3072_, 1, v___x_3071_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3072_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3016_,
                    );
                    v___x_3073_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3073_, 0, v___x_3072_);
                    v___x_3074_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3074_, 0, v___x_3073_);
                    return v___x_3074_;
                }
            }
            10 => {
                if leanh::lean_obj_tag(v_e_2995_) == 7 {
                    v_binderName_3080_ = leanh::lean_ctor_get(v_e_2995_, 0);
                    leanh::lean_inc(v_binderName_3080_);
                    v_binderType_3081_ = leanh::lean_ctor_get(v_e_2995_, 1);
                    leanh::lean_inc_ref(v_binderType_3081_);
                    v_body_3082_ = leanh::lean_ctor_get(v_e_2995_, 2);
                    leanh::lean_inc_ref(v_body_3082_);
                    v_binderInfo_3083_ = leanh::lean_ctor_get_uint8(
                        v_e_2995_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_dec_ref_known(v_e_2995_, 3);
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
                    leanh::lean_dec_ref(v_e_2995_);
                    v___x_3086_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    v___x_3087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3087_, 0, v___x_3086_);
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
                            leanh::lean_dec_ref(v___x_3093_);
                            leanh::lean_del_object(v___x_3091_);
                            v___y_3076_ = v_a_2996_;
                            v___y_3077_ = v_a_2997_;
                            v___y_3078_ = v_a_2998_;
                            v___y_3079_ = v_a_2999_;
                            state = 10;
                            continue;
                        } else {
                            v_arg_3099_ = leanh::lean_ctor_get(v___x_3093_, 1);
                            leanh::lean_inc_ref(v_arg_3099_);
                            v___x_3100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3093_);
                            v___x_3101_ = l_Lean_Expr_isConstOf(v___x_3100_, v___x_3015_);
                            if v___x_3101_ == 0 {
                                v___x_3102_ = l_Lean_Expr_isApp(v___x_3100_);
                                if v___x_3102_ == 0 {
                                    leanh::lean_dec_ref(v___x_3100_);
                                    leanh::lean_dec_ref(v_arg_3099_);
                                    leanh::lean_del_object(v___x_3091_);
                                    v___y_3076_ = v_a_2996_;
                                    v___y_3077_ = v_a_2997_;
                                    v___y_3078_ = v_a_2998_;
                                    v___y_3079_ = v_a_2999_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_arg_3103_ = leanh::lean_ctor_get(v___x_3100_, 1);
                                    leanh::lean_inc_ref(v_arg_3103_);
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
                                                    leanh::lean_dec_ref(v___x_3104_);
                                                    leanh::lean_dec_ref(v_arg_3103_);
                                                    leanh::lean_dec_ref(v_arg_3099_);
                                                    leanh::lean_del_object(v___x_3091_);
                                                    v___y_3076_ = v_a_2996_;
                                                    v___y_3077_ = v_a_2997_;
                                                    v___y_3078_ = v_a_2998_;
                                                    v___y_3079_ = v_a_2999_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    v_arg_3112_ =
                                                        leanh::lean_ctor_get(v___x_3104_, 1);
                                                    leanh::lean_inc_ref(v_arg_3112_);
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
                                                            leanh::lean_dec_ref(v___x_3113_);
                                                            leanh::lean_dec_ref(v_arg_3112_);
                                                            leanh::lean_dec_ref(v_arg_3103_);
                                                            leanh::lean_dec_ref(v_arg_3099_);
                                                            leanh::lean_del_object(
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
                                                                leanh::lean_ctor_get(
                                                                    v___x_3113_,
                                                                    1,
                                                                );
                                                            leanh::lean_inc_ref(v_arg_3117_);
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
                                                                    leanh::lean_dec_ref(
                                                                        v___x_3118_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_3117_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_3112_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_3103_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_3099_,
                                                                    );
                                                                    leanh::lean_del_object(
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
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3118_,
                                                                            1,
                                                                        );
                                                                    leanh::lean_inc_ref(
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
                                                                        leanh::lean_dec_ref(
                                                                            v___x_3123_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_3122_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_3117_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_3112_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_3103_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_3099_,
                                                                        );
                                                                        leanh::lean_del_object(v___x_3091_);
                                                                        v___y_3076_ = v_a_2996_;
                                                                        v___y_3077_ = v_a_2997_;
                                                                        v___y_3078_ = v_a_2998_;
                                                                        v___y_3079_ = v_a_2999_;
                                                                        state = 10;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v_e_2995_,
                                                                        );
                                                                        leanh::lean_inc_ref(
                                                                            v_arg_3103_,
                                                                        );
                                                                        v___x_3126_ = l_Lean_mkNot(
                                                                            v_arg_3103_,
                                                                        );
                                                                        leanh::lean_inc_ref(
                                                                            v_arg_3099_,
                                                                        );
                                                                        v___x_3127_ = l_Lean_mkNot(
                                                                            v_arg_3099_,
                                                                        );
                                                                        leanh::lean_inc_ref(
                                                                            v_arg_3112_,
                                                                        );
                                                                        leanh::lean_inc_ref(
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
                                                                        v___x_3129_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__18), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__18_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18);
                                                                        v___x_3130_ = l_Lean_mkApp4(
                                                                            v___x_3129_,
                                                                            v_arg_3117_,
                                                                            v_arg_3112_,
                                                                            v_arg_3103_,
                                                                            v_arg_3099_,
                                                                        );
                                                                        v___x_3131_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3131_,
                                                                            0,
                                                                            v___x_3130_,
                                                                        );
                                                                        v___x_3132_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3132_,
                                                                            0,
                                                                            v___x_3128_,
                                                                        );
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3132_,
                                                                            1,
                                                                            v___x_3131_,
                                                                        );
                                                                        leanh::lean_ctor_set_uint8(v___x_3132_, (core::mem::size_of::<*mut leanh::LeanObject>()*2) as u32, v___x_3125_);
                                                                        v___x_3133_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3133_,
                                                                            0,
                                                                            v___x_3132_,
                                                                        );
                                                                        if v_isShared_3092_ == 0 {
                                                                            leanh::lean_ctor_set(v___x_3091_, 0, v___x_3133_);
                                                                            v___x_3135_ =
                                                                                v___x_3091_;
                                                                            state = 12;
                                                                            continue;
                                                                        } else {
                                                                            v_reuseFailAlloc_3136_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                            leanh::lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
                                                                            v___x_3135_ = v_reuseFailAlloc_3136_;
                                                                            state = 12;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_3118_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_3112_,
                                                                );
                                                                leanh::lean_del_object(
                                                                    v___x_3091_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_e_2995_,
                                                                );
                                                                v___x_3137_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3117_, v_a_2997_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_3137_,
                                                                ) == 0
                                                                {
                                                                    v_a_3138_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3137_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3173_ = (!leanh::lean_is_exclusive(v___x_3137_)) as u8;
                                                                    if v_isSharedCheck_3173_ == 0 {
                                                                        v___x_3140_ = v___x_3137_;
                                                                        v_isShared_3141_ =
                                                                            v_isSharedCheck_3173_;
                                                                        state = 13;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_3138_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3137_,
                                                                        );
                                                                        v___x_3140_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3141_ =
                                                                            v_isSharedCheck_3173_;
                                                                        state = 13;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_3103_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_3099_,
                                                                    );
                                                                    v_a_3174_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3137_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3181_ = (!leanh::lean_is_exclusive(v___x_3137_)) as u8;
                                                                    if v_isSharedCheck_3181_ == 0 {
                                                                        v___x_3176_ = v___x_3137_;
                                                                        v_isShared_3177_ =
                                                                            v_isSharedCheck_3181_;
                                                                        state = 17;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_3174_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3137_,
                                                                        );
                                                                        v___x_3176_ =
                                                                            leanh::lean_box(
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
                                                        leanh::lean_dec_ref(v_e_2995_);
                                                        v___x_3182_ =
                                                            l_Lean_Expr_isProp(v_arg_3112_);
                                                        if v___x_3182_ == 0 {
                                                            leanh::lean_del_object(
                                                                v___x_3091_,
                                                            );
                                                            v___x_3183_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3099_, v_a_2997_);
                                                            if leanh::lean_obj_tag(
                                                                v___x_3183_,
                                                            ) == 0
                                                            {
                                                                v_a_3184_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3183_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3217_ = (!leanh::lean_is_exclusive(v___x_3183_)) as u8;
                                                                if v_isSharedCheck_3217_ == 0 {
                                                                    v___x_3186_ = v___x_3183_;
                                                                    v_isShared_3187_ =
                                                                        v_isSharedCheck_3217_;
                                                                    state = 19;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_3184_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_3183_,
                                                                    );
                                                                    v___x_3186_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_3187_ =
                                                                        v_isSharedCheck_3217_;
                                                                    state = 19;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_3113_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_3112_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_3103_,
                                                                );
                                                                v_a_3218_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3183_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3225_ = (!leanh::lean_is_exclusive(v___x_3183_)) as u8;
                                                                if v_isSharedCheck_3225_ == 0 {
                                                                    v___x_3220_ = v___x_3183_;
                                                                    v_isShared_3221_ =
                                                                        v_isSharedCheck_3225_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_3218_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_3183_,
                                                                    );
                                                                    v___x_3220_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_3221_ =
                                                                        v_isSharedCheck_3225_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            leanh::lean_inc_ref(v_arg_3099_);
                                                            v___x_3226_ = l_Lean_mkNot(v_arg_3099_);
                                                            leanh::lean_inc_ref(v_arg_3103_);
                                                            v___x_3227_ = l_Lean_mkApp3(
                                                                v___x_3113_,
                                                                v_arg_3112_,
                                                                v_arg_3103_,
                                                                v___x_3226_,
                                                            );
                                                            v___x_3228_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__40), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__40_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40);
                                                            v___x_3229_ = l_Lean_mkAppB(
                                                                v___x_3228_,
                                                                v_arg_3103_,
                                                                v_arg_3099_,
                                                            );
                                                            v___x_3230_ =
                                                                leanh::lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_3230_,
                                                                0,
                                                                v___x_3229_,
                                                            );
                                                            v___x_3231_ =
                                                                leanh::lean_alloc_ctor(
                                                                    0,
                                                                    2,
                                                                    (1) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_3231_,
                                                                0,
                                                                v___x_3227_,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v___x_3231_,
                                                                1,
                                                                v___x_3230_,
                                                            );
                                                            leanh::lean_ctor_set_uint8(
                                                                v___x_3231_,
                                                                (core::mem::size_of::<
                                                                    *mut leanh::LeanObject,
                                                                >(
                                                                ) * 2)
                                                                    as u32,
                                                                v___x_3115_,
                                                            );
                                                            v___x_3232_ =
                                                                leanh::lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_3232_,
                                                                0,
                                                                v___x_3231_,
                                                            );
                                                            if v_isShared_3092_ == 0 {
                                                                leanh::lean_ctor_set(
                                                                    v___x_3091_,
                                                                    0,
                                                                    v___x_3232_,
                                                                );
                                                                v___x_3234_ = v___x_3091_;
                                                                state = 25;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_3235_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
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
                                                leanh::lean_dec_ref(v___x_3104_);
                                                leanh::lean_dec_ref(v_e_2995_);
                                                v___x_3236_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__41), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__41_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__41);
                                                leanh::lean_inc_ref(v_arg_3103_);
                                                v___x_3237_ = l_Lean_mkNot(v_arg_3103_);
                                                leanh::lean_inc_ref(v_arg_3099_);
                                                v___x_3238_ = l_Lean_mkNot(v_arg_3099_);
                                                v___x_3239_ = l_Lean_mkAppB(
                                                    v___x_3236_,
                                                    v___x_3237_,
                                                    v___x_3238_,
                                                );
                                                v___x_3240_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__44), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__44_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__44);
                                                v___x_3241_ = l_Lean_mkAppB(
                                                    v___x_3240_,
                                                    v_arg_3103_,
                                                    v_arg_3099_,
                                                );
                                                v___x_3242_ =
                                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3242_,
                                                    0,
                                                    v___x_3241_,
                                                );
                                                v___x_3243_ =
                                                    leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3243_,
                                                    0,
                                                    v___x_3239_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3243_,
                                                    1,
                                                    v___x_3242_,
                                                );
                                                leanh::lean_ctor_set_uint8(
                                                    v___x_3243_,
                                                    (core::mem::size_of::<
                                                        *mut leanh::LeanObject,
                                                    >(
                                                    ) * 2)
                                                        as u32,
                                                    v___x_3110_,
                                                );
                                                v___x_3244_ =
                                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3244_,
                                                    0,
                                                    v___x_3243_,
                                                );
                                                if v_isShared_3092_ == 0 {
                                                    leanh::lean_ctor_set(
                                                        v___x_3091_,
                                                        0,
                                                        v___x_3244_,
                                                    );
                                                    v___x_3246_ = v___x_3091_;
                                                    state = 26;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3247_ =
                                                        leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    leanh::lean_ctor_set(
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
                                            leanh::lean_dec_ref(v___x_3104_);
                                            leanh::lean_dec_ref(v_e_2995_);
                                            v___x_3248_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__45), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__45_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__45);
                                            leanh::lean_inc_ref(v_arg_3103_);
                                            v___x_3249_ = l_Lean_mkNot(v_arg_3103_);
                                            leanh::lean_inc_ref(v_arg_3099_);
                                            v___x_3250_ = l_Lean_mkNot(v_arg_3099_);
                                            v___x_3251_ = l_Lean_mkAppB(
                                                v___x_3248_,
                                                v___x_3249_,
                                                v___x_3250_,
                                            );
                                            v___x_3252_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__48), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__48_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__48);
                                            v___x_3253_ = l_Lean_mkAppB(
                                                v___x_3252_,
                                                v_arg_3103_,
                                                v_arg_3099_,
                                            );
                                            v___x_3254_ =
                                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3254_,
                                                0,
                                                v___x_3253_,
                                            );
                                            v___x_3255_ =
                                                leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3255_,
                                                0,
                                                v___x_3251_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3255_,
                                                1,
                                                v___x_3254_,
                                            );
                                            leanh::lean_ctor_set_uint8(
                                                v___x_3255_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 2)
                                                    as u32,
                                                v___x_3108_,
                                            );
                                            v___x_3256_ =
                                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3256_,
                                                0,
                                                v___x_3255_,
                                            );
                                            if v_isShared_3092_ == 0 {
                                                leanh::lean_ctor_set(
                                                    v___x_3091_,
                                                    0,
                                                    v___x_3256_,
                                                );
                                                v___x_3258_ = v___x_3091_;
                                                state = 27;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3259_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
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
                                        leanh::lean_dec_ref(v___x_3104_);
                                        leanh::lean_del_object(v___x_3091_);
                                        leanh::lean_dec_ref(v_e_2995_);
                                        v___x_3260_ =
                                            l_Lean_Meta_Grind_pushNot___redArg___closed__50;
                                        v___x_3261_ = 0;
                                        v___x_3262_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__51), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__51_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51);
                                        leanh::lean_inc_ref(v_arg_3099_);
                                        v___x_3263_ =
                                            l_Lean_Expr_app___override(v_arg_3099_, v___x_3262_);
                                        v___x_3264_ = l_Lean_mkNot(v___x_3263_);
                                        leanh::lean_inc_ref_n(v_arg_3103_, 2);
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
                                        if leanh::lean_obj_tag(v___x_3266_) == 0 {
                                            v_a_3267_ = leanh::lean_ctor_get(v___x_3266_, 0);
                                            v_isSharedCheck_3282_ =
                                                (!leanh::lean_is_exclusive(v___x_3266_))
                                                    as u8;
                                            if v_isSharedCheck_3282_ == 0 {
                                                v___x_3269_ = v___x_3266_;
                                                v_isShared_3270_ = v_isSharedCheck_3282_;
                                                state = 28;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3267_);
                                                leanh::lean_dec(v___x_3266_);
                                                v___x_3269_ = leanh::lean_box(0);
                                                v_isShared_3270_ = v_isSharedCheck_3282_;
                                                state = 28;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_3265_);
                                            leanh::lean_dec_ref(v_arg_3103_);
                                            leanh::lean_dec_ref(v_arg_3099_);
                                            v_a_3283_ = leanh::lean_ctor_get(v___x_3266_, 0);
                                            v_isSharedCheck_3290_ =
                                                (!leanh::lean_is_exclusive(v___x_3266_))
                                                    as u8;
                                            if v_isSharedCheck_3290_ == 0 {
                                                v___x_3285_ = v___x_3266_;
                                                v_isShared_3286_ = v_isSharedCheck_3290_;
                                                state = 30;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3283_);
                                                leanh::lean_dec(v___x_3266_);
                                                v___x_3285_ = leanh::lean_box(0);
                                                v_isShared_3286_ = v_isSharedCheck_3290_;
                                                state = 30;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_3100_);
                                leanh::lean_dec_ref(v_e_2995_);
                                v___x_3291_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_pushNot___redArg___closed__56
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_pushNot___redArg___closed__56_once
                                    ),
                                    _init_l_Lean_Meta_Grind_pushNot___redArg___closed__56,
                                );
                                leanh::lean_inc_ref(v_arg_3099_);
                                v___x_3292_ = l_Lean_Expr_app___override(v___x_3291_, v_arg_3099_);
                                v___x_3293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3293_, 0, v___x_3292_);
                                v___x_3294_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                leanh::lean_ctor_set(v___x_3294_, 0, v_arg_3099_);
                                leanh::lean_ctor_set(v___x_3294_, 1, v___x_3293_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_3294_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                        as u32,
                                    v___x_3101_,
                                );
                                v___x_3295_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3295_, 0, v___x_3294_);
                                if v_isShared_3092_ == 0 {
                                    leanh::lean_ctor_set(v___x_3091_, 0, v___x_3295_);
                                    v___x_3297_ = v___x_3091_;
                                    state = 32;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3298_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
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
                        leanh::lean_dec_ref(v___x_3093_);
                        leanh::lean_dec_ref(v_e_2995_);
                        v___x_3299_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpEq___redArg___closed__9_once
                            ),
                            _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9,
                        );
                        v___x_3300_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__60
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__60_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__60,
                        );
                        v___x_3301_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        leanh::lean_ctor_set(v___x_3301_, 0, v___x_3299_);
                        leanh::lean_ctor_set(v___x_3301_, 1, v___x_3300_);
                        leanh::lean_ctor_set_uint8(
                            v___x_3301_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v___x_3097_,
                        );
                        v___x_3302_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3302_, 0, v___x_3301_);
                        if v_isShared_3092_ == 0 {
                            leanh::lean_ctor_set(v___x_3091_, 0, v___x_3302_);
                            v___x_3304_ = v___x_3091_;
                            state = 33;
                            continue;
                        } else {
                            v_reuseFailAlloc_3305_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
                            v___x_3304_ = v_reuseFailAlloc_3305_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3093_);
                    leanh::lean_dec_ref(v_e_2995_);
                    v___x_3306_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6_once),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6,
                    );
                    v___x_3307_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__64),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__64_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__64,
                    );
                    v___x_3308_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3308_, 0, v___x_3306_);
                    leanh::lean_ctor_set(v___x_3308_, 1, v___x_3307_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3308_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3095_,
                    );
                    v___x_3309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3309_, 0, v___x_3308_);
                    if v_isShared_3092_ == 0 {
                        leanh::lean_ctor_set(v___x_3091_, 0, v___x_3309_);
                        v___x_3311_ = v___x_3091_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
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
                    leanh::lean_dec_ref(v___x_3142_);
                    if v___x_3146_ == 0 {
                        leanh::lean_dec_ref(v_arg_3103_);
                        leanh::lean_dec_ref(v_arg_3099_);
                        v___x_3147_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        if v_isShared_3141_ == 0 {
                            leanh::lean_ctor_set(v___x_3140_, 0, v___x_3147_);
                            v___x_3149_ = v___x_3140_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3150_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
                            v___x_3149_ = v_reuseFailAlloc_3150_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___x_3151_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__24
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__24_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24,
                        );
                        leanh::lean_inc_ref(v_arg_3099_);
                        v___x_3152_ = l_Lean_mkIntAdd(v_arg_3099_, v___x_3151_);
                        leanh::lean_inc_ref(v_arg_3103_);
                        v___x_3153_ = l_Lean_mkIntLE(v___x_3152_, v_arg_3103_);
                        v___x_3154_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__27
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__27_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27,
                        );
                        v___x_3155_ = l_Lean_mkAppB(v___x_3154_, v_arg_3103_, v_arg_3099_);
                        v___x_3156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
                        v___x_3157_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        leanh::lean_ctor_set(v___x_3157_, 0, v___x_3153_);
                        leanh::lean_ctor_set(v___x_3157_, 1, v___x_3156_);
                        leanh::lean_ctor_set_uint8(
                            v___x_3157_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v___x_3146_,
                        );
                        v___x_3158_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3158_, 0, v___x_3157_);
                        if v_isShared_3141_ == 0 {
                            leanh::lean_ctor_set(v___x_3140_, 0, v___x_3158_);
                            v___x_3160_ = v___x_3140_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_3161_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3158_);
                            v___x_3160_ = v_reuseFailAlloc_3161_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3142_);
                    v___x_3162_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__28),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__28_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28,
                    );
                    leanh::lean_inc_ref(v_arg_3099_);
                    v___x_3163_ = l_Lean_mkNatAdd(v_arg_3099_, v___x_3162_);
                    leanh::lean_inc_ref(v_arg_3103_);
                    v___x_3164_ = l_Lean_mkNatLE(v___x_3163_, v_arg_3103_);
                    v___x_3165_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__30),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__30_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30,
                    );
                    v___x_3166_ = l_Lean_mkAppB(v___x_3165_, v_arg_3103_, v_arg_3099_);
                    v___x_3167_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3167_, 0, v___x_3166_);
                    v___x_3168_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3168_, 0, v___x_3164_);
                    leanh::lean_ctor_set(v___x_3168_, 1, v___x_3167_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3168_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3144_,
                    );
                    v___x_3169_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3169_, 0, v___x_3168_);
                    if v_isShared_3141_ == 0 {
                        leanh::lean_ctor_set(v___x_3140_, 0, v___x_3169_);
                        v___x_3171_ = v___x_3140_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
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
                    v_reuseFailAlloc_3180_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
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
                    leanh::lean_dec_ref(v___x_3188_);
                    if v___x_3192_ == 0 {
                        leanh::lean_dec_ref(v___x_3113_);
                        leanh::lean_dec_ref(v_arg_3112_);
                        leanh::lean_dec_ref(v_arg_3103_);
                        v___x_3193_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        if v_isShared_3187_ == 0 {
                            leanh::lean_ctor_set(v___x_3186_, 0, v___x_3193_);
                            v___x_3195_ = v___x_3186_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_3196_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
                            v___x_3195_ = v_reuseFailAlloc_3196_;
                            state = 20;
                            continue;
                        }
                    } else {
                        v___x_3197_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__31
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__31_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__31,
                        );
                        leanh::lean_inc_ref(v_arg_3103_);
                        v___x_3198_ =
                            l_Lean_mkApp3(v___x_3113_, v_arg_3112_, v_arg_3103_, v___x_3197_);
                        v___x_3199_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__34
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__34_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__34,
                        );
                        v___x_3200_ = l_Lean_Expr_app___override(v___x_3199_, v_arg_3103_);
                        v___x_3201_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3201_, 0, v___x_3200_);
                        v___x_3202_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        leanh::lean_ctor_set(v___x_3202_, 0, v___x_3198_);
                        leanh::lean_ctor_set(v___x_3202_, 1, v___x_3201_);
                        leanh::lean_ctor_set_uint8(
                            v___x_3202_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v___x_3115_,
                        );
                        v___x_3203_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3203_, 0, v___x_3202_);
                        if v_isShared_3187_ == 0 {
                            leanh::lean_ctor_set(v___x_3186_, 0, v___x_3203_);
                            v___x_3205_ = v___x_3186_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_3206_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
                            v___x_3205_ = v_reuseFailAlloc_3206_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3188_);
                    v___x_3207_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__22),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpEq___redArg___closed__22_once
                        ),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22,
                    );
                    leanh::lean_inc_ref(v_arg_3103_);
                    v___x_3208_ = l_Lean_mkApp3(v___x_3113_, v_arg_3112_, v_arg_3103_, v___x_3207_);
                    v___x_3209_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__37),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__37_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__37,
                    );
                    v___x_3210_ = l_Lean_Expr_app___override(v___x_3209_, v_arg_3103_);
                    v___x_3211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3211_, 0, v___x_3210_);
                    v___x_3212_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3212_, 0, v___x_3208_);
                    leanh::lean_ctor_set(v___x_3212_, 1, v___x_3211_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3212_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3115_,
                    );
                    v___x_3213_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3213_, 0, v___x_3212_);
                    if v_isShared_3187_ == 0 {
                        leanh::lean_ctor_set(v___x_3186_, 0, v___x_3213_);
                        v___x_3215_ = v___x_3186_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_3216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
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
                    v_reuseFailAlloc_3224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
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
                v___x_3272_ = leanh::lean_box(0);
                v___x_3273_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3273_, 0, v_a_3267_);
                leanh::lean_ctor_set(v___x_3273_, 1, v___x_3272_);
                v___x_3274_ = l_Lean_mkConst(v___x_3271_, v___x_3273_);
                v___x_3275_ = l_Lean_mkAppB(v___x_3274_, v_arg_3103_, v_arg_3099_);
                v___x_3276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3276_, 0, v___x_3275_);
                v___x_3277_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3277_, 0, v___x_3265_);
                leanh::lean_ctor_set(v___x_3277_, 1, v___x_3276_);
                leanh::lean_ctor_set_uint8(
                    v___x_3277_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3106_,
                );
                v___x_3278_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3278_, 0, v___x_3277_);
                if v_isShared_3270_ == 0 {
                    leanh::lean_ctor_set(v___x_3269_, 0, v___x_3278_);
                    v___x_3280_ = v___x_3269_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3281_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
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
                    v_reuseFailAlloc_3289_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
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
                    v_reuseFailAlloc_3320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
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
                    v_reuseFailAlloc_3329_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
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
    mut v_e_3331_: *mut leanh::LeanObject,
    mut v_a_3332_: *mut leanh::LeanObject,
    mut v_a_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
    mut v_a_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3337_ =
        l_Lean_Meta_Grind_pushNot___redArg(v_e_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
    leanh::lean_dec(v_a_3335_);
    leanh::lean_dec_ref(v_a_3334_);
    leanh::lean_dec(v_a_3333_);
    leanh::lean_dec_ref(v_a_3332_);
    return v_res_3337_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNot(
    mut v_e_3338_: *mut leanh::LeanObject,
    mut v_a_3339_: *mut leanh::LeanObject,
    mut v_a_3340_: *mut leanh::LeanObject,
    mut v_a_3341_: *mut leanh::LeanObject,
    mut v_a_3342_: *mut leanh::LeanObject,
    mut v_a_3343_: *mut leanh::LeanObject,
    mut v_a_3344_: *mut leanh::LeanObject,
    mut v_a_3345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3347_ =
        l_Lean_Meta_Grind_pushNot___redArg(v_e_3338_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
    return v___x_3347_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNot___boxed(
    mut v_e_3348_: *mut leanh::LeanObject,
    mut v_a_3349_: *mut leanh::LeanObject,
    mut v_a_3350_: *mut leanh::LeanObject,
    mut v_a_3351_: *mut leanh::LeanObject,
    mut v_a_3352_: *mut leanh::LeanObject,
    mut v_a_3353_: *mut leanh::LeanObject,
    mut v_a_3354_: *mut leanh::LeanObject,
    mut v_a_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l_Lean_Meta_Grind_pushNot(
        v_e_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_,
    );
    leanh::lean_dec(v_a_3355_);
    leanh::lean_dec_ref(v_a_3354_);
    leanh::lean_dec(v_a_3353_);
    leanh::lean_dec_ref(v_a_3352_);
    leanh::lean_dec(v_a_3351_);
    leanh::lean_dec_ref(v_a_3350_);
    leanh::lean_dec(v_a_3349_);
    return v_res_3357_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_()
-> *mut leanh::LeanObject {
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3374_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_;
    v___x_3375_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_;
    v___x_3376_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_pushNot___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3377_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3374_, v___x_3375_, v___x_3376_);
    return v___x_3377_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10____boxed(
    mut v_a_3378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3379_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_();
    return v_res_3379_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3385_ = leanh::lean_box(0);
    v___x_3386_ = l_Lean_Meta_Grind_simpOr___redArg___closed__1;
    v___x_3387_ = l_Lean_mkConst(v___x_3386_, v___x_3385_);
    return v___x_3387_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = leanh::lean_box(0);
    v___x_3394_ = l_Lean_Meta_Grind_simpOr___redArg___closed__4;
    v___x_3395_ = l_Lean_mkConst(v___x_3394_, v___x_3393_);
    return v___x_3395_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = leanh::lean_box(0);
    v___x_3400_ = l_Lean_Meta_Grind_simpOr___redArg___closed__7;
    v___x_3401_ = l_Lean_mkConst(v___x_3400_, v___x_3399_);
    return v___x_3401_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11() -> *mut leanh::LeanObject
{
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3405_ = leanh::lean_box(0);
    v___x_3406_ = l_Lean_Meta_Grind_simpOr___redArg___closed__10;
    v___x_3407_ = l_Lean_mkConst(v___x_3406_, v___x_3405_);
    return v___x_3407_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14() -> *mut leanh::LeanObject
{
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3413_ = leanh::lean_box(0);
    v___x_3414_ = l_Lean_Meta_Grind_simpOr___redArg___closed__13;
    v___x_3415_ = l_Lean_mkConst(v___x_3414_, v___x_3413_);
    return v___x_3415_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17() -> *mut leanh::LeanObject
{
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3419_ = leanh::lean_box(0);
    v___x_3420_ = l_Lean_Meta_Grind_simpOr___redArg___closed__16;
    v___x_3421_ = l_Lean_mkConst(v___x_3420_, v___x_3419_);
    return v___x_3421_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20() -> *mut leanh::LeanObject
{
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3425_ = leanh::lean_box(0);
    v___x_3426_ = l_Lean_Meta_Grind_simpOr___redArg___closed__19;
    v___x_3427_ = l_Lean_mkConst(v___x_3426_, v___x_3425_);
    return v___x_3427_;
}
pub unsafe fn l_Lean_Meta_Grind_simpOr___redArg(
    mut v_e_3428_: *mut leanh::LeanObject,
    mut v_a_3429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: u8 = 0;
    let mut v_arg_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v_arg_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3456_: u8 = 0;
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: u8 = 0;
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: u8 = 0;
    let mut v_arg_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v_arg_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: u8 = 0;
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_a_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u8 = 0;
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: u8 = 0;
    let mut v_arg_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: u8 = 0;
    let mut v_arg_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: u8 = 0;
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_a_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut v_a_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3434_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3428_, v_a_3429_);
                if leanh::lean_obj_tag(v___x_3434_) == 0 {
                    v_a_3435_ = leanh::lean_ctor_get(v___x_3434_, 0);
                    v_isSharedCheck_3581_ = (!leanh::lean_is_exclusive(v___x_3434_)) as u8;
                    if v_isSharedCheck_3581_ == 0 {
                        v___x_3437_ = v___x_3434_;
                        v_isShared_3438_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3435_);
                        leanh::lean_dec(v___x_3434_);
                        v___x_3437_ = leanh::lean_box(0);
                        v_isShared_3438_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3582_ = leanh::lean_ctor_get(v___x_3434_, 0);
                    v_isSharedCheck_3589_ = (!leanh::lean_is_exclusive(v___x_3434_)) as u8;
                    if v_isSharedCheck_3589_ == 0 {
                        v___x_3584_ = v___x_3434_;
                        v_isShared_3585_ = v_isSharedCheck_3589_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3582_);
                        leanh::lean_dec(v___x_3434_);
                        v___x_3584_ = leanh::lean_box(0);
                        v_isShared_3585_ = v_isSharedCheck_3589_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3432_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                v___x_3433_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3433_, 0, v___x_3432_);
                return v___x_3433_;
            }
            2 => {
                v___x_3444_ = l_Lean_Expr_cleanupAnnotations(v_a_3435_);
                v___x_3445_ = l_Lean_Expr_isApp(v___x_3444_);
                if v___x_3445_ == 0 {
                    leanh::lean_dec_ref(v___x_3444_);
                    state = 3;
                    continue;
                } else {
                    v_arg_3446_ = leanh::lean_ctor_get(v___x_3444_, 1);
                    leanh::lean_inc_ref(v_arg_3446_);
                    v___x_3447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3444_);
                    v___x_3448_ = l_Lean_Expr_isApp(v___x_3447_);
                    if v___x_3448_ == 0 {
                        leanh::lean_dec_ref(v___x_3447_);
                        leanh::lean_dec_ref(v_arg_3446_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_3449_ = leanh::lean_ctor_get(v___x_3447_, 1);
                        leanh::lean_inc_ref(v_arg_3449_);
                        v___x_3526_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3447_);
                        v___x_3527_ = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
                        v___x_3528_ = l_Lean_Expr_isConstOf(v___x_3526_, v___x_3527_);
                        leanh::lean_dec_ref(v___x_3526_);
                        if v___x_3528_ == 0 {
                            leanh::lean_dec_ref(v_arg_3449_);
                            leanh::lean_dec_ref(v_arg_3446_);
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_3437_);
                            leanh::lean_inc_ref(v_arg_3449_);
                            v___x_3529_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                v_arg_3449_,
                                v_a_3429_,
                            );
                            if leanh::lean_obj_tag(v___x_3529_) == 0 {
                                v_a_3530_ = leanh::lean_ctor_get(v___x_3529_, 0);
                                v_isSharedCheck_3572_ =
                                    (!leanh::lean_is_exclusive(v___x_3529_)) as u8;
                                if v_isSharedCheck_3572_ == 0 {
                                    v___x_3532_ = v___x_3529_;
                                    v_isShared_3533_ = v_isSharedCheck_3572_;
                                    state = 15;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3530_);
                                    leanh::lean_dec(v___x_3529_);
                                    v___x_3532_ = leanh::lean_box(0);
                                    v_isShared_3533_ = v_isSharedCheck_3572_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_arg_3449_);
                                leanh::lean_dec_ref(v_arg_3446_);
                                v_a_3573_ = leanh::lean_ctor_get(v___x_3529_, 0);
                                v_isSharedCheck_3580_ =
                                    (!leanh::lean_is_exclusive(v___x_3529_)) as u8;
                                if v_isSharedCheck_3580_ == 0 {
                                    v___x_3575_ = v___x_3529_;
                                    v_isShared_3576_ = v_isSharedCheck_3580_;
                                    state = 19;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3573_);
                                    leanh::lean_dec(v___x_3529_);
                                    v___x_3575_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3437_, 0, v___x_3440_);
                    v___x_3442_ = v___x_3437_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3443_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
                    v___x_3442_ = v_reuseFailAlloc_3443_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3442_;
            }
            5 => {
                leanh::lean_inc_ref(v_arg_3446_);
                v___x_3452_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3446_, v___y_3451_);
                if leanh::lean_obj_tag(v___x_3452_) == 0 {
                    v_a_3453_ = leanh::lean_ctor_get(v___x_3452_, 0);
                    v_isSharedCheck_3517_ = (!leanh::lean_is_exclusive(v___x_3452_)) as u8;
                    if v_isSharedCheck_3517_ == 0 {
                        v___x_3455_ = v___x_3452_;
                        v_isShared_3456_ = v_isSharedCheck_3517_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3453_);
                        leanh::lean_dec(v___x_3452_);
                        v___x_3455_ = leanh::lean_box(0);
                        v_isShared_3456_ = v_isSharedCheck_3517_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_arg_3449_);
                    leanh::lean_dec_ref(v_arg_3446_);
                    v_a_3518_ = leanh::lean_ctor_get(v___x_3452_, 0);
                    v_isSharedCheck_3525_ = (!leanh::lean_is_exclusive(v___x_3452_)) as u8;
                    if v_isSharedCheck_3525_ == 0 {
                        v___x_3520_ = v___x_3452_;
                        v_isShared_3521_ = v_isSharedCheck_3525_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3518_);
                        leanh::lean_dec(v___x_3452_);
                        v___x_3520_ = leanh::lean_box(0);
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
                        leanh::lean_dec_ref(v_arg_3446_);
                        v___x_3462_ = l_Lean_Expr_isApp(v___x_3457_);
                        if v___x_3462_ == 0 {
                            leanh::lean_dec_ref(v___x_3457_);
                            leanh::lean_del_object(v___x_3455_);
                            leanh::lean_dec_ref(v_arg_3449_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_3463_ = leanh::lean_ctor_get(v___x_3457_, 1);
                            leanh::lean_inc_ref(v_arg_3463_);
                            v___x_3464_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3457_);
                            v___x_3465_ = l_Lean_Expr_isApp(v___x_3464_);
                            if v___x_3465_ == 0 {
                                leanh::lean_dec_ref(v___x_3464_);
                                leanh::lean_dec_ref(v_arg_3463_);
                                leanh::lean_del_object(v___x_3455_);
                                leanh::lean_dec_ref(v_arg_3449_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_3466_ = leanh::lean_ctor_get(v___x_3464_, 1);
                                leanh::lean_inc_ref(v_arg_3466_);
                                v___x_3467_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3464_);
                                v___x_3468_ = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
                                v___x_3469_ = l_Lean_Expr_isConstOf(v___x_3467_, v___x_3468_);
                                leanh::lean_dec_ref(v___x_3467_);
                                if v___x_3469_ == 0 {
                                    leanh::lean_dec_ref(v_arg_3466_);
                                    leanh::lean_dec_ref(v_arg_3463_);
                                    leanh::lean_del_object(v___x_3455_);
                                    leanh::lean_dec_ref(v_arg_3449_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3470_ = l_Lean_Expr_isForall(v_arg_3449_);
                                    if v___x_3470_ == 0 {
                                        v___x_3471_ = l_Lean_Expr_isForall(v_arg_3466_);
                                        if v___x_3471_ == 0 {
                                            v___x_3472_ = l_Lean_Expr_isForall(v_arg_3463_);
                                            if v___x_3472_ == 0 {
                                                leanh::lean_dec_ref(v_arg_3466_);
                                                leanh::lean_dec_ref(v_arg_3463_);
                                                leanh::lean_dec_ref(v_arg_3449_);
                                                v___x_3473_ =
                                                    l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                if v_isShared_3456_ == 0 {
                                                    leanh::lean_ctor_set(
                                                        v___x_3455_,
                                                        0,
                                                        v___x_3473_,
                                                    );
                                                    v___x_3475_ = v___x_3455_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3476_ =
                                                        leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3476_,
                                                        0,
                                                        v___x_3473_,
                                                    );
                                                    v___x_3475_ = v_reuseFailAlloc_3476_;
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_inc_ref(v_arg_3449_);
                                                leanh::lean_inc_ref(v_arg_3466_);
                                                v___x_3477_ = l_Lean_mkOr(v_arg_3466_, v_arg_3449_);
                                                leanh::lean_inc_ref(v_arg_3463_);
                                                v___x_3478_ = l_Lean_mkOr(v_arg_3463_, v___x_3477_);
                                                v___x_3479_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__2_once), _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2);
                                                v___x_3480_ = l_Lean_mkApp3(
                                                    v___x_3479_,
                                                    v_arg_3449_,
                                                    v_arg_3466_,
                                                    v_arg_3463_,
                                                );
                                                v___x_3481_ =
                                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3481_,
                                                    0,
                                                    v___x_3480_,
                                                );
                                                v___x_3482_ =
                                                    leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3482_,
                                                    0,
                                                    v___x_3478_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3482_,
                                                    1,
                                                    v___x_3481_,
                                                );
                                                leanh::lean_ctor_set_uint8(
                                                    v___x_3482_,
                                                    (core::mem::size_of::<
                                                        *mut leanh::LeanObject,
                                                    >(
                                                    ) * 2)
                                                        as u32,
                                                    v___x_3469_,
                                                );
                                                v___x_3483_ =
                                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3483_,
                                                    0,
                                                    v___x_3482_,
                                                );
                                                if v_isShared_3456_ == 0 {
                                                    leanh::lean_ctor_set(
                                                        v___x_3455_,
                                                        0,
                                                        v___x_3483_,
                                                    );
                                                    v___x_3485_ = v___x_3455_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3486_ =
                                                        leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    leanh::lean_ctor_set(
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
                                            leanh::lean_inc_ref(v_arg_3463_);
                                            leanh::lean_inc_ref(v_arg_3449_);
                                            v___x_3487_ = l_Lean_mkOr(v_arg_3449_, v_arg_3463_);
                                            leanh::lean_inc_ref(v_arg_3466_);
                                            v___x_3488_ = l_Lean_mkOr(v_arg_3466_, v___x_3487_);
                                            v___x_3489_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__5_once), _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5);
                                            v___x_3490_ = l_Lean_mkApp3(
                                                v___x_3489_,
                                                v_arg_3449_,
                                                v_arg_3466_,
                                                v_arg_3463_,
                                            );
                                            v___x_3491_ =
                                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3491_,
                                                0,
                                                v___x_3490_,
                                            );
                                            v___x_3492_ =
                                                leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3492_,
                                                0,
                                                v___x_3488_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3492_,
                                                1,
                                                v___x_3491_,
                                            );
                                            leanh::lean_ctor_set_uint8(
                                                v___x_3492_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 2)
                                                    as u32,
                                                v___x_3469_,
                                            );
                                            v___x_3493_ =
                                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3493_,
                                                0,
                                                v___x_3492_,
                                            );
                                            if v_isShared_3456_ == 0 {
                                                leanh::lean_ctor_set(
                                                    v___x_3455_,
                                                    0,
                                                    v___x_3493_,
                                                );
                                                v___x_3495_ = v___x_3455_;
                                                state = 9;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3496_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
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
                                        leanh::lean_dec_ref(v_arg_3466_);
                                        leanh::lean_dec_ref(v_arg_3463_);
                                        leanh::lean_dec_ref(v_arg_3449_);
                                        v___x_3497_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                        if v_isShared_3456_ == 0 {
                                            leanh::lean_ctor_set(
                                                v___x_3455_,
                                                0,
                                                v___x_3497_,
                                            );
                                            v___x_3499_ = v___x_3455_;
                                            state = 10;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3500_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(
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
                        leanh::lean_dec_ref(v___x_3457_);
                        v___x_3501_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__8),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpOr___redArg___closed__8_once
                            ),
                            _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8,
                        );
                        v___x_3502_ = l_Lean_Expr_app___override(v___x_3501_, v_arg_3449_);
                        v___x_3503_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3503_, 0, v___x_3502_);
                        v___x_3504_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        leanh::lean_ctor_set(v___x_3504_, 0, v_arg_3446_);
                        leanh::lean_ctor_set(v___x_3504_, 1, v___x_3503_);
                        leanh::lean_ctor_set_uint8(
                            v___x_3504_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v___x_3461_,
                        );
                        v___x_3505_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3505_, 0, v___x_3504_);
                        if v_isShared_3456_ == 0 {
                            leanh::lean_ctor_set(v___x_3455_, 0, v___x_3505_);
                            v___x_3507_ = v___x_3455_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3508_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
                            v___x_3507_ = v_reuseFailAlloc_3508_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3457_);
                    leanh::lean_dec_ref(v_arg_3446_);
                    v___x_3509_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__11),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpOr___redArg___closed__11_once
                        ),
                        _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11,
                    );
                    leanh::lean_inc_ref(v_arg_3449_);
                    v___x_3510_ = l_Lean_Expr_app___override(v___x_3509_, v_arg_3449_);
                    v___x_3511_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3511_, 0, v___x_3510_);
                    v___x_3512_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3512_, 0, v_arg_3449_);
                    leanh::lean_ctor_set(v___x_3512_, 1, v___x_3511_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3512_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3459_,
                    );
                    v___x_3513_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3513_, 0, v___x_3512_);
                    if v_isShared_3456_ == 0 {
                        leanh::lean_ctor_set(v___x_3455_, 0, v___x_3513_);
                        v___x_3515_ = v___x_3455_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3516_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
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
                    v_reuseFailAlloc_3524_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
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
                            leanh::lean_dec_ref(v___x_3534_);
                            leanh::lean_del_object(v___x_3532_);
                            v___y_3451_ = v_a_3429_;
                            state = 5;
                            continue;
                        } else {
                            v_arg_3540_ = leanh::lean_ctor_get(v___x_3534_, 1);
                            leanh::lean_inc_ref(v_arg_3540_);
                            v___x_3541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3534_);
                            v___x_3542_ = l_Lean_Expr_isApp(v___x_3541_);
                            if v___x_3542_ == 0 {
                                leanh::lean_dec_ref(v___x_3541_);
                                leanh::lean_dec_ref(v_arg_3540_);
                                leanh::lean_del_object(v___x_3532_);
                                v___y_3451_ = v_a_3429_;
                                state = 5;
                                continue;
                            } else {
                                v_arg_3543_ = leanh::lean_ctor_get(v___x_3541_, 1);
                                leanh::lean_inc_ref(v_arg_3543_);
                                v___x_3544_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3541_);
                                v___x_3545_ = l_Lean_Expr_isConstOf(v___x_3544_, v___x_3527_);
                                leanh::lean_dec_ref(v___x_3544_);
                                if v___x_3545_ == 0 {
                                    leanh::lean_dec_ref(v_arg_3543_);
                                    leanh::lean_dec_ref(v_arg_3540_);
                                    leanh::lean_del_object(v___x_3532_);
                                    v___y_3451_ = v_a_3429_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_arg_3449_);
                                    leanh::lean_inc_ref(v_arg_3446_);
                                    leanh::lean_inc_ref(v_arg_3540_);
                                    v___x_3546_ = l_Lean_mkOr(v_arg_3540_, v_arg_3446_);
                                    leanh::lean_inc_ref(v_arg_3543_);
                                    v___x_3547_ = l_Lean_mkOr(v_arg_3543_, v___x_3546_);
                                    v___x_3548_ = leanh::lean_obj_once(
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
                                    v___x_3550_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3550_, 0, v___x_3549_);
                                    v___x_3551_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                                    leanh::lean_ctor_set(v___x_3551_, 0, v___x_3547_);
                                    leanh::lean_ctor_set(v___x_3551_, 1, v___x_3550_);
                                    leanh::lean_ctor_set_uint8(
                                        v___x_3551_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                            as u32,
                                        v___x_3545_,
                                    );
                                    v___x_3552_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3552_, 0, v___x_3551_);
                                    if v_isShared_3533_ == 0 {
                                        leanh::lean_ctor_set(v___x_3532_, 0, v___x_3552_);
                                        v___x_3554_ = v___x_3532_;
                                        state = 16;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3555_ =
                                            leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        leanh::lean_ctor_set(
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
                        leanh::lean_dec_ref(v___x_3534_);
                        v___x_3556_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__17),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpOr___redArg___closed__17_once
                            ),
                            _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17,
                        );
                        v___x_3557_ = l_Lean_Expr_app___override(v___x_3556_, v_arg_3446_);
                        v___x_3558_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3558_, 0, v___x_3557_);
                        v___x_3559_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        leanh::lean_ctor_set(v___x_3559_, 0, v_arg_3449_);
                        leanh::lean_ctor_set(v___x_3559_, 1, v___x_3558_);
                        leanh::lean_ctor_set_uint8(
                            v___x_3559_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v___x_3538_,
                        );
                        v___x_3560_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3560_, 0, v___x_3559_);
                        if v_isShared_3533_ == 0 {
                            leanh::lean_ctor_set(v___x_3532_, 0, v___x_3560_);
                            v___x_3562_ = v___x_3532_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_3563_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
                            v___x_3562_ = v_reuseFailAlloc_3563_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3534_);
                    leanh::lean_dec_ref(v_arg_3449_);
                    v___x_3564_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__20),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpOr___redArg___closed__20_once
                        ),
                        _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20,
                    );
                    leanh::lean_inc_ref(v_arg_3446_);
                    v___x_3565_ = l_Lean_Expr_app___override(v___x_3564_, v_arg_3446_);
                    v___x_3566_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3566_, 0, v___x_3565_);
                    v___x_3567_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3567_, 0, v_arg_3446_);
                    leanh::lean_ctor_set(v___x_3567_, 1, v___x_3566_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3567_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3536_,
                    );
                    v___x_3568_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3568_, 0, v___x_3567_);
                    if v_isShared_3533_ == 0 {
                        leanh::lean_ctor_set(v___x_3532_, 0, v___x_3568_);
                        v___x_3570_ = v___x_3532_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
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
                    v_reuseFailAlloc_3579_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
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
                    v_reuseFailAlloc_3588_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
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
    mut v_e_3590_: *mut leanh::LeanObject,
    mut v_a_3591_: *mut leanh::LeanObject,
    mut v_a_3592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3593_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_3590_, v_a_3591_);
    leanh::lean_dec(v_a_3591_);
    return v_res_3593_;
}
pub unsafe fn l_Lean_Meta_Grind_simpOr(
    mut v_e_3594_: *mut leanh::LeanObject,
    mut v_a_3595_: *mut leanh::LeanObject,
    mut v_a_3596_: *mut leanh::LeanObject,
    mut v_a_3597_: *mut leanh::LeanObject,
    mut v_a_3598_: *mut leanh::LeanObject,
    mut v_a_3599_: *mut leanh::LeanObject,
    mut v_a_3600_: *mut leanh::LeanObject,
    mut v_a_3601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_3594_, v_a_3599_);
    return v___x_3603_;
}
pub unsafe fn l_Lean_Meta_Grind_simpOr___boxed(
    mut v_e_3604_: *mut leanh::LeanObject,
    mut v_a_3605_: *mut leanh::LeanObject,
    mut v_a_3606_: *mut leanh::LeanObject,
    mut v_a_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
    mut v_a_3609_: *mut leanh::LeanObject,
    mut v_a_3610_: *mut leanh::LeanObject,
    mut v_a_3611_: *mut leanh::LeanObject,
    mut v_a_3612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_Meta_Grind_simpOr(
        v_e_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_,
    );
    leanh::lean_dec(v_a_3611_);
    leanh::lean_dec_ref(v_a_3610_);
    leanh::lean_dec(v_a_3609_);
    leanh::lean_dec_ref(v_a_3608_);
    leanh::lean_dec(v_a_3607_);
    leanh::lean_dec_ref(v_a_3606_);
    leanh::lean_dec(v_a_3605_);
    return v_res_3613_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_()
-> *mut leanh::LeanObject {
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3631_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_;
    v___x_3632_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_;
    v___x_3633_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_simpOr___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3634_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3631_, v___x_3632_, v___x_3633_);
    return v___x_3634_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11____boxed(
    mut v_a_3635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_h_3641_: *mut leanh::LeanObject,
    mut v___y_3642_: *mut leanh::LeanObject,
    mut v___y_3643_: *mut leanh::LeanObject,
    mut v___y_3644_: *mut leanh::LeanObject,
    mut v___y_3645_: *mut leanh::LeanObject,
    mut v___y_3646_: *mut leanh::LeanObject,
    mut v___y_3647_: *mut leanh::LeanObject,
    mut v___y_3648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v_trackZetaDelta_3687_: u8 = 0;
    let mut v_zetaDeltaSet_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3694_: u8 = 0;
    let mut v_inTypeClassResolution_3695_: u8 = 0;
    let mut v_cacheInferType_3696_: u8 = 0;
    let mut v___x_3697_: u8 = 0;
    let mut v_config_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: u64 = 0;
    let mut v___x_3701_: u64 = 0;
    let mut v___x_3702_: u64 = 0;
    let mut v___x_3703_: u64 = 0;
    let mut v___x_3704_: u64 = 0;
    let mut v_key_3705_: u64 = 0;
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3718_: u8 = 0;
    let mut v_reuseFailAlloc_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_a_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v_a_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3732_: u8 = 0;
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3650_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__9_once),
                    _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9,
                );
                leanh::lean_inc_ref(v_h_3641_);
                v___x_3657_ = l_Lean_Meta_mkNoConfusion(
                    v___x_3650_,
                    v_h_3641_,
                    v___y_3645_,
                    v___y_3646_,
                    v___y_3647_,
                    v___y_3648_,
                );
                if leanh::lean_obj_tag(v___x_3657_) == 0 {
                    v_a_3658_ = leanh::lean_ctor_get(v___x_3657_, 0);
                    leanh::lean_inc(v_a_3658_);
                    leanh::lean_dec_ref_known(v___x_3657_, 1);
                    v___x_3659_ = leanh::lean_unsigned_to_nat(1);
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
                    leanh::lean_dec_ref(v___x_3661_);
                    if leanh::lean_obj_tag(v___x_3663_) == 0 {
                        v_a_3664_ = leanh::lean_ctor_get(v___x_3663_, 0);
                        leanh::lean_inc(v_a_3664_);
                        leanh::lean_dec_ref_known(v___x_3663_, 1);
                        v___x_3665_ = l_Lean_Meta_Context_config(v___y_3645_);
                        v_foApprox_3666_ = leanh::lean_ctor_get_uint8(v___x_3665_, 0 as u32);
                        v_ctxApprox_3667_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 1 as u32);
                        v_quasiPatternApprox_3668_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 2 as u32);
                        v_constApprox_3669_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 3 as u32);
                        v_isDefEqStuckEx_3670_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 4 as u32);
                        v_unificationHints_3671_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 5 as u32);
                        v_proofIrrelevance_3672_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 6 as u32);
                        v_assignSyntheticOpaque_3673_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 7 as u32);
                        v_offsetCnstrs_3674_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 8 as u32);
                        v_etaStruct_3675_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 10 as u32);
                        v_univApprox_3676_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 11 as u32);
                        v_iota_3677_ = leanh::lean_ctor_get_uint8(v___x_3665_, 12 as u32);
                        v_beta_3678_ = leanh::lean_ctor_get_uint8(v___x_3665_, 13 as u32);
                        v_proj_3679_ = leanh::lean_ctor_get_uint8(v___x_3665_, 14 as u32);
                        v_zeta_3680_ = leanh::lean_ctor_get_uint8(v___x_3665_, 15 as u32);
                        v_zetaDelta_3681_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 16 as u32);
                        v_zetaUnused_3682_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 17 as u32);
                        v_zetaHave_3683_ =
                            leanh::lean_ctor_get_uint8(v___x_3665_, 18 as u32);
                        v_isSharedCheck_3720_ =
                            (!leanh::lean_is_exclusive(v___x_3665_)) as u8;
                        if v_isSharedCheck_3720_ == 0 {
                            v___x_3685_ = v___x_3665_;
                            v_isShared_3686_ = v_isSharedCheck_3720_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3665_);
                            v___x_3685_ = leanh::lean_box(0);
                            v_isShared_3686_ = v_isSharedCheck_3720_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3721_ = leanh::lean_ctor_get(v___x_3663_, 0);
                        v_isSharedCheck_3728_ =
                            (!leanh::lean_is_exclusive(v___x_3663_)) as u8;
                        if v_isSharedCheck_3728_ == 0 {
                            v___x_3723_ = v___x_3663_;
                            v_isShared_3724_ = v_isSharedCheck_3728_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3721_);
                            leanh::lean_dec(v___x_3663_);
                            v___x_3723_ = leanh::lean_box(0);
                            v_isShared_3724_ = v_isSharedCheck_3728_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_h_3641_);
                    v_a_3729_ = leanh::lean_ctor_get(v___x_3657_, 0);
                    v_isSharedCheck_3736_ = (!leanh::lean_is_exclusive(v___x_3657_)) as u8;
                    if v_isSharedCheck_3736_ == 0 {
                        v___x_3731_ = v___x_3657_;
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3729_);
                        leanh::lean_dec(v___x_3657_);
                        v___x_3731_ = leanh::lean_box(0);
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3653_, 0, v_a_3652_);
                v___x_3654_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3654_, 0, v___x_3650_);
                leanh::lean_ctor_set(v___x_3654_, 1, v___x_3653_);
                leanh::lean_ctor_set_uint8(
                    v___x_3654_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3640_,
                );
                v___x_3655_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3655_, 0, v___x_3654_);
                v___x_3656_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3656_, 0, v___x_3655_);
                return v___x_3656_;
            }
            2 => {
                v_trackZetaDelta_3687_ = leanh::lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3688_ = leanh::lean_ctor_get(v___y_3645_, 1);
                v_lctx_3689_ = leanh::lean_ctor_get(v___y_3645_, 2);
                v_localInstances_3690_ = leanh::lean_ctor_get(v___y_3645_, 3);
                v_defEqCtx_x3f_3691_ = leanh::lean_ctor_get(v___y_3645_, 4);
                v_synthPendingDepth_3692_ = leanh::lean_ctor_get(v___y_3645_, 5);
                v_canUnfold_x3f_3693_ = leanh::lean_ctor_get(v___y_3645_, 6);
                v_univApprox_3694_ = leanh::lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3695_ = leanh::lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3696_ = leanh::lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3697_ = 1;
                if v_isShared_3686_ == 0 {
                    v_config_3699_ = v___x_3685_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        0 as u32,
                        v_foApprox_3666_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        1 as u32,
                        v_ctxApprox_3667_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        2 as u32,
                        v_quasiPatternApprox_3668_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        3 as u32,
                        v_constApprox_3669_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        4 as u32,
                        v_isDefEqStuckEx_3670_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        5 as u32,
                        v_unificationHints_3671_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        6 as u32,
                        v_proofIrrelevance_3672_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        7 as u32,
                        v_assignSyntheticOpaque_3673_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        8 as u32,
                        v_offsetCnstrs_3674_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        10 as u32,
                        v_etaStruct_3675_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        11 as u32,
                        v_univApprox_3676_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        12 as u32,
                        v_iota_3677_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        13 as u32,
                        v_beta_3678_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        14 as u32,
                        v_proj_3679_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        15 as u32,
                        v_zeta_3680_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        16 as u32,
                        v_zetaDelta_3681_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        17 as u32,
                        v_zetaUnused_3682_,
                    );
                    leanh::lean_ctor_set_uint8(
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
                leanh::lean_ctor_set_uint8(v_config_3699_, 9 as u32, v___x_3697_);
                v___x_3700_ = l_Lean_Meta_Context_configKey(v___y_3645_);
                v___x_3701_ = 3u64;
                v___x_3702_ = lean_uint64_shift_right(v___x_3700_, v___x_3701_);
                v___x_3703_ = lean_uint64_shift_left(v___x_3702_, v___x_3701_);
                v___x_3704_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0_once
                    ),
                    _init_l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0,
                );
                v_key_3705_ = lean_uint64_lor(v___x_3703_, v___x_3704_);
                v___x_3706_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_3706_, 0, v_config_3699_);
                leanh::lean_ctor_set_uint64(
                    v___x_3706_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_3705_,
                );
                leanh::lean_inc(v_canUnfold_x3f_3693_);
                leanh::lean_inc(v_synthPendingDepth_3692_);
                leanh::lean_inc(v_defEqCtx_x3f_3691_);
                leanh::lean_inc_ref(v_localInstances_3690_);
                leanh::lean_inc_ref(v_lctx_3689_);
                leanh::lean_inc(v_zetaDeltaSet_3688_);
                v___x_3707_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_3707_, 0, v___x_3706_);
                leanh::lean_ctor_set(v___x_3707_, 1, v_zetaDeltaSet_3688_);
                leanh::lean_ctor_set(v___x_3707_, 2, v_lctx_3689_);
                leanh::lean_ctor_set(v___x_3707_, 3, v_localInstances_3690_);
                leanh::lean_ctor_set(v___x_3707_, 4, v_defEqCtx_x3f_3691_);
                leanh::lean_ctor_set(v___x_3707_, 5, v_synthPendingDepth_3692_);
                leanh::lean_ctor_set(v___x_3707_, 6, v_canUnfold_x3f_3693_);
                leanh::lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3687_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3694_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3695_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3696_,
                );
                v___x_3708_ = l_Lean_Meta_mkEqFalse_x27(
                    v_a_3664_,
                    v___x_3707_,
                    v___y_3646_,
                    v___y_3647_,
                    v___y_3648_,
                );
                leanh::lean_dec_ref_known(v___x_3707_, 7);
                if leanh::lean_obj_tag(v___x_3708_) == 0 {
                    v_a_3709_ = leanh::lean_ctor_get(v___x_3708_, 0);
                    leanh::lean_inc(v_a_3709_);
                    leanh::lean_dec_ref_known(v___x_3708_, 1);
                    v_a_3652_ = v_a_3709_;
                    state = 1;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_3708_) == 0 {
                        v_a_3710_ = leanh::lean_ctor_get(v___x_3708_, 0);
                        leanh::lean_inc(v_a_3710_);
                        leanh::lean_dec_ref_known(v___x_3708_, 1);
                        v_a_3652_ = v_a_3710_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3711_ = leanh::lean_ctor_get(v___x_3708_, 0);
                        v_isSharedCheck_3718_ =
                            (!leanh::lean_is_exclusive(v___x_3708_)) as u8;
                        if v_isSharedCheck_3718_ == 0 {
                            v___x_3713_ = v___x_3708_;
                            v_isShared_3714_ = v_isSharedCheck_3718_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3711_);
                            leanh::lean_dec(v___x_3708_);
                            v___x_3713_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3717_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
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
                    v_reuseFailAlloc_3727_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
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
                    v_reuseFailAlloc_3735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
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
    mut v___x_3737_: *mut leanh::LeanObject,
    mut v___x_3738_: *mut leanh::LeanObject,
    mut v_h_3739_: *mut leanh::LeanObject,
    mut v___y_3740_: *mut leanh::LeanObject,
    mut v___y_3741_: *mut leanh::LeanObject,
    mut v___y_3742_: *mut leanh::LeanObject,
    mut v___y_3743_: *mut leanh::LeanObject,
    mut v___y_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_18057__boxed_3748_: u8 = 0;
    let mut v___x_18058__boxed_3749_: u8 = 0;
    let mut v_res_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_18057__boxed_3748_ = (leanh::lean_unbox(v___x_3737_) as u8);
    v___x_18058__boxed_3749_ = (leanh::lean_unbox(v___x_3738_) as u8);
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
    leanh::lean_dec(v___y_3746_);
    leanh::lean_dec_ref(v___y_3745_);
    leanh::lean_dec(v___y_3744_);
    leanh::lean_dec_ref(v___y_3743_);
    leanh::lean_dec(v___y_3742_);
    leanh::lean_dec_ref(v___y_3741_);
    leanh::lean_dec(v___y_3740_);
    return v_res_3750_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(
    mut v_k_3751_: *mut leanh::LeanObject,
    mut v___y_3752_: *mut leanh::LeanObject,
    mut v___y_3753_: *mut leanh::LeanObject,
    mut v___y_3754_: *mut leanh::LeanObject,
    mut v_b_3755_: *mut leanh::LeanObject,
    mut v___y_3756_: *mut leanh::LeanObject,
    mut v___y_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3759_);
    leanh::lean_inc_ref(v___y_3758_);
    leanh::lean_inc(v___y_3757_);
    leanh::lean_inc_ref(v___y_3756_);
    leanh::lean_inc(v___y_3754_);
    leanh::lean_inc_ref(v___y_3753_);
    leanh::lean_inc(v___y_3752_);
    v___x_3761_ = leanh::lean_apply_9(
        v_k_3751_,
        v_b_3755_,
        v___y_3752_,
        v___y_3753_,
        v___y_3754_,
        v___y_3756_,
        v___y_3757_,
        v___y_3758_,
        v___y_3759_,
        leanh::lean_box(0),
    );
    return v___x_3761_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_3762_: *mut leanh::LeanObject,
    mut v___y_3763_: *mut leanh::LeanObject,
    mut v___y_3764_: *mut leanh::LeanObject,
    mut v___y_3765_: *mut leanh::LeanObject,
    mut v_b_3766_: *mut leanh::LeanObject,
    mut v___y_3767_: *mut leanh::LeanObject,
    mut v___y_3768_: *mut leanh::LeanObject,
    mut v___y_3769_: *mut leanh::LeanObject,
    mut v___y_3770_: *mut leanh::LeanObject,
    mut v___y_3771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(v_k_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v_b_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
    leanh::lean_dec(v___y_3770_);
    leanh::lean_dec_ref(v___y_3769_);
    leanh::lean_dec(v___y_3768_);
    leanh::lean_dec_ref(v___y_3767_);
    leanh::lean_dec(v___y_3765_);
    leanh::lean_dec_ref(v___y_3764_);
    leanh::lean_dec(v___y_3763_);
    return v_res_3772_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(
    mut v_name_3773_: *mut leanh::LeanObject,
    mut v_bi_3774_: u8,
    mut v_type_3775_: *mut leanh::LeanObject,
    mut v_k_3776_: *mut leanh::LeanObject,
    mut v_kind_3777_: u8,
    mut v___y_3778_: *mut leanh::LeanObject,
    mut v___y_3779_: *mut leanh::LeanObject,
    mut v___y_3780_: *mut leanh::LeanObject,
    mut v___y_3781_: *mut leanh::LeanObject,
    mut v___y_3782_: *mut leanh::LeanObject,
    mut v___y_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3780_);
                leanh::lean_inc_ref(v___y_3779_);
                leanh::lean_inc(v___y_3778_);
                v___f_3786_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                leanh::lean_closure_set(v___f_3786_, 0, v_k_3776_);
                leanh::lean_closure_set(v___f_3786_, 1, v___y_3778_);
                leanh::lean_closure_set(v___f_3786_, 2, v___y_3779_);
                leanh::lean_closure_set(v___f_3786_, 3, v___y_3780_);
                v___x_3787_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
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
                if leanh::lean_obj_tag(v___x_3787_) == 0 {
                    return v___x_3787_;
                } else {
                    v_a_3788_ = leanh::lean_ctor_get(v___x_3787_, 0);
                    v_isSharedCheck_3795_ = (!leanh::lean_is_exclusive(v___x_3787_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v___x_3790_ = v___x_3787_;
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3788_);
                        leanh::lean_dec(v___x_3787_);
                        v___x_3790_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3794_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
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
    mut v_name_3796_: *mut leanh::LeanObject,
    mut v_bi_3797_: *mut leanh::LeanObject,
    mut v_type_3798_: *mut leanh::LeanObject,
    mut v_k_3799_: *mut leanh::LeanObject,
    mut v_kind_3800_: *mut leanh::LeanObject,
    mut v___y_3801_: *mut leanh::LeanObject,
    mut v___y_3802_: *mut leanh::LeanObject,
    mut v___y_3803_: *mut leanh::LeanObject,
    mut v___y_3804_: *mut leanh::LeanObject,
    mut v___y_3805_: *mut leanh::LeanObject,
    mut v___y_3806_: *mut leanh::LeanObject,
    mut v___y_3807_: *mut leanh::LeanObject,
    mut v___y_3808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3809_: u8 = 0;
    let mut v_kind_boxed_3810_: u8 = 0;
    let mut v_res_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3809_ = (leanh::lean_unbox(v_bi_3797_) as u8);
    v_kind_boxed_3810_ = (leanh::lean_unbox(v_kind_3800_) as u8);
    v_res_3811_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_3796_, v_bi_boxed_3809_, v_type_3798_, v_k_3799_, v_kind_boxed_3810_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
    leanh::lean_dec(v___y_3807_);
    leanh::lean_dec_ref(v___y_3806_);
    leanh::lean_dec(v___y_3805_);
    leanh::lean_dec_ref(v___y_3804_);
    leanh::lean_dec(v___y_3803_);
    leanh::lean_dec_ref(v___y_3802_);
    leanh::lean_dec(v___y_3801_);
    return v_res_3811_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(
    mut v_name_3812_: *mut leanh::LeanObject,
    mut v_type_3813_: *mut leanh::LeanObject,
    mut v_k_3814_: *mut leanh::LeanObject,
    mut v___y_3815_: *mut leanh::LeanObject,
    mut v___y_3816_: *mut leanh::LeanObject,
    mut v___y_3817_: *mut leanh::LeanObject,
    mut v___y_3818_: *mut leanh::LeanObject,
    mut v___y_3819_: *mut leanh::LeanObject,
    mut v___y_3820_: *mut leanh::LeanObject,
    mut v___y_3821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = 0;
    v___x_3824_ = 0;
    v___x_3825_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_3812_, v___x_3823_, v_type_3813_, v_k_3814_, v___x_3824_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
    return v___x_3825_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg___boxed(
    mut v_name_3826_: *mut leanh::LeanObject,
    mut v_type_3827_: *mut leanh::LeanObject,
    mut v_k_3828_: *mut leanh::LeanObject,
    mut v___y_3829_: *mut leanh::LeanObject,
    mut v___y_3830_: *mut leanh::LeanObject,
    mut v___y_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3835_);
    leanh::lean_dec_ref(v___y_3834_);
    leanh::lean_dec(v___y_3833_);
    leanh::lean_dec_ref(v___y_3832_);
    leanh::lean_dec(v___y_3831_);
    leanh::lean_dec_ref(v___y_3830_);
    leanh::lean_dec(v___y_3829_);
    return v_res_3837_;
}
pub unsafe fn l_Lean_Meta_Grind_reduceCtorEqCheap(
    mut v_e_3841_: *mut leanh::LeanObject,
    mut v_a_3842_: *mut leanh::LeanObject,
    mut v_a_3843_: *mut leanh::LeanObject,
    mut v_a_3844_: *mut leanh::LeanObject,
    mut v_a_3845_: *mut leanh::LeanObject,
    mut v_a_3846_: *mut leanh::LeanObject,
    mut v_a_3847_: *mut leanh::LeanObject,
    mut v_a_3848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3854_: u8 = 0;
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: u8 = 0;
    let mut v_arg_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v_arg_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: u8 = 0;
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3875_: u8 = 0;
    let mut v_val_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3881_: u8 = 0;
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: u8 = 0;
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut v_a_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v_a_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3919_: u8 = 0;
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3923_: u8 = 0;
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_a_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_3841_);
                v___x_3850_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3841_, v_a_3846_);
                if leanh::lean_obj_tag(v___x_3850_) == 0 {
                    v_a_3851_ = leanh::lean_ctor_get(v___x_3850_, 0);
                    v_isSharedCheck_3924_ = (!leanh::lean_is_exclusive(v___x_3850_)) as u8;
                    if v_isSharedCheck_3924_ == 0 {
                        v___x_3853_ = v___x_3850_;
                        v_isShared_3854_ = v_isSharedCheck_3924_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3851_);
                        leanh::lean_dec(v___x_3850_);
                        v___x_3853_ = leanh::lean_box(0);
                        v_isShared_3854_ = v_isSharedCheck_3924_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3841_);
                    v_a_3925_ = leanh::lean_ctor_get(v___x_3850_, 0);
                    v_isSharedCheck_3932_ = (!leanh::lean_is_exclusive(v___x_3850_)) as u8;
                    if v_isSharedCheck_3932_ == 0 {
                        v___x_3927_ = v___x_3850_;
                        v_isShared_3928_ = v_isSharedCheck_3932_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3925_);
                        leanh::lean_dec(v___x_3850_);
                        v___x_3927_ = leanh::lean_box(0);
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
                    leanh::lean_dec_ref(v___x_3860_);
                    leanh::lean_dec_ref(v_e_3841_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3862_ = leanh::lean_ctor_get(v___x_3860_, 1);
                    leanh::lean_inc_ref(v_arg_3862_);
                    v___x_3863_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3860_);
                    v___x_3864_ = l_Lean_Expr_isApp(v___x_3863_);
                    if v___x_3864_ == 0 {
                        leanh::lean_dec_ref(v___x_3863_);
                        leanh::lean_dec_ref(v_arg_3862_);
                        leanh::lean_dec_ref(v_e_3841_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_3865_ = leanh::lean_ctor_get(v___x_3863_, 1);
                        leanh::lean_inc_ref(v_arg_3865_);
                        v___x_3866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3863_);
                        v___x_3867_ = l_Lean_Expr_isApp(v___x_3866_);
                        if v___x_3867_ == 0 {
                            leanh::lean_dec_ref(v___x_3866_);
                            leanh::lean_dec_ref(v_arg_3865_);
                            leanh::lean_dec_ref(v_arg_3862_);
                            leanh::lean_dec_ref(v_e_3841_);
                            state = 2;
                            continue;
                        } else {
                            v___x_3868_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3866_);
                            v___x_3869_ = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
                            v___x_3870_ = l_Lean_Expr_isConstOf(v___x_3868_, v___x_3869_);
                            leanh::lean_dec_ref(v___x_3868_);
                            if v___x_3870_ == 0 {
                                leanh::lean_dec_ref(v_arg_3865_);
                                leanh::lean_dec_ref(v_arg_3862_);
                                leanh::lean_dec_ref(v_e_3841_);
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_3853_);
                                v___x_3871_ = l_Lean_Meta_isConstructorApp_x3f(
                                    v_arg_3865_,
                                    v_a_3845_,
                                    v_a_3846_,
                                    v_a_3847_,
                                    v_a_3848_,
                                );
                                if leanh::lean_obj_tag(v___x_3871_) == 0 {
                                    v_a_3872_ = leanh::lean_ctor_get(v___x_3871_, 0);
                                    v_isSharedCheck_3915_ =
                                        (!leanh::lean_is_exclusive(v___x_3871_)) as u8;
                                    if v_isSharedCheck_3915_ == 0 {
                                        v___x_3874_ = v___x_3871_;
                                        v_isShared_3875_ = v_isSharedCheck_3915_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3872_);
                                        leanh::lean_dec(v___x_3871_);
                                        v___x_3874_ = leanh::lean_box(0);
                                        v_isShared_3875_ = v_isSharedCheck_3915_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_3862_);
                                    leanh::lean_dec_ref(v_e_3841_);
                                    v_a_3916_ = leanh::lean_ctor_get(v___x_3871_, 0);
                                    v_isSharedCheck_3923_ =
                                        (!leanh::lean_is_exclusive(v___x_3871_)) as u8;
                                    if v_isSharedCheck_3923_ == 0 {
                                        v___x_3918_ = v___x_3871_;
                                        v_isShared_3919_ = v_isSharedCheck_3923_;
                                        state = 12;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3916_);
                                        leanh::lean_dec(v___x_3871_);
                                        v___x_3918_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3853_, 0, v___x_3856_);
                    v___x_3858_ = v___x_3853_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3859_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
                    v___x_3858_ = v_reuseFailAlloc_3859_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3858_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_3872_) == 1 {
                    v_val_3876_ = leanh::lean_ctor_get(v_a_3872_, 0);
                    leanh::lean_inc(v_val_3876_);
                    leanh::lean_dec_ref_known(v_a_3872_, 1);
                    v___x_3877_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_arg_3862_,
                        v_a_3845_,
                        v_a_3846_,
                        v_a_3847_,
                        v_a_3848_,
                    );
                    if leanh::lean_obj_tag(v___x_3877_) == 0 {
                        v_a_3878_ = leanh::lean_ctor_get(v___x_3877_, 0);
                        v_isSharedCheck_3902_ =
                            (!leanh::lean_is_exclusive(v___x_3877_)) as u8;
                        if v_isSharedCheck_3902_ == 0 {
                            v___x_3880_ = v___x_3877_;
                            v_isShared_3881_ = v_isSharedCheck_3902_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3878_);
                            leanh::lean_dec(v___x_3877_);
                            v___x_3880_ = leanh::lean_box(0);
                            v_isShared_3881_ = v_isSharedCheck_3902_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_3876_);
                        leanh::lean_del_object(v___x_3874_);
                        leanh::lean_dec_ref(v_e_3841_);
                        v_a_3903_ = leanh::lean_ctor_get(v___x_3877_, 0);
                        v_isSharedCheck_3910_ =
                            (!leanh::lean_is_exclusive(v___x_3877_)) as u8;
                        if v_isSharedCheck_3910_ == 0 {
                            v___x_3905_ = v___x_3877_;
                            v_isShared_3906_ = v_isSharedCheck_3910_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3903_);
                            leanh::lean_dec(v___x_3877_);
                            v___x_3905_ = leanh::lean_box(0);
                            v_isShared_3906_ = v_isSharedCheck_3910_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3872_);
                    leanh::lean_dec_ref(v_arg_3862_);
                    leanh::lean_dec_ref(v_e_3841_);
                    v___x_3911_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    if v_isShared_3875_ == 0 {
                        leanh::lean_ctor_set(v___x_3874_, 0, v___x_3911_);
                        v___x_3913_ = v___x_3874_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
                        v___x_3913_ = v_reuseFailAlloc_3914_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_3878_) == 1 {
                    leanh::lean_del_object(v___x_3874_);
                    v_toConstantVal_3887_ = leanh::lean_ctor_get(v_val_3876_, 0);
                    leanh::lean_inc_ref(v_toConstantVal_3887_);
                    leanh::lean_dec(v_val_3876_);
                    v_val_3888_ = leanh::lean_ctor_get(v_a_3878_, 0);
                    leanh::lean_inc(v_val_3888_);
                    leanh::lean_dec_ref_known(v_a_3878_, 1);
                    v_toConstantVal_3889_ = leanh::lean_ctor_get(v_val_3888_, 0);
                    leanh::lean_inc_ref(v_toConstantVal_3889_);
                    leanh::lean_dec(v_val_3888_);
                    v_name_3890_ = leanh::lean_ctor_get(v_toConstantVal_3887_, 0);
                    leanh::lean_inc(v_name_3890_);
                    leanh::lean_dec_ref(v_toConstantVal_3887_);
                    v_name_3891_ = leanh::lean_ctor_get(v_toConstantVal_3889_, 0);
                    leanh::lean_inc(v_name_3891_);
                    leanh::lean_dec_ref(v_toConstantVal_3889_);
                    v___x_3892_ = lean_name_eq(v_name_3890_, v_name_3891_);
                    leanh::lean_dec(v_name_3891_);
                    leanh::lean_dec(v_name_3890_);
                    if v___x_3892_ == 0 {
                        if v___x_3870_ == 0 {
                            leanh::lean_dec_ref(v_e_3841_);
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_3880_);
                            v___x_3893_ = leanh::lean_box((v___x_3892_) as usize);
                            v___x_3894_ = leanh::lean_box((v___x_3870_) as usize);
                            v___f_3895_ = leanh::lean_alloc_closure(
                                l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                2,
                            );
                            leanh::lean_closure_set(v___f_3895_, 0, v___x_3893_);
                            leanh::lean_closure_set(v___f_3895_, 1, v___x_3894_);
                            v___x_3896_ = l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1;
                            v___x_3897_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v___x_3896_, v_e_3841_, v___f_3895_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
                            return v___x_3897_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_3841_);
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3880_);
                    leanh::lean_dec(v_a_3878_);
                    leanh::lean_dec(v_val_3876_);
                    leanh::lean_dec_ref(v_e_3841_);
                    v___x_3898_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    if v_isShared_3875_ == 0 {
                        leanh::lean_ctor_set(v___x_3874_, 0, v___x_3898_);
                        v___x_3900_ = v___x_3874_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3901_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
                        v___x_3900_ = v_reuseFailAlloc_3901_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3883_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_3881_ == 0 {
                    leanh::lean_ctor_set(v___x_3880_, 0, v___x_3883_);
                    v___x_3885_ = v___x_3880_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3886_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
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
                    v_reuseFailAlloc_3909_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
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
                    v_reuseFailAlloc_3922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
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
                    v_reuseFailAlloc_3931_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
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
    mut v_e_3933_: *mut leanh::LeanObject,
    mut v_a_3934_: *mut leanh::LeanObject,
    mut v_a_3935_: *mut leanh::LeanObject,
    mut v_a_3936_: *mut leanh::LeanObject,
    mut v_a_3937_: *mut leanh::LeanObject,
    mut v_a_3938_: *mut leanh::LeanObject,
    mut v_a_3939_: *mut leanh::LeanObject,
    mut v_a_3940_: *mut leanh::LeanObject,
    mut v_a_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3942_ = l_Lean_Meta_Grind_reduceCtorEqCheap(
        v_e_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_,
    );
    leanh::lean_dec(v_a_3940_);
    leanh::lean_dec_ref(v_a_3939_);
    leanh::lean_dec(v_a_3938_);
    leanh::lean_dec_ref(v_a_3937_);
    leanh::lean_dec(v_a_3936_);
    leanh::lean_dec_ref(v_a_3935_);
    leanh::lean_dec(v_a_3934_);
    return v_res_3942_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(
    mut v_00_u03b1_3943_: *mut leanh::LeanObject,
    mut v_name_3944_: *mut leanh::LeanObject,
    mut v_bi_3945_: u8,
    mut v_type_3946_: *mut leanh::LeanObject,
    mut v_k_3947_: *mut leanh::LeanObject,
    mut v_kind_3948_: u8,
    mut v___y_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3957_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_3944_, v_bi_3945_, v_type_3946_, v_k_3947_, v_kind_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    return v___x_3957_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___boxed(
    mut v_00_u03b1_3958_: *mut leanh::LeanObject,
    mut v_name_3959_: *mut leanh::LeanObject,
    mut v_bi_3960_: *mut leanh::LeanObject,
    mut v_type_3961_: *mut leanh::LeanObject,
    mut v_k_3962_: *mut leanh::LeanObject,
    mut v_kind_3963_: *mut leanh::LeanObject,
    mut v___y_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
    mut v___y_3967_: *mut leanh::LeanObject,
    mut v___y_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
    mut v___y_3971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3972_: u8 = 0;
    let mut v_kind_boxed_3973_: u8 = 0;
    let mut v_res_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3972_ = (leanh::lean_unbox(v_bi_3960_) as u8);
    v_kind_boxed_3973_ = (leanh::lean_unbox(v_kind_3963_) as u8);
    v_res_3974_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(v_00_u03b1_3958_, v_name_3959_, v_bi_boxed_3972_, v_type_3961_, v_k_3962_, v_kind_boxed_3973_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
    leanh::lean_dec(v___y_3970_);
    leanh::lean_dec_ref(v___y_3969_);
    leanh::lean_dec(v___y_3968_);
    leanh::lean_dec_ref(v___y_3967_);
    leanh::lean_dec(v___y_3966_);
    leanh::lean_dec_ref(v___y_3965_);
    leanh::lean_dec(v___y_3964_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(
    mut v_00_u03b1_3975_: *mut leanh::LeanObject,
    mut v_name_3976_: *mut leanh::LeanObject,
    mut v_type_3977_: *mut leanh::LeanObject,
    mut v_k_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
    mut v___y_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
    mut v___y_3985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3988_: *mut leanh::LeanObject,
    mut v_name_3989_: *mut leanh::LeanObject,
    mut v_type_3990_: *mut leanh::LeanObject,
    mut v_k_3991_: *mut leanh::LeanObject,
    mut v___y_3992_: *mut leanh::LeanObject,
    mut v___y_3993_: *mut leanh::LeanObject,
    mut v___y_3994_: *mut leanh::LeanObject,
    mut v___y_3995_: *mut leanh::LeanObject,
    mut v___y_3996_: *mut leanh::LeanObject,
    mut v___y_3997_: *mut leanh::LeanObject,
    mut v___y_3998_: *mut leanh::LeanObject,
    mut v___y_3999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3998_);
    leanh::lean_dec_ref(v___y_3997_);
    leanh::lean_dec(v___y_3996_);
    leanh::lean_dec_ref(v___y_3995_);
    leanh::lean_dec(v___y_3994_);
    leanh::lean_dec_ref(v___y_3993_);
    leanh::lean_dec(v___y_3992_);
    return v_res_4000_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4008_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_;
    v___x_4009_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
    v___x_4010_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_reduceCtorEqCheap___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4011_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4008_, v___x_4009_, v___x_4010_);
    return v___x_4011_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13____boxed(
    mut v_a_4012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4013_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_();
    return v_res_4013_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(
    mut v_e_4014_: *mut leanh::LeanObject,
    mut v_a_4015_: *mut leanh::LeanObject,
    mut v_a_4016_: *mut leanh::LeanObject,
    mut v_a_4017_: *mut leanh::LeanObject,
    mut v_a_4018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4020_ =
        l_Lean_Meta_Sym_unfoldReducibleStep(v_e_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
    return v___x_4020_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg___boxed(
    mut v_e_4021_: *mut leanh::LeanObject,
    mut v_a_4022_: *mut leanh::LeanObject,
    mut v_a_4023_: *mut leanh::LeanObject,
    mut v_a_4024_: *mut leanh::LeanObject,
    mut v_a_4025_: *mut leanh::LeanObject,
    mut v_a_4026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4027_ = l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(
        v_e_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_,
    );
    leanh::lean_dec(v_a_4025_);
    leanh::lean_dec_ref(v_a_4024_);
    leanh::lean_dec(v_a_4023_);
    leanh::lean_dec_ref(v_a_4022_);
    return v_res_4027_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc(
    mut v_e_4028_: *mut leanh::LeanObject,
    mut v_a_4029_: *mut leanh::LeanObject,
    mut v_a_4030_: *mut leanh::LeanObject,
    mut v_a_4031_: *mut leanh::LeanObject,
    mut v_a_4032_: *mut leanh::LeanObject,
    mut v_a_4033_: *mut leanh::LeanObject,
    mut v_a_4034_: *mut leanh::LeanObject,
    mut v_a_4035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4037_ =
        l_Lean_Meta_Sym_unfoldReducibleStep(v_e_4028_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
    return v___x_4037_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc___boxed(
    mut v_e_4038_: *mut leanh::LeanObject,
    mut v_a_4039_: *mut leanh::LeanObject,
    mut v_a_4040_: *mut leanh::LeanObject,
    mut v_a_4041_: *mut leanh::LeanObject,
    mut v_a_4042_: *mut leanh::LeanObject,
    mut v_a_4043_: *mut leanh::LeanObject,
    mut v_a_4044_: *mut leanh::LeanObject,
    mut v_a_4045_: *mut leanh::LeanObject,
    mut v_a_4046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4047_ = l_Lean_Meta_Grind_unfoldReducibleSimproc(
        v_e_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_,
    );
    leanh::lean_dec(v_a_4045_);
    leanh::lean_dec_ref(v_a_4044_);
    leanh::lean_dec(v_a_4043_);
    leanh::lean_dec_ref(v_a_4042_);
    leanh::lean_dec(v_a_4041_);
    leanh::lean_dec_ref(v_a_4040_);
    leanh::lean_dec(v_a_4039_);
    return v_res_4047_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_(
    mut v___y_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
    mut v___y_4051_: *mut leanh::LeanObject,
    mut v___y_4052_: *mut leanh::LeanObject,
    mut v___y_4053_: *mut leanh::LeanObject,
    mut v___y_4054_: *mut leanh::LeanObject,
    mut v___y_4055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v___y_4058_: *mut leanh::LeanObject,
    mut v___y_4059_: *mut leanh::LeanObject,
    mut v___y_4060_: *mut leanh::LeanObject,
    mut v___y_4061_: *mut leanh::LeanObject,
    mut v___y_4062_: *mut leanh::LeanObject,
    mut v___y_4063_: *mut leanh::LeanObject,
    mut v___y_4064_: *mut leanh::LeanObject,
    mut v___y_4065_: *mut leanh::LeanObject,
    mut v___y_4066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4067_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_(v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
    leanh::lean_dec(v___y_4065_);
    leanh::lean_dec_ref(v___y_4064_);
    leanh::lean_dec(v___y_4063_);
    leanh::lean_dec_ref(v___y_4062_);
    leanh::lean_dec(v___y_4061_);
    leanh::lean_dec_ref(v___y_4060_);
    leanh::lean_dec(v___y_4059_);
    return v_res_4067_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_()
-> *mut leanh::LeanObject {
    let mut v___f_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4080_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
    v___x_4081_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
    v___x_4082_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
    v___x_4083_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4081_, v___x_4082_, v___f_4080_);
    return v___x_4083_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9____boxed(
    mut v_a_4084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4085_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_();
    return v_res_4085_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs___redArg(
    mut v_a_4094_: *mut leanh::LeanObject,
    mut v_a_4095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut v_a_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v_a_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4172_: u8 = 0;
    let mut v_a_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4180_: u8 = 0;
    let mut v_a_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4184_: u8 = 0;
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4188_: u8 = 0;
    let mut v_a_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4196_: u8 = 0;
    let mut v_a_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v_a_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4208_: u8 = 0;
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_a_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v_a_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4097_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_4095_);
                if leanh::lean_obj_tag(v___x_4097_) == 0 {
                    v_a_4098_ = leanh::lean_ctor_get(v___x_4097_, 0);
                    leanh::lean_inc(v_a_4098_);
                    leanh::lean_dec_ref_known(v___x_4097_, 1);
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
                    if leanh::lean_obj_tag(v___x_4105_) == 0 {
                        v_a_4106_ = leanh::lean_ctor_get(v___x_4105_, 0);
                        leanh::lean_inc(v_a_4106_);
                        leanh::lean_dec_ref_known(v___x_4105_, 1);
                        v___x_4107_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(
                            v_a_4106_, v_a_4094_, v_a_4095_,
                        );
                        if leanh::lean_obj_tag(v___x_4107_) == 0 {
                            v_a_4108_ = leanh::lean_ctor_get(v___x_4107_, 0);
                            leanh::lean_inc(v_a_4108_);
                            leanh::lean_dec_ref_known(v___x_4107_, 1);
                            v___x_4109_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(
                                v_a_4108_, v_a_4094_, v_a_4095_,
                            );
                            if leanh::lean_obj_tag(v___x_4109_) == 0 {
                                v_a_4110_ = leanh::lean_ctor_get(v___x_4109_, 0);
                                leanh::lean_inc(v_a_4110_);
                                leanh::lean_dec_ref_known(v___x_4109_, 1);
                                v___x_4111_ = l_Lean_Meta_Grind_Arith_addSimproc(
                                    v_a_4110_, v_a_4094_, v_a_4095_,
                                );
                                if leanh::lean_obj_tag(v___x_4111_) == 0 {
                                    v_a_4112_ = leanh::lean_ctor_get(v___x_4111_, 0);
                                    leanh::lean_inc(v_a_4112_);
                                    leanh::lean_dec_ref_known(v___x_4111_, 1);
                                    v___x_4113_ = l_Lean_Meta_Grind_addForallSimproc(
                                        v_a_4112_, v_a_4094_, v_a_4095_,
                                    );
                                    if leanh::lean_obj_tag(v___x_4113_) == 0 {
                                        v_a_4114_ = leanh::lean_ctor_get(v___x_4113_, 0);
                                        leanh::lean_inc(v_a_4114_);
                                        leanh::lean_dec_ref_known(v___x_4113_, 1);
                                        v___x_4115_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
                                        v___x_4116_ = l_Lean_Meta_Simp_Simprocs_add(
                                            v_a_4114_,
                                            v___x_4115_,
                                            v___x_4104_,
                                            v_a_4094_,
                                            v_a_4095_,
                                        );
                                        if leanh::lean_obj_tag(v___x_4116_) == 0 {
                                            v_a_4117_ = leanh::lean_ctor_get(v___x_4116_, 0);
                                            leanh::lean_inc(v_a_4117_);
                                            leanh::lean_dec_ref_known(v___x_4116_, 1);
                                            v___x_4118_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_;
                                            v___x_4119_ = l_Lean_Meta_Simp_Simprocs_add(
                                                v_a_4117_,
                                                v___x_4118_,
                                                v___x_4104_,
                                                v_a_4094_,
                                                v_a_4095_,
                                            );
                                            if leanh::lean_obj_tag(v___x_4119_) == 0 {
                                                v_a_4120_ =
                                                    leanh::lean_ctor_get(v___x_4119_, 0);
                                                leanh::lean_inc(v_a_4120_);
                                                leanh::lean_dec_ref_known(v___x_4119_, 1);
                                                v___x_4121_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_;
                                                v___x_4122_ = l_Lean_Meta_Simp_Simprocs_add(
                                                    v_a_4120_,
                                                    v___x_4121_,
                                                    v___x_4104_,
                                                    v_a_4094_,
                                                    v_a_4095_,
                                                );
                                                if leanh::lean_obj_tag(v___x_4122_) == 0 {
                                                    v_a_4123_ =
                                                        leanh::lean_ctor_get(v___x_4122_, 0);
                                                    leanh::lean_inc(v_a_4123_);
                                                    leanh::lean_dec_ref_known(
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
                                                    if leanh::lean_obj_tag(v___x_4126_) == 0
                                                    {
                                                        v_a_4127_ = leanh::lean_ctor_get(
                                                            v___x_4126_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_4127_);
                                                        leanh::lean_dec_ref_known(
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
                                                        if leanh::lean_obj_tag(v___x_4129_)
                                                            == 0
                                                        {
                                                            v_a_4130_ = leanh::lean_ctor_get(
                                                                v___x_4129_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4140_ =
                                                                (!leanh::lean_is_exclusive(
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
                                                                leanh::lean_inc(v_a_4130_);
                                                                leanh::lean_dec(v___x_4129_);
                                                                v___x_4132_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_4133_ =
                                                                    v_isSharedCheck_4140_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_4141_ = leanh::lean_ctor_get(
                                                                v___x_4129_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4148_ =
                                                                (!leanh::lean_is_exclusive(
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
                                                                leanh::lean_inc(v_a_4141_);
                                                                leanh::lean_dec(v___x_4129_);
                                                                v___x_4143_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_4144_ =
                                                                    v_isSharedCheck_4148_;
                                                                state = 3;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        v_a_4149_ = leanh::lean_ctor_get(
                                                            v___x_4126_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4156_ =
                                                            (!leanh::lean_is_exclusive(
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
                                                            leanh::lean_inc(v_a_4149_);
                                                            leanh::lean_dec(v___x_4126_);
                                                            v___x_4151_ = leanh::lean_box(0);
                                                            v_isShared_4152_ =
                                                                v_isSharedCheck_4156_;
                                                            state = 5;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    v_a_4157_ =
                                                        leanh::lean_ctor_get(v___x_4122_, 0);
                                                    v_isSharedCheck_4164_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4122_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4164_ == 0 {
                                                        v___x_4159_ = v___x_4122_;
                                                        v_isShared_4160_ = v_isSharedCheck_4164_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_4157_);
                                                        leanh::lean_dec(v___x_4122_);
                                                        v___x_4159_ = leanh::lean_box(0);
                                                        v_isShared_4160_ = v_isSharedCheck_4164_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                v_a_4165_ =
                                                    leanh::lean_ctor_get(v___x_4119_, 0);
                                                v_isSharedCheck_4172_ =
                                                    (!leanh::lean_is_exclusive(v___x_4119_))
                                                        as u8;
                                                if v_isSharedCheck_4172_ == 0 {
                                                    v___x_4167_ = v___x_4119_;
                                                    v_isShared_4168_ = v_isSharedCheck_4172_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_4165_);
                                                    leanh::lean_dec(v___x_4119_);
                                                    v___x_4167_ = leanh::lean_box(0);
                                                    v_isShared_4168_ = v_isSharedCheck_4172_;
                                                    state = 9;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v_a_4173_ = leanh::lean_ctor_get(v___x_4116_, 0);
                                            v_isSharedCheck_4180_ =
                                                (!leanh::lean_is_exclusive(v___x_4116_))
                                                    as u8;
                                            if v_isSharedCheck_4180_ == 0 {
                                                v___x_4175_ = v___x_4116_;
                                                v_isShared_4176_ = v_isSharedCheck_4180_;
                                                state = 11;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4173_);
                                                leanh::lean_dec(v___x_4116_);
                                                v___x_4175_ = leanh::lean_box(0);
                                                v_isShared_4176_ = v_isSharedCheck_4180_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v_a_4181_ = leanh::lean_ctor_get(v___x_4113_, 0);
                                        v_isSharedCheck_4188_ =
                                            (!leanh::lean_is_exclusive(v___x_4113_)) as u8;
                                        if v_isSharedCheck_4188_ == 0 {
                                            v___x_4183_ = v___x_4113_;
                                            v_isShared_4184_ = v_isSharedCheck_4188_;
                                            state = 13;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4181_);
                                            leanh::lean_dec(v___x_4113_);
                                            v___x_4183_ = leanh::lean_box(0);
                                            v_isShared_4184_ = v_isSharedCheck_4188_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_a_4189_ = leanh::lean_ctor_get(v___x_4111_, 0);
                                    v_isSharedCheck_4196_ =
                                        (!leanh::lean_is_exclusive(v___x_4111_)) as u8;
                                    if v_isSharedCheck_4196_ == 0 {
                                        v___x_4191_ = v___x_4111_;
                                        v_isShared_4192_ = v_isSharedCheck_4196_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4189_);
                                        leanh::lean_dec(v___x_4111_);
                                        v___x_4191_ = leanh::lean_box(0);
                                        v_isShared_4192_ = v_isSharedCheck_4196_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_4197_ = leanh::lean_ctor_get(v___x_4109_, 0);
                                v_isSharedCheck_4204_ =
                                    (!leanh::lean_is_exclusive(v___x_4109_)) as u8;
                                if v_isSharedCheck_4204_ == 0 {
                                    v___x_4199_ = v___x_4109_;
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4197_);
                                    leanh::lean_dec(v___x_4109_);
                                    v___x_4199_ = leanh::lean_box(0);
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4205_ = leanh::lean_ctor_get(v___x_4107_, 0);
                            v_isSharedCheck_4212_ =
                                (!leanh::lean_is_exclusive(v___x_4107_)) as u8;
                            if v_isSharedCheck_4212_ == 0 {
                                v___x_4207_ = v___x_4107_;
                                v_isShared_4208_ = v_isSharedCheck_4212_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4205_);
                                leanh::lean_dec(v___x_4107_);
                                v___x_4207_ = leanh::lean_box(0);
                                v_isShared_4208_ = v_isSharedCheck_4212_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        v_a_4213_ = leanh::lean_ctor_get(v___x_4105_, 0);
                        v_isSharedCheck_4220_ =
                            (!leanh::lean_is_exclusive(v___x_4105_)) as u8;
                        if v_isSharedCheck_4220_ == 0 {
                            v___x_4215_ = v___x_4105_;
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4213_);
                            leanh::lean_dec(v___x_4105_);
                            v___x_4215_ = leanh::lean_box(0);
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    v_a_4221_ = leanh::lean_ctor_get(v___x_4097_, 0);
                    v_isSharedCheck_4228_ = (!leanh::lean_is_exclusive(v___x_4097_)) as u8;
                    if v_isSharedCheck_4228_ == 0 {
                        v___x_4223_ = v___x_4097_;
                        v_isShared_4224_ = v_isSharedCheck_4228_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4221_);
                        leanh::lean_dec(v___x_4097_);
                        v___x_4223_ = leanh::lean_box(0);
                        v_isShared_4224_ = v_isSharedCheck_4228_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4134_ = leanh::lean_unsigned_to_nat(1);
                v___x_4135_ = lean_mk_empty_array_with_capacity(v___x_4134_);
                v___x_4136_ = lean_array_push(v___x_4135_, v_a_4130_);
                if v_isShared_4133_ == 0 {
                    leanh::lean_ctor_set(v___x_4132_, 0, v___x_4136_);
                    v___x_4138_ = v___x_4132_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
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
                    v_reuseFailAlloc_4147_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
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
                    v_reuseFailAlloc_4155_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
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
                    v_reuseFailAlloc_4163_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
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
                    v_reuseFailAlloc_4171_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
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
                    v_reuseFailAlloc_4179_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
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
                    v_reuseFailAlloc_4187_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
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
                    v_reuseFailAlloc_4195_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
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
                    v_reuseFailAlloc_4203_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
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
                    v_reuseFailAlloc_4211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
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
                    v_reuseFailAlloc_4219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
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
                    v_reuseFailAlloc_4227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
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
    mut v_a_4229_: *mut leanh::LeanObject,
    mut v_a_4230_: *mut leanh::LeanObject,
    mut v_a_4231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4232_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_4229_, v_a_4230_);
    leanh::lean_dec(v_a_4230_);
    leanh::lean_dec_ref(v_a_4229_);
    return v_res_4232_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs(
    mut v_a_4233_: *mut leanh::LeanObject,
    mut v_a_4234_: *mut leanh::LeanObject,
    mut v_a_4235_: *mut leanh::LeanObject,
    mut v_a_4236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4238_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_4235_, v_a_4236_);
    return v___x_4238_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs___boxed(
    mut v_a_4239_: *mut leanh::LeanObject,
    mut v_a_4240_: *mut leanh::LeanObject,
    mut v_a_4241_: *mut leanh::LeanObject,
    mut v_a_4242_: *mut leanh::LeanObject,
    mut v_a_4243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4244_ = l_Lean_Meta_Grind_getSimprocs(v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
    leanh::lean_dec(v_a_4242_);
    leanh::lean_dec_ref(v_a_4241_);
    leanh::lean_dec(v_a_4240_);
    leanh::lean_dec_ref(v_a_4239_);
    return v_res_4244_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
    mut v_s_4245_: *mut leanh::LeanObject,
    mut v_declName_4246_: *mut leanh::LeanObject,
    mut v_a_4247_: *mut leanh::LeanObject,
    mut v_a_4248_: *mut leanh::LeanObject,
    mut v_a_4249_: *mut leanh::LeanObject,
    mut v_a_4250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: u8 = 0;
    v___x_4252_ = lean_st_ref_get(v_a_4250_);
    v_env_4253_ = leanh::lean_ctor_get(v___x_4252_, 0);
    leanh::lean_inc_ref(v_env_4253_);
    leanh::lean_dec(v___x_4252_);
    v___x_4254_ = 1;
    leanh::lean_inc(v_declName_4246_);
    v___x_4255_ = l_Lean_Environment_contains(v_env_4253_, v_declName_4246_, v___x_4254_);
    if v___x_4255_ == 0 {
        let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_declName_4246_);
        v___x_4256_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4256_, 0, v_s_4245_);
        return v___x_4256_;
    } else {
        let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_s_4258_: *mut leanh::LeanObject,
    mut v_declName_4259_: *mut leanh::LeanObject,
    mut v_a_4260_: *mut leanh::LeanObject,
    mut v_a_4261_: *mut leanh::LeanObject,
    mut v_a_4262_: *mut leanh::LeanObject,
    mut v_a_4263_: *mut leanh::LeanObject,
    mut v_a_4264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4265_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
        v_s_4258_,
        v_declName_4259_,
        v_a_4260_,
        v_a_4261_,
        v_a_4262_,
        v_a_4263_,
    );
    leanh::lean_dec(v_a_4263_);
    leanh::lean_dec_ref(v_a_4262_);
    leanh::lean_dec(v_a_4261_);
    leanh::lean_dec_ref(v_a_4260_);
    return v_res_4265_;
}
pub unsafe fn l_Lean_Meta_Grind_getNormTheorems(
    mut v_a_4287_: *mut leanh::LeanObject,
    mut v_a_4288_: *mut leanh::LeanObject,
    mut v_a_4289_: *mut leanh::LeanObject,
    mut v_a_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_Lean_Meta_Grind_normExt;
    v___x_4293_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_4292_, v_a_4290_);
    if leanh::lean_obj_tag(v___x_4293_) == 0 {
        let mut v_a_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4294_ = leanh::lean_ctor_get(v___x_4293_, 0);
        leanh::lean_inc(v_a_4294_);
        leanh::lean_dec_ref_known(v___x_4293_, 1);
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
        if leanh::lean_obj_tag(v___x_4296_) == 0 {
            let mut v_a_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_4297_ = leanh::lean_ctor_get(v___x_4296_, 0);
            leanh::lean_inc(v_a_4297_);
            leanh::lean_dec_ref_known(v___x_4296_, 1);
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
            if leanh::lean_obj_tag(v___x_4299_) == 0 {
                let mut v_a_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_4300_ = leanh::lean_ctor_get(v___x_4299_, 0);
                leanh::lean_inc(v_a_4300_);
                leanh::lean_dec_ref_known(v___x_4299_, 1);
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
                if leanh::lean_obj_tag(v___x_4302_) == 0 {
                    let mut v_a_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_a_4303_ = leanh::lean_ctor_get(v___x_4302_, 0);
                    leanh::lean_inc(v_a_4303_);
                    leanh::lean_dec_ref_known(v___x_4302_, 1);
                    v___x_4304_ = l_Lean_Meta_Grind_getNormTheorems___closed__9;
                    v___x_4305_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_4303_, v___x_4304_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
                    if leanh::lean_obj_tag(v___x_4305_) == 0 {
                        let mut v_a_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_a_4306_ = leanh::lean_ctor_get(v___x_4305_, 0);
                        leanh::lean_inc(v_a_4306_);
                        leanh::lean_dec_ref_known(v___x_4305_, 1);
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
    mut v_a_4309_: *mut leanh::LeanObject,
    mut v_a_4310_: *mut leanh::LeanObject,
    mut v_a_4311_: *mut leanh::LeanObject,
    mut v_a_4312_: *mut leanh::LeanObject,
    mut v_a_4313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4314_ = l_Lean_Meta_Grind_getNormTheorems(v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
    leanh::lean_dec(v_a_4312_);
    leanh::lean_dec_ref(v_a_4311_);
    leanh::lean_dec(v_a_4310_);
    leanh::lean_dec_ref(v_a_4309_);
    return v_res_4314_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimpContext(
    mut v_config_4315_: *mut leanh::LeanObject,
    mut v_a_4316_: *mut leanh::LeanObject,
    mut v_a_4317_: *mut leanh::LeanObject,
    mut v_a_4318_: *mut leanh::LeanObject,
    mut v_a_4319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDelta_4325_: u8 = 0;
    let mut v_zeta_4326_: u8 = 0;
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: u8 = 0;
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_a_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4350_: u8 = 0;
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4321_ =
                    l_Lean_Meta_Grind_getNormTheorems(v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_);
                if leanh::lean_obj_tag(v___x_4321_) == 0 {
                    v_a_4322_ = leanh::lean_ctor_get(v___x_4321_, 0);
                    leanh::lean_inc(v_a_4322_);
                    leanh::lean_dec_ref_known(v___x_4321_, 1);
                    v___x_4323_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_4319_);
                    if leanh::lean_obj_tag(v___x_4323_) == 0 {
                        v_a_4324_ = leanh::lean_ctor_get(v___x_4323_, 0);
                        leanh::lean_inc(v_a_4324_);
                        leanh::lean_dec_ref_known(v___x_4323_, 1);
                        v_zetaDelta_4325_ = leanh::lean_ctor_get_uint8(
                            v_config_4315_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 19)
                                as u32,
                        );
                        v_zeta_4326_ = leanh::lean_ctor_get_uint8(
                            v_config_4315_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 20)
                                as u32,
                        );
                        v___x_4327_ = leanh::lean_unsigned_to_nat(100000);
                        v___x_4328_ = leanh::lean_unsigned_to_nat(2);
                        v___x_4329_ = 0;
                        v___x_4330_ = 1;
                        v___x_4331_ = 0;
                        v___x_4332_ = leanh::lean_box(0);
                        v___x_4333_ = leanh::lean_alloc_ctor(0, 3, (29) as u32);
                        leanh::lean_ctor_set(v___x_4333_, 0, v___x_4327_);
                        leanh::lean_ctor_set(v___x_4333_, 1, v___x_4328_);
                        leanh::lean_ctor_set(v___x_4333_, 2, v___x_4332_);
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3) as u32,
                            v_zeta_4326_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 5) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 6) as u32,
                            v___x_4331_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 7) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 9) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 10) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 11) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 12) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 13) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 14) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 15) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                            v_zetaDelta_4325_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 17) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 18) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 19) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 20) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 21) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 22) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 23) as u32,
                            v___x_4330_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 24) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 25) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 26) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 27) as u32,
                            v___x_4329_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 28) as u32,
                            v___x_4329_,
                        );
                        v___x_4334_ = leanh::lean_unsigned_to_nat(1);
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
                        leanh::lean_dec(v_a_4322_);
                        v_a_4339_ = leanh::lean_ctor_get(v___x_4323_, 0);
                        v_isSharedCheck_4346_ =
                            (!leanh::lean_is_exclusive(v___x_4323_)) as u8;
                        if v_isSharedCheck_4346_ == 0 {
                            v___x_4341_ = v___x_4323_;
                            v_isShared_4342_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4339_);
                            leanh::lean_dec(v___x_4323_);
                            v___x_4341_ = leanh::lean_box(0);
                            v_isShared_4342_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_4347_ = leanh::lean_ctor_get(v___x_4321_, 0);
                    v_isSharedCheck_4354_ = (!leanh::lean_is_exclusive(v___x_4321_)) as u8;
                    if v_isSharedCheck_4354_ == 0 {
                        v___x_4349_ = v___x_4321_;
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4347_);
                        leanh::lean_dec(v___x_4321_);
                        v___x_4349_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4345_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
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
                    v_reuseFailAlloc_4353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
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
    mut v_config_4355_: *mut leanh::LeanObject,
    mut v_a_4356_: *mut leanh::LeanObject,
    mut v_a_4357_: *mut leanh::LeanObject,
    mut v_a_4358_: *mut leanh::LeanObject,
    mut v_a_4359_: *mut leanh::LeanObject,
    mut v_a_4360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4361_ = l_Lean_Meta_Grind_getSimpContext(
        v_config_4355_,
        v_a_4356_,
        v_a_4357_,
        v_a_4358_,
        v_a_4359_,
    );
    leanh::lean_dec(v_a_4359_);
    leanh::lean_dec_ref(v_a_4358_);
    leanh::lean_dec(v_a_4357_);
    leanh::lean_dec_ref(v_a_4356_);
    leanh::lean_dec_ref(v_config_4355_);
    return v_res_4361_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4362_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4362_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4363_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__0_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__0,
    );
    v___x_4364_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4364_, 0, v___x_4363_);
    return v___x_4364_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4365_ = leanh::lean_unsigned_to_nat(0);
    v___x_4366_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__1,
    );
    v___x_4367_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4367_, 0, v___x_4366_);
    leanh::lean_ctor_set(v___x_4367_, 1, v___x_4365_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4368_ = leanh::lean_unsigned_to_nat(32);
    v___x_4369_ = lean_mk_empty_array_with_capacity(v___x_4368_);
    v___x_4370_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4370_, 0, v___x_4369_);
    return v___x_4370_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4371_: usize = 0;
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4371_ = 5usize;
    v___x_4372_ = leanh::lean_unsigned_to_nat(0);
    v___x_4373_ = leanh::lean_unsigned_to_nat(32);
    v___x_4374_ = lean_mk_empty_array_with_capacity(v___x_4373_);
    v___x_4375_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__3_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__3,
    );
    v___x_4376_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_4376_, 0, v___x_4375_);
    leanh::lean_ctor_set(v___x_4376_, 1, v___x_4374_);
    leanh::lean_ctor_set(v___x_4376_, 2, v___x_4372_);
    leanh::lean_ctor_set(v___x_4376_, 3, v___x_4372_);
    leanh::lean_ctor_set_usize(v___x_4376_, 4, v___x_4371_);
    return v___x_4376_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__4_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__4,
    );
    v___x_4378_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__1,
    );
    v___x_4379_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4379_, 0, v___x_4378_);
    leanh::lean_ctor_set(v___x_4379_, 1, v___x_4378_);
    leanh::lean_ctor_set(v___x_4379_, 2, v___x_4378_);
    leanh::lean_ctor_set(v___x_4379_, 3, v___x_4377_);
    return v___x_4379_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__5_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__5,
    );
    v___x_4381_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__2_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__2,
    );
    v___x_4382_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4382_, 0, v___x_4381_);
    leanh::lean_ctor_set(v___x_4382_, 1, v___x_4380_);
    return v___x_4382_;
}
pub unsafe fn lean_grind_normalize(
    mut v_e_4383_: *mut leanh::LeanObject,
    mut v_config_4384_: *mut leanh::LeanObject,
    mut v_a_4385_: *mut leanh::LeanObject,
    mut v_a_4386_: *mut leanh::LeanObject,
    mut v_a_4387_: *mut leanh::LeanObject,
    mut v_a_4388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v_fst_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v_a_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v_a_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_a_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4426_: u8 = 0;
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                leanh::lean_dec_ref(v_config_4384_);
                if leanh::lean_obj_tag(v___x_4390_) == 0 {
                    v_a_4391_ = leanh::lean_ctor_get(v___x_4390_, 0);
                    leanh::lean_inc(v_a_4391_);
                    leanh::lean_dec_ref_known(v___x_4390_, 1);
                    v___x_4392_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_4387_, v_a_4388_);
                    if leanh::lean_obj_tag(v___x_4392_) == 0 {
                        v_a_4393_ = leanh::lean_ctor_get(v___x_4392_, 0);
                        leanh::lean_inc(v_a_4393_);
                        leanh::lean_dec_ref_known(v___x_4392_, 1);
                        v___x_4394_ = leanh::lean_box(0);
                        v___x_4395_ = leanh::lean_obj_once(
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
                        leanh::lean_dec(v_a_4388_);
                        leanh::lean_dec_ref(v_a_4387_);
                        leanh::lean_dec(v_a_4386_);
                        leanh::lean_dec_ref(v_a_4385_);
                        if leanh::lean_obj_tag(v___x_4396_) == 0 {
                            v_a_4397_ = leanh::lean_ctor_get(v___x_4396_, 0);
                            v_isSharedCheck_4406_ =
                                (!leanh::lean_is_exclusive(v___x_4396_)) as u8;
                            if v_isSharedCheck_4406_ == 0 {
                                v___x_4399_ = v___x_4396_;
                                v_isShared_4400_ = v_isSharedCheck_4406_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4397_);
                                leanh::lean_dec(v___x_4396_);
                                v___x_4399_ = leanh::lean_box(0);
                                v_isShared_4400_ = v_isSharedCheck_4406_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4407_ = leanh::lean_ctor_get(v___x_4396_, 0);
                            v_isSharedCheck_4414_ =
                                (!leanh::lean_is_exclusive(v___x_4396_)) as u8;
                            if v_isSharedCheck_4414_ == 0 {
                                v___x_4409_ = v___x_4396_;
                                v_isShared_4410_ = v_isSharedCheck_4414_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4407_);
                                leanh::lean_dec(v___x_4396_);
                                v___x_4409_ = leanh::lean_box(0);
                                v_isShared_4410_ = v_isSharedCheck_4414_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4391_);
                        leanh::lean_dec(v_a_4388_);
                        leanh::lean_dec_ref(v_a_4387_);
                        leanh::lean_dec(v_a_4386_);
                        leanh::lean_dec_ref(v_a_4385_);
                        leanh::lean_dec_ref(v_e_4383_);
                        v_a_4415_ = leanh::lean_ctor_get(v___x_4392_, 0);
                        v_isSharedCheck_4422_ =
                            (!leanh::lean_is_exclusive(v___x_4392_)) as u8;
                        if v_isSharedCheck_4422_ == 0 {
                            v___x_4417_ = v___x_4392_;
                            v_isShared_4418_ = v_isSharedCheck_4422_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4415_);
                            leanh::lean_dec(v___x_4392_);
                            v___x_4417_ = leanh::lean_box(0);
                            v_isShared_4418_ = v_isSharedCheck_4422_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4388_);
                    leanh::lean_dec_ref(v_a_4387_);
                    leanh::lean_dec(v_a_4386_);
                    leanh::lean_dec_ref(v_a_4385_);
                    leanh::lean_dec_ref(v_e_4383_);
                    v_a_4423_ = leanh::lean_ctor_get(v___x_4390_, 0);
                    v_isSharedCheck_4430_ = (!leanh::lean_is_exclusive(v___x_4390_)) as u8;
                    if v_isSharedCheck_4430_ == 0 {
                        v___x_4425_ = v___x_4390_;
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4423_);
                        leanh::lean_dec(v___x_4390_);
                        v___x_4425_ = leanh::lean_box(0);
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4401_ = leanh::lean_ctor_get(v_a_4397_, 0);
                leanh::lean_inc(v_fst_4401_);
                leanh::lean_dec(v_a_4397_);
                v_expr_4402_ = leanh::lean_ctor_get(v_fst_4401_, 0);
                leanh::lean_inc_ref(v_expr_4402_);
                leanh::lean_dec(v_fst_4401_);
                if v_isShared_4400_ == 0 {
                    leanh::lean_ctor_set(v___x_4399_, 0, v_expr_4402_);
                    v___x_4404_ = v___x_4399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_expr_4402_);
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
                    v_reuseFailAlloc_4413_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
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
                    v_reuseFailAlloc_4421_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
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
                    v_reuseFailAlloc_4429_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
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
    mut v_e_4431_: *mut leanh::LeanObject,
    mut v_config_4432_: *mut leanh::LeanObject,
    mut v_a_4433_: *mut leanh::LeanObject,
    mut v_a_4434_: *mut leanh::LeanObject,
    mut v_a_4435_: *mut leanh::LeanObject,
    mut v_a_4436_: *mut leanh::LeanObject,
    mut v_a_4437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Norm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_SimpUtil(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_SimpUtil(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Norm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
}