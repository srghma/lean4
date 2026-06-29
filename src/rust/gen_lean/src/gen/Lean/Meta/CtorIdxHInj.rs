// Lean compiler output
// Module: Lean.Meta.CtorIdxHInj
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.Refl Lean.Meta.Constructions.CtorIdx Lean.Meta.Tactic.Subst
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::lean_name_append_after;
use crate::r#gen::Init::Prelude::l_Lean_Name_str___override;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::l_Lean_Environment_hasUnsafe;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasMVar, l_Lean_Expr_isForall, l_Lean_Expr_mvarId_x21,
    l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkForall,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkEq, l_Lean_Meta_mkEqHEq};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withPrimedNamesImp,
    l_Lean_FVarId_getUserName___redArg, l_Lean_Meta_mkForallFVars, l_Lean_Meta_realizeConst,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Constructions::CtorIdx::{
    initialize_Lean_Meta_Constructions_CtorIdx, l_isCtorIdxCore_x3f, l_mkCtorIdxName,
    runtime_initialize_Lean_Meta_Constructions_CtorIdx,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProof;
use crate::r#gen::Lean::Meta::Tactic::Intro::{l_Lean_Meta_intro1Core, l_Lean_Meta_introNCore};
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, l_Lean_MVarId_refl, runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Subst::{
    initialize_Lean_Meta_Tactic_Subst, l_Lean_Meta_heqToEq, l_Lean_Meta_substEq,
    runtime_initialize_Lean_Meta_Tactic_Subst,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::ReservedNameAction::l_Lean_registerReservedNameAction;
use crate::r#gen::Lean::ResolveName::l_Lean_registerReservedNamePredicate;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_lt, lean_nat_mul, lean_string_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0_value:
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
    m_data: [104, 105, 110, 106, 0],
};
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [95, 101, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [120, 39, 0]};
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,8629873184902941699 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__0_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(
    mut v_indName_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = l_mkCtorIdxName(v_indName_1018_);
    v___x_1020_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0;
    v___x_1021_ = l_Lean_Name_str___override(v___x_1019_, v___x_1020_);
    return v___x_1021_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(
    mut v_mvarId_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_a_1024_: *mut crate::leanh::LeanObject,
    mut v_a_1025_: *mut crate::leanh::LeanObject,
    mut v_a_1026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: u8 = 0;
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1050_: u8 = 0;
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1054_: u8 = 0;
    let mut v_a_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1058_: u8 = 0;
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1062_: u8 = 0;
    let mut v_a_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1070_: u8 = 0;
    let mut v_a_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_1022_);
                v___x_1028_ = l_Lean_MVarId_getType(
                    v_mvarId_1022_,
                    v_a_1023_,
                    v_a_1024_,
                    v_a_1025_,
                    v_a_1026_,
                );
                if crate::leanh::lean_obj_tag(v___x_1028_) == 0 {
                    v_a_1029_ = crate::leanh::lean_ctor_get(v___x_1028_, 0);
                    crate::leanh::lean_inc(v_a_1029_);
                    crate::leanh::lean_dec_ref_known(v___x_1028_, 1);
                    v___x_1030_ = l_Lean_Expr_isForall(v_a_1029_);
                    crate::leanh::lean_dec(v_a_1029_);
                    v___x_1031_ = 1;
                    if v___x_1030_ == 0 {
                        v___x_1032_ = l_Lean_MVarId_refl(
                            v_mvarId_1022_,
                            v___x_1031_,
                            v_a_1023_,
                            v_a_1024_,
                            v_a_1025_,
                            v_a_1026_,
                        );
                        return v___x_1032_;
                    } else {
                        v___x_1033_ = 0;
                        v___x_1034_ = l_Lean_Meta_intro1Core(
                            v_mvarId_1022_,
                            v___x_1033_,
                            v_a_1023_,
                            v_a_1024_,
                            v_a_1025_,
                            v_a_1026_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1034_) == 0 {
                            v_a_1035_ = crate::leanh::lean_ctor_get(v___x_1034_, 0);
                            crate::leanh::lean_inc(v_a_1035_);
                            crate::leanh::lean_dec_ref_known(v___x_1034_, 1);
                            v_fst_1036_ = crate::leanh::lean_ctor_get(v_a_1035_, 0);
                            crate::leanh::lean_inc(v_fst_1036_);
                            v_snd_1037_ = crate::leanh::lean_ctor_get(v_a_1035_, 1);
                            crate::leanh::lean_inc(v_snd_1037_);
                            crate::leanh::lean_dec(v_a_1035_);
                            v___x_1038_ = l_Lean_Meta_heqToEq(
                                v_snd_1037_,
                                v_fst_1036_,
                                v___x_1031_,
                                v_a_1023_,
                                v_a_1024_,
                                v_a_1025_,
                                v_a_1026_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1038_) == 0 {
                                v_a_1039_ = crate::leanh::lean_ctor_get(v___x_1038_, 0);
                                crate::leanh::lean_inc(v_a_1039_);
                                crate::leanh::lean_dec_ref_known(v___x_1038_, 1);
                                v_fst_1040_ = crate::leanh::lean_ctor_get(v_a_1039_, 0);
                                crate::leanh::lean_inc(v_fst_1040_);
                                v_snd_1041_ = crate::leanh::lean_ctor_get(v_a_1039_, 1);
                                crate::leanh::lean_inc(v_snd_1041_);
                                crate::leanh::lean_dec(v_a_1039_);
                                v___x_1042_ = crate::leanh::lean_box(0);
                                v___x_1043_ = l_Lean_Meta_substEq(
                                    v_snd_1041_,
                                    v_fst_1040_,
                                    v___x_1042_,
                                    v_a_1023_,
                                    v_a_1024_,
                                    v_a_1025_,
                                    v_a_1026_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1043_) == 0 {
                                    v_a_1044_ = crate::leanh::lean_ctor_get(v___x_1043_, 0);
                                    crate::leanh::lean_inc(v_a_1044_);
                                    crate::leanh::lean_dec_ref_known(v___x_1043_, 1);
                                    v_snd_1045_ = crate::leanh::lean_ctor_get(v_a_1044_, 1);
                                    crate::leanh::lean_inc(v_snd_1045_);
                                    crate::leanh::lean_dec(v_a_1044_);
                                    v_mvarId_1022_ = v_snd_1045_;
                                    state = 0;
                                    continue;
                                } else {
                                    v_a_1047_ = crate::leanh::lean_ctor_get(v___x_1043_, 0);
                                    v_isSharedCheck_1054_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1043_)) as u8;
                                    if v_isSharedCheck_1054_ == 0 {
                                        v___x_1049_ = v___x_1043_;
                                        v_isShared_1050_ = v_isSharedCheck_1054_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1047_);
                                        crate::leanh::lean_dec(v___x_1043_);
                                        v___x_1049_ = crate::leanh::lean_box(0);
                                        v_isShared_1050_ = v_isSharedCheck_1054_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_1055_ = crate::leanh::lean_ctor_get(v___x_1038_, 0);
                                v_isSharedCheck_1062_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1038_)) as u8;
                                if v_isSharedCheck_1062_ == 0 {
                                    v___x_1057_ = v___x_1038_;
                                    v_isShared_1058_ = v_isSharedCheck_1062_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1055_);
                                    crate::leanh::lean_dec(v___x_1038_);
                                    v___x_1057_ = crate::leanh::lean_box(0);
                                    v_isShared_1058_ = v_isSharedCheck_1062_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_1063_ = crate::leanh::lean_ctor_get(v___x_1034_, 0);
                            v_isSharedCheck_1070_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1034_)) as u8;
                            if v_isSharedCheck_1070_ == 0 {
                                v___x_1065_ = v___x_1034_;
                                v_isShared_1066_ = v_isSharedCheck_1070_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1063_);
                                crate::leanh::lean_dec(v___x_1034_);
                                v___x_1065_ = crate::leanh::lean_box(0);
                                v_isShared_1066_ = v_isSharedCheck_1070_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1022_);
                    v_a_1071_ = crate::leanh::lean_ctor_get(v___x_1028_, 0);
                    v_isSharedCheck_1078_ = (!crate::leanh::lean_is_exclusive(v___x_1028_)) as u8;
                    if v_isSharedCheck_1078_ == 0 {
                        v___x_1073_ = v___x_1028_;
                        v_isShared_1074_ = v_isSharedCheck_1078_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1071_);
                        crate::leanh::lean_dec(v___x_1028_);
                        v___x_1073_ = crate::leanh::lean_box(0);
                        v_isShared_1074_ = v_isSharedCheck_1078_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1050_ == 0 {
                    v___x_1052_ = v___x_1049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
                    v___x_1052_ = v_reuseFailAlloc_1053_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1052_;
            }
            3 => {
                if v_isShared_1058_ == 0 {
                    v___x_1060_ = v___x_1057_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1061_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
                    v___x_1060_ = v_reuseFailAlloc_1061_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1060_;
            }
            5 => {
                if v_isShared_1066_ == 0 {
                    v___x_1068_ = v___x_1065_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
                    v___x_1068_ = v_reuseFailAlloc_1069_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1068_;
            }
            7 => {
                if v_isShared_1074_ == 0 {
                    v___x_1076_ = v___x_1073_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
                    v___x_1076_ = v_reuseFailAlloc_1077_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl___boxed(
    mut v_mvarId_1079_: *mut crate::leanh::LeanObject,
    mut v_a_1080_: *mut crate::leanh::LeanObject,
    mut v_a_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_a_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1085_ =
        l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(
            v_mvarId_1079_,
            v_a_1080_,
            v_a_1081_,
            v_a_1082_,
            v_a_1083_,
        );
    crate::leanh::lean_dec(v_a_1083_);
    crate::leanh::lean_dec_ref(v_a_1082_);
    crate::leanh::lean_dec(v_a_1081_);
    crate::leanh::lean_dec_ref(v_a_1080_);
    return v_res_1085_;
}
pub unsafe fn l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(
    mut v_xs_1086_: *mut crate::leanh::LeanObject,
    mut v_k_1087_: *mut crate::leanh::LeanObject,
    mut v___y_1088_: *mut crate::leanh::LeanObject,
    mut v___y_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
    mut v___y_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1097_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut v_a_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1093_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withPrimedNamesImp(
                    crate::leanh::lean_box(0),
                    v_xs_1086_,
                    v_k_1087_,
                    v___y_1088_,
                    v___y_1089_,
                    v___y_1090_,
                    v___y_1091_,
                );
                if crate::leanh::lean_obj_tag(v___x_1093_) == 0 {
                    v_a_1094_ = crate::leanh::lean_ctor_get(v___x_1093_, 0);
                    v_isSharedCheck_1101_ = (!crate::leanh::lean_is_exclusive(v___x_1093_)) as u8;
                    if v_isSharedCheck_1101_ == 0 {
                        v___x_1096_ = v___x_1093_;
                        v_isShared_1097_ = v_isSharedCheck_1101_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1094_);
                        crate::leanh::lean_dec(v___x_1093_);
                        v___x_1096_ = crate::leanh::lean_box(0);
                        v_isShared_1097_ = v_isSharedCheck_1101_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1102_ = crate::leanh::lean_ctor_get(v___x_1093_, 0);
                    v_isSharedCheck_1109_ = (!crate::leanh::lean_is_exclusive(v___x_1093_)) as u8;
                    if v_isSharedCheck_1109_ == 0 {
                        v___x_1104_ = v___x_1093_;
                        v_isShared_1105_ = v_isSharedCheck_1109_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1102_);
                        crate::leanh::lean_dec(v___x_1093_);
                        v___x_1104_ = crate::leanh::lean_box(0);
                        v_isShared_1105_ = v_isSharedCheck_1109_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1097_ == 0 {
                    v___x_1099_ = v___x_1096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
                    v___x_1099_ = v_reuseFailAlloc_1100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1099_;
            }
            3 => {
                if v_isShared_1105_ == 0 {
                    v___x_1107_ = v___x_1104_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1108_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
                    v___x_1107_ = v_reuseFailAlloc_1108_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg___boxed(
    mut v_xs_1110_: *mut crate::leanh::LeanObject,
    mut v_k_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
    mut v___y_1114_: *mut crate::leanh::LeanObject,
    mut v___y_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(v_xs_1110_, v_k_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
    crate::leanh::lean_dec(v___y_1115_);
    crate::leanh::lean_dec_ref(v___y_1114_);
    crate::leanh::lean_dec(v___y_1113_);
    crate::leanh::lean_dec_ref(v___y_1112_);
    return v_res_1117_;
}
pub unsafe fn l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3(
    mut v_00_u03b1_1118_: *mut crate::leanh::LeanObject,
    mut v_xs_1119_: *mut crate::leanh::LeanObject,
    mut v_k_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___redArg(v_xs_1119_, v_k_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
    return v___x_1126_;
}
pub unsafe fn l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___boxed(
    mut v_00_u03b1_1127_: *mut crate::leanh::LeanObject,
    mut v_xs_1128_: *mut crate::leanh::LeanObject,
    mut v_k_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3(v_00_u03b1_1127_, v_xs_1128_, v_k_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
    crate::leanh::lean_dec(v___y_1133_);
    crate::leanh::lean_dec_ref(v___y_1132_);
    crate::leanh::lean_dec(v___y_1131_);
    crate::leanh::lean_dec_ref(v___y_1130_);
    return v_res_1135_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0(
    mut v_k_1136_: *mut crate::leanh::LeanObject,
    mut v_b_1137_: *mut crate::leanh::LeanObject,
    mut v_c_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1142_);
    crate::leanh::lean_inc_ref(v___y_1141_);
    crate::leanh::lean_inc(v___y_1140_);
    crate::leanh::lean_inc_ref(v___y_1139_);
    v___x_1144_ = crate::leanh::lean_apply_7(
        v_k_1136_,
        v_b_1137_,
        v_c_1138_,
        v___y_1139_,
        v___y_1140_,
        v___y_1141_,
        v___y_1142_,
        crate::leanh::lean_box(0),
    );
    return v___x_1144_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0___boxed(
    mut v_k_1145_: *mut crate::leanh::LeanObject,
    mut v_b_1146_: *mut crate::leanh::LeanObject,
    mut v_c_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
    mut v___y_1149_: *mut crate::leanh::LeanObject,
    mut v___y_1150_: *mut crate::leanh::LeanObject,
    mut v___y_1151_: *mut crate::leanh::LeanObject,
    mut v___y_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1153_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0(v_k_1145_, v_b_1146_, v_c_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
    crate::leanh::lean_dec(v___y_1151_);
    crate::leanh::lean_dec_ref(v___y_1150_);
    crate::leanh::lean_dec(v___y_1149_);
    crate::leanh::lean_dec_ref(v___y_1148_);
    return v_res_1153_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(
    mut v_type_1154_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1155_: *mut crate::leanh::LeanObject,
    mut v_k_1156_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1157_: u8,
    mut v_whnfType_1158_: u8,
    mut v___y_1159_: *mut crate::leanh::LeanObject,
    mut v___y_1160_: *mut crate::leanh::LeanObject,
    mut v___y_1161_: *mut crate::leanh::LeanObject,
    mut v___y_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1169_: u8 = 0;
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1173_: u8 = 0;
    let mut v_a_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1164_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1164_, 0, v_k_1156_);
                v___x_1165_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_1154_,
                    v_maxFVars_x3f_1155_,
                    v___f_1164_,
                    v_cleanupAnnotations_1157_,
                    v_whnfType_1158_,
                    v___y_1159_,
                    v___y_1160_,
                    v___y_1161_,
                    v___y_1162_,
                );
                if crate::leanh::lean_obj_tag(v___x_1165_) == 0 {
                    v_a_1166_ = crate::leanh::lean_ctor_get(v___x_1165_, 0);
                    v_isSharedCheck_1173_ = (!crate::leanh::lean_is_exclusive(v___x_1165_)) as u8;
                    if v_isSharedCheck_1173_ == 0 {
                        v___x_1168_ = v___x_1165_;
                        v_isShared_1169_ = v_isSharedCheck_1173_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1166_);
                        crate::leanh::lean_dec(v___x_1165_);
                        v___x_1168_ = crate::leanh::lean_box(0);
                        v_isShared_1169_ = v_isSharedCheck_1173_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1174_ = crate::leanh::lean_ctor_get(v___x_1165_, 0);
                    v_isSharedCheck_1181_ = (!crate::leanh::lean_is_exclusive(v___x_1165_)) as u8;
                    if v_isSharedCheck_1181_ == 0 {
                        v___x_1176_ = v___x_1165_;
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1174_);
                        crate::leanh::lean_dec(v___x_1165_);
                        v___x_1176_ = crate::leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1169_ == 0 {
                    v___x_1171_ = v___x_1168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
                    v___x_1171_ = v_reuseFailAlloc_1172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1171_;
            }
            3 => {
                if v_isShared_1177_ == 0 {
                    v___x_1179_ = v___x_1176_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
                    v___x_1179_ = v_reuseFailAlloc_1180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg___boxed(
    mut v_type_1182_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1183_: *mut crate::leanh::LeanObject,
    mut v_k_1184_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1185_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
    mut v___y_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1192_: u8 = 0;
    let mut v_whnfType_boxed_1193_: u8 = 0;
    let mut v_res_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1192_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1185_) as u8);
    v_whnfType_boxed_1193_ = (crate::leanh::lean_unbox(v_whnfType_1186_) as u8);
    v_res_1194_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_1182_, v_maxFVars_x3f_1183_, v_k_1184_, v_cleanupAnnotations_boxed_1192_, v_whnfType_boxed_1193_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
    crate::leanh::lean_dec(v___y_1190_);
    crate::leanh::lean_dec_ref(v___y_1189_);
    crate::leanh::lean_dec(v___y_1188_);
    crate::leanh::lean_dec_ref(v___y_1187_);
    return v_res_1194_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5(
    mut v_00_u03b1_1195_: *mut crate::leanh::LeanObject,
    mut v_type_1196_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1197_: *mut crate::leanh::LeanObject,
    mut v_k_1198_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1199_: u8,
    mut v_whnfType_1200_: u8,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
    mut v___y_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_1196_, v_maxFVars_x3f_1197_, v_k_1198_, v_cleanupAnnotations_1199_, v_whnfType_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
    return v___x_1206_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___boxed(
    mut v_00_u03b1_1207_: *mut crate::leanh::LeanObject,
    mut v_type_1208_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1209_: *mut crate::leanh::LeanObject,
    mut v_k_1210_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1211_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1218_: u8 = 0;
    let mut v_whnfType_boxed_1219_: u8 = 0;
    let mut v_res_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1218_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1211_) as u8);
    v_whnfType_boxed_1219_ = (crate::leanh::lean_unbox(v_whnfType_1212_) as u8);
    v_res_1220_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5(v_00_u03b1_1207_, v_type_1208_, v_maxFVars_x3f_1209_, v_k_1210_, v_cleanupAnnotations_boxed_1218_, v_whnfType_boxed_1219_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
    crate::leanh::lean_dec(v___y_1216_);
    crate::leanh::lean_dec_ref(v___y_1215_);
    crate::leanh::lean_dec(v___y_1214_);
    crate::leanh::lean_dec_ref(v___y_1213_);
    return v_res_1220_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(
    mut v_e_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1224_: u8 = 0;
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1238_: u8 = 0;
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v_unused_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1224_ = l_Lean_Expr_hasMVar(v_e_1221_);
                if v___x_1224_ == 0 {
                    v___x_1225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1225_, 0, v_e_1221_);
                    return v___x_1225_;
                } else {
                    v___x_1226_ = lean_st_ref_get(v___y_1222_);
                    v_mctx_1227_ = crate::leanh::lean_ctor_get(v___x_1226_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1227_);
                    crate::leanh::lean_dec(v___x_1226_);
                    v___x_1228_ = l_Lean_instantiateMVarsCore(v_mctx_1227_, v_e_1221_);
                    v_fst_1229_ = crate::leanh::lean_ctor_get(v___x_1228_, 0);
                    crate::leanh::lean_inc(v_fst_1229_);
                    v_snd_1230_ = crate::leanh::lean_ctor_get(v___x_1228_, 1);
                    crate::leanh::lean_inc(v_snd_1230_);
                    crate::leanh::lean_dec_ref(v___x_1228_);
                    v___x_1231_ = lean_st_ref_take(v___y_1222_);
                    v_cache_1232_ = crate::leanh::lean_ctor_get(v___x_1231_, 1);
                    v_zetaDeltaFVarIds_1233_ = crate::leanh::lean_ctor_get(v___x_1231_, 2);
                    v_postponed_1234_ = crate::leanh::lean_ctor_get(v___x_1231_, 3);
                    v_diag_1235_ = crate::leanh::lean_ctor_get(v___x_1231_, 4);
                    v_isSharedCheck_1244_ = (!crate::leanh::lean_is_exclusive(v___x_1231_)) as u8;
                    if v_isSharedCheck_1244_ == 0 {
                        v_unused_1245_ = crate::leanh::lean_ctor_get(v___x_1231_, 0);
                        crate::leanh::lean_dec(v_unused_1245_);
                        v___x_1237_ = v___x_1231_;
                        v_isShared_1238_ = v_isSharedCheck_1244_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1235_);
                        crate::leanh::lean_inc(v_postponed_1234_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1233_);
                        crate::leanh::lean_inc(v_cache_1232_);
                        crate::leanh::lean_dec(v___x_1231_);
                        v___x_1237_ = crate::leanh::lean_box(0);
                        v_isShared_1238_ = v_isSharedCheck_1244_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1237_, 0, v_snd_1230_);
                    v___x_1240_ = v___x_1237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_snd_1230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_cache_1232_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1243_,
                        2,
                        v_zetaDeltaFVarIds_1233_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_postponed_1234_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_diag_1235_);
                    v___x_1240_ = v_reuseFailAlloc_1243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1241_ = lean_st_ref_set(v___y_1222_, v___x_1240_);
                v___x_1242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1242_, 0, v_fst_1229_);
                return v___x_1242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg___boxed(
    mut v_e_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_e_1246_, v___y_1247_);
    crate::leanh::lean_dec(v___y_1247_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6(
    mut v_e_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1256_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_e_1250_, v___y_1252_);
    return v___x_1256_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___boxed(
    mut v_e_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
    mut v___y_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1263_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6(v_e_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
    crate::leanh::lean_dec(v___y_1261_);
    crate::leanh::lean_dec_ref(v___y_1260_);
    crate::leanh::lean_dec(v___y_1259_);
    crate::leanh::lean_dec_ref(v___y_1258_);
    return v_res_1263_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(
    mut v_as_1265_: *mut crate::leanh::LeanObject,
    mut v_sz_1266_: usize,
    mut v_i_1267_: usize,
    mut v_b_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: usize = 0;
    let mut v___x_1277_: usize = 0;
    let mut v___x_1279_: u8 = 0;
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v_array_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: u8 = 0;
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v_a_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: u8 = 0;
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: u8 = 0;
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1325_: u8 = 0;
    let mut v_a_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1329_: u8 = 0;
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1341_: u8 = 0;
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut v_isSharedCheck_1346_: u8 = 0;
    let mut v_unused_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1279_ = lean_usize_dec_lt(v_i_1267_, v_sz_1266_);
                if v___x_1279_ == 0 {
                    v___x_1280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1280_, 0, v_b_1268_);
                    return v___x_1280_;
                } else {
                    v_snd_1281_ = crate::leanh::lean_ctor_get(v_b_1268_, 1);
                    v_fst_1282_ = crate::leanh::lean_ctor_get(v_b_1268_, 0);
                    v_isSharedCheck_1350_ = (!crate::leanh::lean_is_exclusive(v_b_1268_)) as u8;
                    if v_isSharedCheck_1350_ == 0 {
                        v___x_1284_ = v_b_1268_;
                        v_isShared_1285_ = v_isSharedCheck_1350_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1281_);
                        crate::leanh::lean_inc(v_fst_1282_);
                        crate::leanh::lean_dec(v_b_1268_);
                        v___x_1284_ = crate::leanh::lean_box(0);
                        v_isShared_1285_ = v_isSharedCheck_1350_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1276_ = 1usize;
                v___x_1277_ = lean_usize_add(v_i_1267_, v___x_1276_);
                v_i_1267_ = v___x_1277_;
                v_b_1268_ = v_a_1275_;
                state = 0;
                continue;
            }
            2 => {
                v_array_1286_ = crate::leanh::lean_ctor_get(v_snd_1281_, 0);
                v_start_1287_ = crate::leanh::lean_ctor_get(v_snd_1281_, 1);
                v_stop_1288_ = crate::leanh::lean_ctor_get(v_snd_1281_, 2);
                v___x_1289_ = lean_nat_dec_lt(v_start_1287_, v_stop_1288_);
                if v___x_1289_ == 0 {
                    if v_isShared_1285_ == 0 {
                        v___x_1291_ = v___x_1284_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1293_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_fst_1282_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_snd_1281_);
                        v___x_1291_ = v_reuseFailAlloc_1293_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_1288_);
                    crate::leanh::lean_inc(v_start_1287_);
                    crate::leanh::lean_inc_ref(v_array_1286_);
                    v_isSharedCheck_1346_ = (!crate::leanh::lean_is_exclusive(v_snd_1281_)) as u8;
                    if v_isSharedCheck_1346_ == 0 {
                        v_unused_1347_ = crate::leanh::lean_ctor_get(v_snd_1281_, 2);
                        crate::leanh::lean_dec(v_unused_1347_);
                        v_unused_1348_ = crate::leanh::lean_ctor_get(v_snd_1281_, 1);
                        crate::leanh::lean_dec(v_unused_1348_);
                        v_unused_1349_ = crate::leanh::lean_ctor_get(v_snd_1281_, 0);
                        crate::leanh::lean_dec(v_unused_1349_);
                        v___x_1295_ = v_snd_1281_;
                        v_isShared_1296_ = v_isSharedCheck_1346_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_1281_);
                        v___x_1295_ = crate::leanh::lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1346_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1292_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1292_, 0, v___x_1291_);
                return v___x_1292_;
            }
            4 => {
                v_a_1297_ = lean_array_uget_borrowed(v_as_1265_, v_i_1267_);
                crate::leanh::lean_inc(v_a_1297_);
                v___x_1298_ = l_Lean_Meta_isProof(
                    v_a_1297_,
                    v___y_1269_,
                    v___y_1270_,
                    v___y_1271_,
                    v___y_1272_,
                );
                if crate::leanh::lean_obj_tag(v___x_1298_) == 0 {
                    v_a_1299_ = crate::leanh::lean_ctor_get(v___x_1298_, 0);
                    crate::leanh::lean_inc(v_a_1299_);
                    crate::leanh::lean_dec_ref_known(v___x_1298_, 1);
                    v___x_1300_ = lean_array_fget(v_array_1286_, v_start_1287_);
                    v___x_1301_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1302_ = lean_nat_add(v_start_1287_, v___x_1301_);
                    crate::leanh::lean_dec(v_start_1287_);
                    if v_isShared_1296_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1295_, 1, v___x_1302_);
                        v___x_1304_ = v___x_1295_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1337_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_array_1286_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1337_, 1, v___x_1302_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_stop_1288_);
                        v___x_1304_ = v_reuseFailAlloc_1337_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1295_);
                    crate::leanh::lean_dec(v_stop_1288_);
                    crate::leanh::lean_dec(v_start_1287_);
                    crate::leanh::lean_dec_ref(v_array_1286_);
                    crate::leanh::lean_del_object(v___x_1284_);
                    crate::leanh::lean_dec(v_fst_1282_);
                    v_a_1338_ = crate::leanh::lean_ctor_get(v___x_1298_, 0);
                    v_isSharedCheck_1345_ = (!crate::leanh::lean_is_exclusive(v___x_1298_)) as u8;
                    if v_isSharedCheck_1345_ == 0 {
                        v___x_1340_ = v___x_1298_;
                        v_isShared_1341_ = v_isSharedCheck_1345_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1338_);
                        crate::leanh::lean_dec(v___x_1298_);
                        v___x_1340_ = crate::leanh::lean_box(0);
                        v_isShared_1341_ = v_isSharedCheck_1345_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1305_ = (crate::leanh::lean_unbox(v_a_1299_) as u8);
                crate::leanh::lean_dec(v_a_1299_);
                if v___x_1305_ == 0 {
                    v___x_1306_ = l_Lean_Expr_fvarId_x21(v_a_1297_);
                    v___x_1307_ = l_Lean_FVarId_getUserName___redArg(
                        v___x_1306_,
                        v___y_1269_,
                        v___y_1271_,
                        v___y_1272_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1307_) == 0 {
                        v_a_1308_ = crate::leanh::lean_ctor_get(v___x_1307_, 0);
                        crate::leanh::lean_inc(v_a_1308_);
                        crate::leanh::lean_dec_ref_known(v___x_1307_, 1);
                        crate::leanh::lean_inc(v_a_1297_);
                        v___x_1309_ = l_Lean_Meta_mkEqHEq(
                            v_a_1297_,
                            v___x_1300_,
                            v___y_1269_,
                            v___y_1270_,
                            v___y_1271_,
                            v___y_1272_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1309_) == 0 {
                            v_a_1310_ = crate::leanh::lean_ctor_get(v___x_1309_, 0);
                            crate::leanh::lean_inc(v_a_1310_);
                            crate::leanh::lean_dec_ref_known(v___x_1309_, 1);
                            v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___closed__0;
                            v___x_1312_ = lean_name_append_after(v_a_1308_, v___x_1311_);
                            v___x_1313_ = 0;
                            v___x_1314_ =
                                l_Lean_mkForall(v___x_1312_, v___x_1313_, v_a_1310_, v_fst_1282_);
                            if v_isShared_1285_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1284_, 1, v___x_1304_);
                                crate::leanh::lean_ctor_set(v___x_1284_, 0, v___x_1314_);
                                v___x_1316_ = v___x_1284_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_1317_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1304_);
                                v___x_1316_ = v_reuseFailAlloc_1317_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1308_);
                            crate::leanh::lean_dec_ref(v___x_1304_);
                            crate::leanh::lean_del_object(v___x_1284_);
                            crate::leanh::lean_dec(v_fst_1282_);
                            v_a_1318_ = crate::leanh::lean_ctor_get(v___x_1309_, 0);
                            v_isSharedCheck_1325_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1309_)) as u8;
                            if v_isSharedCheck_1325_ == 0 {
                                v___x_1320_ = v___x_1309_;
                                v_isShared_1321_ = v_isSharedCheck_1325_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1318_);
                                crate::leanh::lean_dec(v___x_1309_);
                                v___x_1320_ = crate::leanh::lean_box(0);
                                v_isShared_1321_ = v_isSharedCheck_1325_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1304_);
                        crate::leanh::lean_dec(v___x_1300_);
                        crate::leanh::lean_del_object(v___x_1284_);
                        crate::leanh::lean_dec(v_fst_1282_);
                        v_a_1326_ = crate::leanh::lean_ctor_get(v___x_1307_, 0);
                        v_isSharedCheck_1333_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1307_)) as u8;
                        if v_isSharedCheck_1333_ == 0 {
                            v___x_1328_ = v___x_1307_;
                            v_isShared_1329_ = v_isSharedCheck_1333_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1326_);
                            crate::leanh::lean_dec(v___x_1307_);
                            v___x_1328_ = crate::leanh::lean_box(0);
                            v_isShared_1329_ = v_isSharedCheck_1333_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1300_);
                    if v_isShared_1285_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1284_, 1, v___x_1304_);
                        v___x_1335_ = v___x_1284_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1336_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_fst_1282_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1304_);
                        v___x_1335_ = v_reuseFailAlloc_1336_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                v_a_1275_ = v___x_1316_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_1321_ == 0 {
                    v___x_1323_ = v___x_1320_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
                    v___x_1323_ = v_reuseFailAlloc_1324_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1323_;
            }
            9 => {
                if v_isShared_1329_ == 0 {
                    v___x_1331_ = v___x_1328_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
                    v___x_1331_ = v_reuseFailAlloc_1332_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1331_;
            }
            11 => {
                v_a_1275_ = v___x_1335_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_1341_ == 0 {
                    v___x_1343_ = v___x_1340_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
                    v___x_1343_ = v_reuseFailAlloc_1344_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1___boxed(
    mut v_as_1351_: *mut crate::leanh::LeanObject,
    mut v_sz_1352_: *mut crate::leanh::LeanObject,
    mut v_i_1353_: *mut crate::leanh::LeanObject,
    mut v_b_1354_: *mut crate::leanh::LeanObject,
    mut v___y_1355_: *mut crate::leanh::LeanObject,
    mut v___y_1356_: *mut crate::leanh::LeanObject,
    mut v___y_1357_: *mut crate::leanh::LeanObject,
    mut v___y_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1360_: usize = 0;
    let mut v_i_boxed_1361_: usize = 0;
    let mut v_res_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1360_ = crate::leanh::lean_unbox_usize(v_sz_1352_);
    crate::leanh::lean_dec(v_sz_1352_);
    v_i_boxed_1361_ = crate::leanh::lean_unbox_usize(v_i_1353_);
    crate::leanh::lean_dec(v_i_1353_);
    v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(v_as_1351_, v_sz_boxed_1360_, v_i_boxed_1361_, v_b_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
    crate::leanh::lean_dec(v___y_1358_);
    crate::leanh::lean_dec_ref(v___y_1357_);
    crate::leanh::lean_dec(v___y_1356_);
    crate::leanh::lean_dec_ref(v___y_1355_);
    crate::leanh::lean_dec_ref(v_as_1351_);
    return v_res_1362_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0(
    mut v_name_1363_: *mut crate::leanh::LeanObject,
    mut v_us_1364_: *mut crate::leanh::LeanObject,
    mut v_xs1_1365_: *mut crate::leanh::LeanObject,
    mut v_x1_1366_: *mut crate::leanh::LeanObject,
    mut v_xs2_1367_: *mut crate::leanh::LeanObject,
    mut v_x2_1368_: *mut crate::leanh::LeanObject,
    mut v___y_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorIdxApp1_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorIdxApp2_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1388_: usize = 0;
    let mut v___x_1389_: usize = 0;
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: u8 = 0;
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1374_ = l_mkCtorIdxName(v_name_1363_);
                v___x_1375_ = l_Lean_mkConst(v___x_1374_, v_us_1364_);
                v___x_1376_ = lean_array_push(v_xs1_1365_, v_x1_1366_);
                crate::leanh::lean_inc_ref(v___x_1375_);
                v_ctorIdxApp1_1377_ = l_Lean_mkAppN(v___x_1375_, v___x_1376_);
                v___x_1378_ = lean_array_push(v_xs2_1367_, v_x2_1368_);
                v_ctorIdxApp2_1379_ = l_Lean_mkAppN(v___x_1375_, v___x_1378_);
                v___x_1380_ = l_Lean_Meta_mkEq(
                    v_ctorIdxApp1_1377_,
                    v_ctorIdxApp2_1379_,
                    v___y_1369_,
                    v___y_1370_,
                    v___y_1371_,
                    v___y_1372_,
                );
                if crate::leanh::lean_obj_tag(v___x_1380_) == 0 {
                    v_a_1381_ = crate::leanh::lean_ctor_get(v___x_1380_, 0);
                    crate::leanh::lean_inc(v_a_1381_);
                    crate::leanh::lean_dec_ref_known(v___x_1380_, 1);
                    crate::leanh::lean_inc_ref(v___x_1378_);
                    v___x_1382_ = l_Array_reverse___redArg(v___x_1378_);
                    v___x_1383_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1384_ = lean_array_get_size(v___x_1382_);
                    v___x_1385_ =
                        l_Array_toSubarray___redArg(v___x_1382_, v___x_1383_, v___x_1384_);
                    crate::leanh::lean_inc_ref(v___x_1376_);
                    v___x_1386_ = l_Array_reverse___redArg(v___x_1376_);
                    v___x_1387_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1387_, 0, v_a_1381_);
                    crate::leanh::lean_ctor_set(v___x_1387_, 1, v___x_1385_);
                    v_sz_1388_ = lean_array_size(v___x_1386_);
                    v___x_1389_ = 0usize;
                    v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__1(v___x_1386_, v_sz_1388_, v___x_1389_, v___x_1387_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
                    crate::leanh::lean_dec_ref(v___x_1386_);
                    if crate::leanh::lean_obj_tag(v___x_1390_) == 0 {
                        v_a_1391_ = crate::leanh::lean_ctor_get(v___x_1390_, 0);
                        crate::leanh::lean_inc(v_a_1391_);
                        crate::leanh::lean_dec_ref_known(v___x_1390_, 1);
                        v_fst_1392_ = crate::leanh::lean_ctor_get(v_a_1391_, 0);
                        crate::leanh::lean_inc(v_fst_1392_);
                        crate::leanh::lean_dec(v_a_1391_);
                        v___x_1393_ = l_Array_append___redArg(v___x_1376_, v___x_1378_);
                        crate::leanh::lean_dec_ref(v___x_1378_);
                        v___x_1394_ = 0;
                        v___x_1395_ = 1;
                        v___x_1396_ = 1;
                        v___x_1397_ = l_Lean_Meta_mkForallFVars(
                            v___x_1393_,
                            v_fst_1392_,
                            v___x_1394_,
                            v___x_1395_,
                            v___x_1395_,
                            v___x_1396_,
                            v___y_1369_,
                            v___y_1370_,
                            v___y_1371_,
                            v___y_1372_,
                        );
                        crate::leanh::lean_dec_ref(v___x_1393_);
                        return v___x_1397_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1378_);
                        crate::leanh::lean_dec_ref(v___x_1376_);
                        v_a_1398_ = crate::leanh::lean_ctor_get(v___x_1390_, 0);
                        v_isSharedCheck_1405_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1390_)) as u8;
                        if v_isSharedCheck_1405_ == 0 {
                            v___x_1400_ = v___x_1390_;
                            v_isShared_1401_ = v_isSharedCheck_1405_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1398_);
                            crate::leanh::lean_dec(v___x_1390_);
                            v___x_1400_ = crate::leanh::lean_box(0);
                            v_isShared_1401_ = v_isSharedCheck_1405_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1378_);
                    crate::leanh::lean_dec_ref(v___x_1376_);
                    return v___x_1380_;
                }
            }
            1 => {
                if v_isShared_1401_ == 0 {
                    v___x_1403_ = v___x_1400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
                    v___x_1403_ = v_reuseFailAlloc_1404_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0___boxed(
    mut v_name_1406_: *mut crate::leanh::LeanObject,
    mut v_us_1407_: *mut crate::leanh::LeanObject,
    mut v_xs1_1408_: *mut crate::leanh::LeanObject,
    mut v_x1_1409_: *mut crate::leanh::LeanObject,
    mut v_xs2_1410_: *mut crate::leanh::LeanObject,
    mut v_x2_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
    mut v___y_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1417_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0(
        v_name_1406_,
        v_us_1407_,
        v_xs1_1408_,
        v_x1_1409_,
        v_xs2_1410_,
        v_x2_1411_,
        v___y_1412_,
        v___y_1413_,
        v___y_1414_,
        v___y_1415_,
    );
    crate::leanh::lean_dec(v___y_1415_);
    crate::leanh::lean_dec_ref(v___y_1414_);
    crate::leanh::lean_dec(v___y_1413_);
    crate::leanh::lean_dec_ref(v___y_1412_);
    return v_res_1417_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0(
    mut v_k_1418_: *mut crate::leanh::LeanObject,
    mut v_b_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1423_);
    crate::leanh::lean_inc_ref(v___y_1422_);
    crate::leanh::lean_inc(v___y_1421_);
    crate::leanh::lean_inc_ref(v___y_1420_);
    v___x_1425_ = crate::leanh::lean_apply_6(
        v_k_1418_,
        v_b_1419_,
        v___y_1420_,
        v___y_1421_,
        v___y_1422_,
        v___y_1423_,
        crate::leanh::lean_box(0),
    );
    return v___x_1425_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0___boxed(
    mut v_k_1426_: *mut crate::leanh::LeanObject,
    mut v_b_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1433_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0(v_k_1426_, v_b_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
    crate::leanh::lean_dec(v___y_1431_);
    crate::leanh::lean_dec_ref(v___y_1430_);
    crate::leanh::lean_dec(v___y_1429_);
    crate::leanh::lean_dec_ref(v___y_1428_);
    return v_res_1433_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(
    mut v_name_1434_: *mut crate::leanh::LeanObject,
    mut v_bi_1435_: u8,
    mut v_type_1436_: *mut crate::leanh::LeanObject,
    mut v_k_1437_: *mut crate::leanh::LeanObject,
    mut v_kind_1438_: u8,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
    mut v___y_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_a_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1457_: u8 = 0;
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1444_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_1444_, 0, v_k_1437_);
                v___x_1445_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_1434_,
                    v_bi_1435_,
                    v_type_1436_,
                    v___f_1444_,
                    v_kind_1438_,
                    v___y_1439_,
                    v___y_1440_,
                    v___y_1441_,
                    v___y_1442_,
                );
                if crate::leanh::lean_obj_tag(v___x_1445_) == 0 {
                    v_a_1446_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                    v_isSharedCheck_1453_ = (!crate::leanh::lean_is_exclusive(v___x_1445_)) as u8;
                    if v_isSharedCheck_1453_ == 0 {
                        v___x_1448_ = v___x_1445_;
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1446_);
                        crate::leanh::lean_dec(v___x_1445_);
                        v___x_1448_ = crate::leanh::lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1454_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                    v_isSharedCheck_1461_ = (!crate::leanh::lean_is_exclusive(v___x_1445_)) as u8;
                    if v_isSharedCheck_1461_ == 0 {
                        v___x_1456_ = v___x_1445_;
                        v_isShared_1457_ = v_isSharedCheck_1461_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1454_);
                        crate::leanh::lean_dec(v___x_1445_);
                        v___x_1456_ = crate::leanh::lean_box(0);
                        v_isShared_1457_ = v_isSharedCheck_1461_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1449_ == 0 {
                    v___x_1451_ = v___x_1448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
                    v___x_1451_ = v_reuseFailAlloc_1452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1451_;
            }
            3 => {
                if v_isShared_1457_ == 0 {
                    v___x_1459_ = v___x_1456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
                    v___x_1459_ = v_reuseFailAlloc_1460_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1459_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg___boxed(
    mut v_name_1462_: *mut crate::leanh::LeanObject,
    mut v_bi_1463_: *mut crate::leanh::LeanObject,
    mut v_type_1464_: *mut crate::leanh::LeanObject,
    mut v_k_1465_: *mut crate::leanh::LeanObject,
    mut v_kind_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_1472_: u8 = 0;
    let mut v_kind_boxed_1473_: u8 = 0;
    let mut v_res_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1472_ = (crate::leanh::lean_unbox(v_bi_1463_) as u8);
    v_kind_boxed_1473_ = (crate::leanh::lean_unbox(v_kind_1466_) as u8);
    v_res_1474_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_1462_, v_bi_boxed_1472_, v_type_1464_, v_k_1465_, v_kind_boxed_1473_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
    crate::leanh::lean_dec(v___y_1470_);
    crate::leanh::lean_dec_ref(v___y_1469_);
    crate::leanh::lean_dec(v___y_1468_);
    crate::leanh::lean_dec_ref(v___y_1467_);
    return v_res_1474_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(
    mut v_name_1475_: *mut crate::leanh::LeanObject,
    mut v_type_1476_: *mut crate::leanh::LeanObject,
    mut v_k_1477_: *mut crate::leanh::LeanObject,
    mut v___y_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: u8 = 0;
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = 0;
    v___x_1484_ = 0;
    v___x_1485_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_1475_, v___x_1483_, v_type_1476_, v_k_1477_, v___x_1484_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
    return v___x_1485_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg___boxed(
    mut v_name_1486_: *mut crate::leanh::LeanObject,
    mut v_type_1487_: *mut crate::leanh::LeanObject,
    mut v_k_1488_: *mut crate::leanh::LeanObject,
    mut v___y_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
    mut v___y_1491_: *mut crate::leanh::LeanObject,
    mut v___y_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1494_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v_name_1486_, v_type_1487_, v_k_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
    crate::leanh::lean_dec(v___y_1492_);
    crate::leanh::lean_dec_ref(v___y_1491_);
    crate::leanh::lean_dec(v___y_1490_);
    crate::leanh::lean_dec_ref(v___y_1489_);
    return v_res_1494_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1(
    mut v_name_1498_: *mut crate::leanh::LeanObject,
    mut v_us_1499_: *mut crate::leanh::LeanObject,
    mut v_xs1_1500_: *mut crate::leanh::LeanObject,
    mut v_xs2_1501_: *mut crate::leanh::LeanObject,
    mut v___x_1502_: *mut crate::leanh::LeanObject,
    mut v_x1_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
    mut v___y_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_xs2_1501_);
    v___f_1509_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__0___boxed
            as *mut core::ffi::c_void,
        11,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1509_, 0, v_name_1498_);
    crate::leanh::lean_closure_set(v___f_1509_, 1, v_us_1499_);
    crate::leanh::lean_closure_set(v___f_1509_, 2, v_xs1_1500_);
    crate::leanh::lean_closure_set(v___f_1509_, 3, v_x1_1503_);
    crate::leanh::lean_closure_set(v___f_1509_, 4, v_xs2_1501_);
    v___x_1510_ =
        l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___closed__1;
    v___x_1511_ = l_Lean_mkAppN(v___x_1502_, v_xs2_1501_);
    crate::leanh::lean_dec_ref(v_xs2_1501_);
    v___x_1512_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v___x_1510_, v___x_1511_, v___f_1509_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
    return v___x_1512_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___boxed(
    mut v_name_1513_: *mut crate::leanh::LeanObject,
    mut v_us_1514_: *mut crate::leanh::LeanObject,
    mut v_xs1_1515_: *mut crate::leanh::LeanObject,
    mut v_xs2_1516_: *mut crate::leanh::LeanObject,
    mut v___x_1517_: *mut crate::leanh::LeanObject,
    mut v_x1_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1(
        v_name_1513_,
        v_us_1514_,
        v_xs1_1515_,
        v_xs2_1516_,
        v___x_1517_,
        v_x1_1518_,
        v___y_1519_,
        v___y_1520_,
        v___y_1521_,
        v___y_1522_,
    );
    crate::leanh::lean_dec(v___y_1522_);
    crate::leanh::lean_dec_ref(v___y_1521_);
    crate::leanh::lean_dec(v___y_1520_);
    crate::leanh::lean_dec_ref(v___y_1519_);
    return v_res_1524_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2(
    mut v_00_u03b1_1525_: *mut crate::leanh::LeanObject,
    mut v_name_1526_: *mut crate::leanh::LeanObject,
    mut v_type_1527_: *mut crate::leanh::LeanObject,
    mut v_k_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
    mut v___y_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___redArg(v_name_1526_, v_type_1527_, v_k_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
    return v___x_1534_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___boxed(
    mut v_00_u03b1_1535_: *mut crate::leanh::LeanObject,
    mut v_name_1536_: *mut crate::leanh::LeanObject,
    mut v_type_1537_: *mut crate::leanh::LeanObject,
    mut v_k_1538_: *mut crate::leanh::LeanObject,
    mut v___y_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
    mut v___y_1541_: *mut crate::leanh::LeanObject,
    mut v___y_1542_: *mut crate::leanh::LeanObject,
    mut v___y_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1544_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2(v_00_u03b1_1535_, v_name_1536_, v_type_1537_, v_k_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
    crate::leanh::lean_dec(v___y_1542_);
    crate::leanh::lean_dec_ref(v___y_1541_);
    crate::leanh::lean_dec(v___y_1540_);
    crate::leanh::lean_dec_ref(v___y_1539_);
    return v_res_1544_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(
    mut v_bs_1545_: *mut crate::leanh::LeanObject,
    mut v_k_1546_: *mut crate::leanh::LeanObject,
    mut v___y_1547_: *mut crate::leanh::LeanObject,
    mut v___y_1548_: *mut crate::leanh::LeanObject,
    mut v___y_1549_: *mut crate::leanh::LeanObject,
    mut v___y_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_a_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1552_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(
                    crate::leanh::lean_box(0),
                    v_bs_1545_,
                    v_k_1546_,
                    v___y_1547_,
                    v___y_1548_,
                    v___y_1549_,
                    v___y_1550_,
                );
                if crate::leanh::lean_obj_tag(v___x_1552_) == 0 {
                    v_a_1553_ = crate::leanh::lean_ctor_get(v___x_1552_, 0);
                    v_isSharedCheck_1560_ = (!crate::leanh::lean_is_exclusive(v___x_1552_)) as u8;
                    if v_isSharedCheck_1560_ == 0 {
                        v___x_1555_ = v___x_1552_;
                        v_isShared_1556_ = v_isSharedCheck_1560_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1553_);
                        crate::leanh::lean_dec(v___x_1552_);
                        v___x_1555_ = crate::leanh::lean_box(0);
                        v_isShared_1556_ = v_isSharedCheck_1560_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1561_ = crate::leanh::lean_ctor_get(v___x_1552_, 0);
                    v_isSharedCheck_1568_ = (!crate::leanh::lean_is_exclusive(v___x_1552_)) as u8;
                    if v_isSharedCheck_1568_ == 0 {
                        v___x_1563_ = v___x_1552_;
                        v_isShared_1564_ = v_isSharedCheck_1568_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1561_);
                        crate::leanh::lean_dec(v___x_1552_);
                        v___x_1563_ = crate::leanh::lean_box(0);
                        v_isShared_1564_ = v_isSharedCheck_1568_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1556_ == 0 {
                    v___x_1558_ = v___x_1555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
                    v___x_1558_ = v_reuseFailAlloc_1559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1558_;
            }
            3 => {
                if v_isShared_1564_ == 0 {
                    v___x_1566_ = v___x_1563_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
                    v___x_1566_ = v_reuseFailAlloc_1567_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg___boxed(
    mut v_bs_1569_: *mut crate::leanh::LeanObject,
    mut v_k_1570_: *mut crate::leanh::LeanObject,
    mut v___y_1571_: *mut crate::leanh::LeanObject,
    mut v___y_1572_: *mut crate::leanh::LeanObject,
    mut v___y_1573_: *mut crate::leanh::LeanObject,
    mut v___y_1574_: *mut crate::leanh::LeanObject,
    mut v___y_1575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1576_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v_bs_1569_, v_k_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
    crate::leanh::lean_dec(v___y_1574_);
    crate::leanh::lean_dec_ref(v___y_1573_);
    crate::leanh::lean_dec(v___y_1572_);
    crate::leanh::lean_dec_ref(v___y_1571_);
    crate::leanh::lean_dec_ref(v_bs_1569_);
    return v_res_1576_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(
    mut v_sz_1577_: usize,
    mut v_i_1578_: usize,
    mut v_bs_1579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1580_: u8 = 0;
    let mut v_v_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: usize = 0;
    let mut v___x_1589_: usize = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1580_ = lean_usize_dec_lt(v_i_1578_, v_sz_1577_);
                if v___x_1580_ == 0 {
                    return v_bs_1579_;
                } else {
                    v_v_1581_ = lean_array_uget(v_bs_1579_, v_i_1578_);
                    v___x_1582_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1583_ = lean_array_uset(v_bs_1579_, v_i_1578_, v___x_1582_);
                    v___x_1584_ = l_Lean_Expr_fvarId_x21(v_v_1581_);
                    crate::leanh::lean_dec(v_v_1581_);
                    v___x_1585_ = 1;
                    v___x_1586_ = crate::leanh::lean_box((v___x_1585_) as usize);
                    v___x_1587_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1587_, 0, v___x_1584_);
                    crate::leanh::lean_ctor_set(v___x_1587_, 1, v___x_1586_);
                    v___x_1588_ = 1usize;
                    v___x_1589_ = lean_usize_add(v_i_1578_, v___x_1588_);
                    v___x_1590_ = lean_array_uset(v_bs_x27_1583_, v_i_1578_, v___x_1587_);
                    v_i_1578_ = v___x_1589_;
                    v_bs_1579_ = v___x_1590_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5___boxed(
    mut v_sz_1592_: *mut crate::leanh::LeanObject,
    mut v_i_1593_: *mut crate::leanh::LeanObject,
    mut v_bs_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1595_: usize = 0;
    let mut v_i_boxed_1596_: usize = 0;
    let mut v_res_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1595_ = crate::leanh::lean_unbox_usize(v_sz_1592_);
    crate::leanh::lean_dec(v_sz_1592_);
    v_i_boxed_1596_ = crate::leanh::lean_unbox_usize(v_i_1593_);
    crate::leanh::lean_dec(v_i_1593_);
    v_res_1597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(v_sz_boxed_1595_, v_i_boxed_1596_, v_bs_1594_);
    return v_res_1597_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(
    mut v_bs_1598_: *mut crate::leanh::LeanObject,
    mut v_k_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
    mut v___y_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1605_: usize = 0;
    let mut v___x_1606_: usize = 0;
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1605_ = lean_array_size(v_bs_1598_);
    v___x_1606_ = 0usize;
    v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__5(v_sz_1605_, v___x_1606_, v_bs_1598_);
    v___x_1608_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v___x_1607_, v_k_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
    crate::leanh::lean_dec_ref(v___x_1607_);
    return v___x_1608_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg___boxed(
    mut v_bs_1609_: *mut crate::leanh::LeanObject,
    mut v_k_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1616_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_bs_1609_, v_k_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
    crate::leanh::lean_dec(v___y_1614_);
    crate::leanh::lean_dec_ref(v___y_1613_);
    crate::leanh::lean_dec(v___y_1612_);
    crate::leanh::lean_dec_ref(v___y_1611_);
    return v_res_1616_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4(
    mut v_00_u03b1_1617_: *mut crate::leanh::LeanObject,
    mut v_bs_1618_: *mut crate::leanh::LeanObject,
    mut v_k_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_bs_1618_, v_k_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
    return v___x_1625_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___boxed(
    mut v_00_u03b1_1626_: *mut crate::leanh::LeanObject,
    mut v_bs_1627_: *mut crate::leanh::LeanObject,
    mut v_k_1628_: *mut crate::leanh::LeanObject,
    mut v___y_1629_: *mut crate::leanh::LeanObject,
    mut v___y_1630_: *mut crate::leanh::LeanObject,
    mut v___y_1631_: *mut crate::leanh::LeanObject,
    mut v___y_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1634_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4(v_00_u03b1_1626_, v_bs_1627_, v_k_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
    crate::leanh::lean_dec(v___y_1632_);
    crate::leanh::lean_dec_ref(v___y_1631_);
    crate::leanh::lean_dec(v___y_1630_);
    crate::leanh::lean_dec_ref(v___y_1629_);
    return v_res_1634_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2(
    mut v_name_1638_: *mut crate::leanh::LeanObject,
    mut v_us_1639_: *mut crate::leanh::LeanObject,
    mut v_xs1_1640_: *mut crate::leanh::LeanObject,
    mut v_xs2_1641_: *mut crate::leanh::LeanObject,
    mut v_x_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1648_ =
        l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___closed__1;
    crate::leanh::lean_inc(v_us_1639_);
    crate::leanh::lean_inc(v_name_1638_);
    v___x_1649_ = l_Lean_mkConst(v_name_1638_, v_us_1639_);
    crate::leanh::lean_inc_ref(v___x_1649_);
    crate::leanh::lean_inc_ref_n(v_xs2_1641_, 2);
    crate::leanh::lean_inc_ref(v_xs1_1640_);
    v___f_1650_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__1___boxed
            as *mut core::ffi::c_void,
        11,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1650_, 0, v_name_1638_);
    crate::leanh::lean_closure_set(v___f_1650_, 1, v_us_1639_);
    crate::leanh::lean_closure_set(v___f_1650_, 2, v_xs1_1640_);
    crate::leanh::lean_closure_set(v___f_1650_, 3, v_xs2_1641_);
    crate::leanh::lean_closure_set(v___f_1650_, 4, v___x_1649_);
    v___x_1651_ = l_Lean_mkAppN(v___x_1649_, v_xs1_1640_);
    v___x_1652_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2___boxed as *mut core::ffi::c_void, 9, 4);
    crate::leanh::lean_closure_set(v___x_1652_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1652_, 1, v___x_1648_);
    crate::leanh::lean_closure_set(v___x_1652_, 2, v___x_1651_);
    crate::leanh::lean_closure_set(v___x_1652_, 3, v___f_1650_);
    v___x_1653_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__3___boxed as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1653_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1653_, 1, v_xs2_1641_);
    crate::leanh::lean_closure_set(v___x_1653_, 2, v___x_1652_);
    v___x_1654_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___boxed as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1654_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1654_, 1, v_xs2_1641_);
    crate::leanh::lean_closure_set(v___x_1654_, 2, v___x_1653_);
    v___x_1655_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4___redArg(v_xs1_1640_, v___x_1654_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
    return v___x_1655_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___boxed(
    mut v_name_1656_: *mut crate::leanh::LeanObject,
    mut v_us_1657_: *mut crate::leanh::LeanObject,
    mut v_xs1_1658_: *mut crate::leanh::LeanObject,
    mut v_xs2_1659_: *mut crate::leanh::LeanObject,
    mut v_x_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2(
        v_name_1656_,
        v_us_1657_,
        v_xs1_1658_,
        v_xs2_1659_,
        v_x_1660_,
        v___y_1661_,
        v___y_1662_,
        v___y_1663_,
        v___y_1664_,
    );
    crate::leanh::lean_dec(v___y_1664_);
    crate::leanh::lean_dec_ref(v___y_1663_);
    crate::leanh::lean_dec(v___y_1662_);
    crate::leanh::lean_dec_ref(v___y_1661_);
    crate::leanh::lean_dec_ref(v_x_1660_);
    return v_res_1666_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3(
    mut v_name_1667_: *mut crate::leanh::LeanObject,
    mut v_us_1668_: *mut crate::leanh::LeanObject,
    mut v_type_1669_: *mut crate::leanh::LeanObject,
    mut v___x_1670_: *mut crate::leanh::LeanObject,
    mut v_xs1_1671_: *mut crate::leanh::LeanObject,
    mut v_x_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1678_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__2___boxed
            as *mut core::ffi::c_void,
        10,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1678_, 0, v_name_1667_);
    crate::leanh::lean_closure_set(v___f_1678_, 1, v_us_1668_);
    crate::leanh::lean_closure_set(v___f_1678_, 2, v_xs1_1671_);
    v___x_1679_ = 0;
    v___x_1680_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_1669_, v___x_1670_, v___f_1678_, v___x_1679_, v___x_1679_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
    return v___x_1680_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3___boxed(
    mut v_name_1681_: *mut crate::leanh::LeanObject,
    mut v_us_1682_: *mut crate::leanh::LeanObject,
    mut v_type_1683_: *mut crate::leanh::LeanObject,
    mut v___x_1684_: *mut crate::leanh::LeanObject,
    mut v_xs1_1685_: *mut crate::leanh::LeanObject,
    mut v_x_1686_: *mut crate::leanh::LeanObject,
    mut v___y_1687_: *mut crate::leanh::LeanObject,
    mut v___y_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
    mut v___y_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3(
        v_name_1681_,
        v_us_1682_,
        v_type_1683_,
        v___x_1684_,
        v_xs1_1685_,
        v_x_1686_,
        v___y_1687_,
        v___y_1688_,
        v___y_1689_,
        v___y_1690_,
    );
    crate::leanh::lean_dec(v___y_1690_);
    crate::leanh::lean_dec_ref(v___y_1689_);
    crate::leanh::lean_dec(v___y_1688_);
    crate::leanh::lean_dec_ref(v___y_1687_);
    crate::leanh::lean_dec_ref(v_x_1686_);
    return v_res_1692_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__0(
    mut v_a_1693_: *mut crate::leanh::LeanObject,
    mut v_a_1694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1693_) == 0 {
                    v___x_1695_ = l_List_reverse___redArg(v_a_1694_);
                    return v___x_1695_;
                } else {
                    v_head_1696_ = crate::leanh::lean_ctor_get(v_a_1693_, 0);
                    v_tail_1697_ = crate::leanh::lean_ctor_get(v_a_1693_, 1);
                    v_isSharedCheck_1706_ = (!crate::leanh::lean_is_exclusive(v_a_1693_)) as u8;
                    if v_isSharedCheck_1706_ == 0 {
                        v___x_1699_ = v_a_1693_;
                        v_isShared_1700_ = v_isSharedCheck_1706_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1697_);
                        crate::leanh::lean_inc(v_head_1696_);
                        crate::leanh::lean_dec(v_a_1693_);
                        v___x_1699_ = crate::leanh::lean_box(0);
                        v_isShared_1700_ = v_isSharedCheck_1706_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1701_ = l_Lean_mkLevelParam(v_head_1696_);
                if v_isShared_1700_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1699_, 1, v_a_1694_);
                    crate::leanh::lean_ctor_set(v___x_1699_, 0, v___x_1701_);
                    v___x_1703_ = v___x_1699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_a_1694_);
                    v___x_1703_ = v_reuseFailAlloc_1705_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1693_ = v_tail_1697_;
                v_a_1694_ = v___x_1703_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(
    mut v_thmName_1707_: *mut crate::leanh::LeanObject,
    mut v_indVal_1708_: *mut crate::leanh::LeanObject,
    mut v_a_1709_: *mut crate::leanh::LeanObject,
    mut v_a_1710_: *mut crate::leanh::LeanObject,
    mut v_a_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toConstantVal_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1722_: u8 = 0;
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1761_: u8 = 0;
    let mut v_a_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v_unused_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut v_a_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1787_: u8 = 0;
    let mut v_a_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toConstantVal_1714_ = crate::leanh::lean_ctor_get(v_indVal_1708_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_1714_);
                v_numParams_1715_ = crate::leanh::lean_ctor_get(v_indVal_1708_, 1);
                crate::leanh::lean_inc(v_numParams_1715_);
                v_numIndices_1716_ = crate::leanh::lean_ctor_get(v_indVal_1708_, 2);
                crate::leanh::lean_inc(v_numIndices_1716_);
                crate::leanh::lean_dec_ref(v_indVal_1708_);
                v_name_1717_ = crate::leanh::lean_ctor_get(v_toConstantVal_1714_, 0);
                v_levelParams_1718_ = crate::leanh::lean_ctor_get(v_toConstantVal_1714_, 1);
                v_type_1719_ = crate::leanh::lean_ctor_get(v_toConstantVal_1714_, 2);
                v_isSharedCheck_1796_ =
                    (!crate::leanh::lean_is_exclusive(v_toConstantVal_1714_)) as u8;
                if v_isSharedCheck_1796_ == 0 {
                    v___x_1721_ = v_toConstantVal_1714_;
                    v_isShared_1722_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_type_1719_);
                    crate::leanh::lean_inc(v_levelParams_1718_);
                    crate::leanh::lean_inc(v_name_1717_);
                    crate::leanh::lean_dec(v_toConstantVal_1714_);
                    v___x_1721_ = crate::leanh::lean_box(0);
                    v_isShared_1722_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1723_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_levelParams_1718_);
                v_us_1724_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__0(v_levelParams_1718_, v___x_1723_);
                v___x_1725_ = lean_nat_add(v_numParams_1715_, v_numIndices_1716_);
                crate::leanh::lean_dec(v_numIndices_1716_);
                crate::leanh::lean_dec(v_numParams_1715_);
                crate::leanh::lean_inc(v___x_1725_);
                v___x_1726_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1726_, 0, v___x_1725_);
                crate::leanh::lean_inc_ref(v___x_1726_);
                crate::leanh::lean_inc_ref(v_type_1719_);
                v___f_1727_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___lam__3___boxed as *mut core::ffi::c_void, 11, 4);
                crate::leanh::lean_closure_set(v___f_1727_, 0, v_name_1717_);
                crate::leanh::lean_closure_set(v___f_1727_, 1, v_us_1724_);
                crate::leanh::lean_closure_set(v___f_1727_, 2, v_type_1719_);
                crate::leanh::lean_closure_set(v___f_1727_, 3, v___x_1726_);
                v___x_1728_ = 0;
                v___x_1729_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__5___redArg(v_type_1719_, v___x_1726_, v___f_1727_, v___x_1728_, v___x_1728_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
                if crate::leanh::lean_obj_tag(v___x_1729_) == 0 {
                    v_a_1730_ = crate::leanh::lean_ctor_get(v___x_1729_, 0);
                    crate::leanh::lean_inc_n(v_a_1730_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1729_, 1);
                    v___x_1731_ = crate::leanh::lean_box(0);
                    v___x_1732_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v_a_1730_,
                        v___x_1731_,
                        v_a_1709_,
                        v_a_1710_,
                        v_a_1711_,
                        v_a_1712_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1732_) == 0 {
                        v_a_1733_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                        crate::leanh::lean_inc(v_a_1733_);
                        crate::leanh::lean_dec_ref_known(v___x_1732_, 1);
                        v___x_1734_ = l_Lean_Expr_mvarId_x21(v_a_1733_);
                        v___x_1735_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1736_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1737_ = lean_nat_add(v___x_1725_, v___x_1736_);
                        crate::leanh::lean_dec(v___x_1725_);
                        v___x_1738_ = lean_nat_mul(v___x_1735_, v___x_1737_);
                        crate::leanh::lean_dec(v___x_1737_);
                        v___x_1739_ = l_Lean_Meta_introNCore(
                            v___x_1734_,
                            v___x_1738_,
                            v___x_1723_,
                            v___x_1728_,
                            v___x_1728_,
                            v_a_1709_,
                            v_a_1710_,
                            v_a_1711_,
                            v_a_1712_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1739_) == 0 {
                            v_a_1740_ = crate::leanh::lean_ctor_get(v___x_1739_, 0);
                            crate::leanh::lean_inc(v_a_1740_);
                            crate::leanh::lean_dec_ref_known(v___x_1739_, 1);
                            v_snd_1741_ = crate::leanh::lean_ctor_get(v_a_1740_, 1);
                            v_isSharedCheck_1770_ =
                                (!crate::leanh::lean_is_exclusive(v_a_1740_)) as u8;
                            if v_isSharedCheck_1770_ == 0 {
                                v_unused_1771_ = crate::leanh::lean_ctor_get(v_a_1740_, 0);
                                crate::leanh::lean_dec(v_unused_1771_);
                                v___x_1743_ = v_a_1740_;
                                v_isShared_1744_ = v_isSharedCheck_1770_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1741_);
                                crate::leanh::lean_dec(v_a_1740_);
                                v___x_1743_ = crate::leanh::lean_box(0);
                                v_isShared_1744_ = v_isSharedCheck_1770_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1733_);
                            crate::leanh::lean_dec(v_a_1730_);
                            crate::leanh::lean_del_object(v___x_1721_);
                            crate::leanh::lean_dec(v_levelParams_1718_);
                            crate::leanh::lean_dec(v_thmName_1707_);
                            v_a_1772_ = crate::leanh::lean_ctor_get(v___x_1739_, 0);
                            v_isSharedCheck_1779_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1739_)) as u8;
                            if v_isSharedCheck_1779_ == 0 {
                                v___x_1774_ = v___x_1739_;
                                v_isShared_1775_ = v_isSharedCheck_1779_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1772_);
                                crate::leanh::lean_dec(v___x_1739_);
                                v___x_1774_ = crate::leanh::lean_box(0);
                                v_isShared_1775_ = v_isSharedCheck_1779_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1730_);
                        crate::leanh::lean_dec(v___x_1725_);
                        crate::leanh::lean_del_object(v___x_1721_);
                        crate::leanh::lean_dec(v_levelParams_1718_);
                        crate::leanh::lean_dec(v_thmName_1707_);
                        v_a_1780_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                        v_isSharedCheck_1787_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1732_)) as u8;
                        if v_isSharedCheck_1787_ == 0 {
                            v___x_1782_ = v___x_1732_;
                            v_isShared_1783_ = v_isSharedCheck_1787_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1780_);
                            crate::leanh::lean_dec(v___x_1732_);
                            v___x_1782_ = crate::leanh::lean_box(0);
                            v_isShared_1783_ = v_isSharedCheck_1787_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1725_);
                    crate::leanh::lean_del_object(v___x_1721_);
                    crate::leanh::lean_dec(v_levelParams_1718_);
                    crate::leanh::lean_dec(v_thmName_1707_);
                    v_a_1788_ = crate::leanh::lean_ctor_get(v___x_1729_, 0);
                    v_isSharedCheck_1795_ = (!crate::leanh::lean_is_exclusive(v___x_1729_)) as u8;
                    if v_isSharedCheck_1795_ == 0 {
                        v___x_1790_ = v___x_1729_;
                        v_isShared_1791_ = v_isSharedCheck_1795_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1788_);
                        crate::leanh::lean_dec(v___x_1729_);
                        v___x_1790_ = crate::leanh::lean_box(0);
                        v_isShared_1791_ = v_isSharedCheck_1795_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1745_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_repeatIntroSubstRefl(v_snd_1741_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
                if crate::leanh::lean_obj_tag(v___x_1745_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1745_, 1);
                    v___x_1746_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__6___redArg(v_a_1733_, v_a_1710_);
                    v_a_1747_ = crate::leanh::lean_ctor_get(v___x_1746_, 0);
                    v_isSharedCheck_1761_ = (!crate::leanh::lean_is_exclusive(v___x_1746_)) as u8;
                    if v_isSharedCheck_1761_ == 0 {
                        v___x_1749_ = v___x_1746_;
                        v_isShared_1750_ = v_isSharedCheck_1761_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1747_);
                        crate::leanh::lean_dec(v___x_1746_);
                        v___x_1749_ = crate::leanh::lean_box(0);
                        v_isShared_1750_ = v_isSharedCheck_1761_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1743_);
                    crate::leanh::lean_dec(v_a_1733_);
                    crate::leanh::lean_dec(v_a_1730_);
                    crate::leanh::lean_del_object(v___x_1721_);
                    crate::leanh::lean_dec(v_levelParams_1718_);
                    crate::leanh::lean_dec(v_thmName_1707_);
                    v_a_1762_ = crate::leanh::lean_ctor_get(v___x_1745_, 0);
                    v_isSharedCheck_1769_ = (!crate::leanh::lean_is_exclusive(v___x_1745_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1764_ = v___x_1745_;
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1762_);
                        crate::leanh::lean_dec(v___x_1745_);
                        v___x_1764_ = crate::leanh::lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_thmName_1707_);
                if v_isShared_1722_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1721_, 2, v_a_1730_);
                    crate::leanh::lean_ctor_set(v___x_1721_, 0, v_thmName_1707_);
                    v___x_1752_ = v___x_1721_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_thmName_1707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_levelParams_1718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_a_1730_);
                    v___x_1752_ = v_reuseFailAlloc_1760_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1744_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1743_, 1);
                    crate::leanh::lean_ctor_set(v___x_1743_, 1, v___x_1723_);
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v_thmName_1707_);
                    v___x_1754_ = v___x_1743_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1759_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_thmName_1707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1723_);
                    v___x_1754_ = v_reuseFailAlloc_1759_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1755_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1755_, 0, v___x_1752_);
                crate::leanh::lean_ctor_set(v___x_1755_, 1, v_a_1747_);
                crate::leanh::lean_ctor_set(v___x_1755_, 2, v___x_1754_);
                if v_isShared_1750_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1749_, 0, v___x_1755_);
                    v___x_1757_ = v___x_1749_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
                    v___x_1757_ = v_reuseFailAlloc_1758_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1757_;
            }
            7 => {
                if v_isShared_1765_ == 0 {
                    v___x_1767_ = v___x_1764_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
                    v___x_1767_ = v_reuseFailAlloc_1768_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1767_;
            }
            9 => {
                if v_isShared_1775_ == 0 {
                    v___x_1777_ = v___x_1774_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
                    v___x_1777_ = v_reuseFailAlloc_1778_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1777_;
            }
            11 => {
                if v_isShared_1783_ == 0 {
                    v___x_1785_ = v___x_1782_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1786_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
                    v___x_1785_ = v_reuseFailAlloc_1786_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1785_;
            }
            13 => {
                if v_isShared_1791_ == 0 {
                    v___x_1793_ = v___x_1790_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
                    v___x_1793_ = v_reuseFailAlloc_1794_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(
    mut v_thmName_1797_: *mut crate::leanh::LeanObject,
    mut v_indVal_1798_: *mut crate::leanh::LeanObject,
    mut v_a_1799_: *mut crate::leanh::LeanObject,
    mut v_a_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
    mut v_a_1802_: *mut crate::leanh::LeanObject,
    mut v_a_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1804_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(
        v_thmName_1797_,
        v_indVal_1798_,
        v_a_1799_,
        v_a_1800_,
        v_a_1801_,
        v_a_1802_,
    );
    crate::leanh::lean_dec(v_a_1802_);
    crate::leanh::lean_dec_ref(v_a_1801_);
    crate::leanh::lean_dec(v_a_1800_);
    crate::leanh::lean_dec_ref(v_a_1799_);
    return v_res_1804_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2(
    mut v_00_u03b1_1805_: *mut crate::leanh::LeanObject,
    mut v_name_1806_: *mut crate::leanh::LeanObject,
    mut v_bi_1807_: u8,
    mut v_type_1808_: *mut crate::leanh::LeanObject,
    mut v_k_1809_: *mut crate::leanh::LeanObject,
    mut v_kind_1810_: u8,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___redArg(v_name_1806_, v_bi_1807_, v_type_1808_, v_k_1809_, v_kind_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
    return v___x_1816_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2___boxed(
    mut v_00_u03b1_1817_: *mut crate::leanh::LeanObject,
    mut v_name_1818_: *mut crate::leanh::LeanObject,
    mut v_bi_1819_: *mut crate::leanh::LeanObject,
    mut v_type_1820_: *mut crate::leanh::LeanObject,
    mut v_k_1821_: *mut crate::leanh::LeanObject,
    mut v_kind_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_1828_: u8 = 0;
    let mut v_kind_boxed_1829_: u8 = 0;
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1828_ = (crate::leanh::lean_unbox(v_bi_1819_) as u8);
    v_kind_boxed_1829_ = (crate::leanh::lean_unbox(v_kind_1822_) as u8);
    v_res_1830_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__2_spec__2(v_00_u03b1_1817_, v_name_1818_, v_bi_boxed_1828_, v_type_1820_, v_k_1821_, v_kind_boxed_1829_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
    crate::leanh::lean_dec(v___y_1826_);
    crate::leanh::lean_dec_ref(v___y_1825_);
    crate::leanh::lean_dec(v___y_1824_);
    crate::leanh::lean_dec_ref(v___y_1823_);
    return v_res_1830_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6(
    mut v_00_u03b1_1831_: *mut crate::leanh::LeanObject,
    mut v_bs_1832_: *mut crate::leanh::LeanObject,
    mut v_k_1833_: *mut crate::leanh::LeanObject,
    mut v___y_1834_: *mut crate::leanh::LeanObject,
    mut v___y_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___redArg(v_bs_1832_, v_k_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
    return v___x_1839_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6___boxed(
    mut v_00_u03b1_1840_: *mut crate::leanh::LeanObject,
    mut v_bs_1841_: *mut crate::leanh::LeanObject,
    mut v_k_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f_spec__4_spec__6(v_00_u03b1_1840_, v_bs_1841_, v_k_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
    crate::leanh::lean_dec(v___y_1846_);
    crate::leanh::lean_dec_ref(v___y_1845_);
    crate::leanh::lean_dec(v___y_1844_);
    crate::leanh::lean_dec_ref(v___y_1843_);
    crate::leanh::lean_dec_ref(v_bs_1841_);
    return v_res_1848_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(
    mut v_env_1849_: *mut crate::leanh::LeanObject,
    mut v_n_1850_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_n_1850_) == 1 {
        let mut v_pre_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1854_: u8 = 0;
        v_pre_1851_ = crate::leanh::lean_ctor_get(v_n_1850_, 0);
        crate::leanh::lean_inc(v_pre_1851_);
        v_str_1852_ = crate::leanh::lean_ctor_get(v_n_1850_, 1);
        crate::leanh::lean_inc_ref(v_str_1852_);
        crate::leanh::lean_dec_ref_known(v_n_1850_, 2);
        v___x_1853_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0;
        v___x_1854_ = lean_string_dec_eq(v_str_1852_, v___x_1853_);
        crate::leanh::lean_dec_ref(v_str_1852_);
        if v___x_1854_ == 0 {
            crate::leanh::lean_dec(v_pre_1851_);
            crate::leanh::lean_dec_ref(v_env_1849_);
            return v___x_1854_;
        } else {
            let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1855_ = l_isCtorIdxCore_x3f(v_env_1849_, v_pre_1851_);
            if crate::leanh::lean_obj_tag(v___x_1855_) == 0 {
                let mut v___x_1856_: u8 = 0;
                v___x_1856_ = 0;
                return v___x_1856_;
            } else {
                crate::leanh::lean_dec_ref_known(v___x_1855_, 1);
                return v___x_1854_;
            }
        }
    } else {
        let mut v___x_1857_: u8 = 0;
        crate::leanh::lean_dec(v_n_1850_);
        crate::leanh::lean_dec_ref(v_env_1849_);
        v___x_1857_ = 0;
        return v___x_1857_;
    }
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed(
    mut v_env_1858_: *mut crate::leanh::LeanObject,
    mut v_n_1859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1860_: u8 = 0;
    let mut v_r_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1860_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_(v_env_1858_, v_n_1859_);
    v_r_1861_ = crate::leanh::lean_box((v_res_1860_) as usize);
    return v_r_1861_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1864_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_;
    v___x_1865_ = l_Lean_registerReservedNamePredicate(v___f_1864_);
    return v___x_1865_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2____boxed(
    mut v_a_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_();
    return v_res_1867_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(
    mut v_thm_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1877_: u8 = 0;
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1871_ = lean_st_ref_get(v___y_1869_);
                v_env_1872_ = crate::leanh::lean_ctor_get(v___x_1871_, 0);
                crate::leanh::lean_inc_ref_n(v_env_1872_, 2);
                crate::leanh::lean_dec(v___x_1871_);
                v_toConstantVal_1873_ = crate::leanh::lean_ctor_get(v_thm_1868_, 0);
                v_value_1874_ = crate::leanh::lean_ctor_get(v_thm_1868_, 1);
                v_all_1875_ = crate::leanh::lean_ctor_get(v_thm_1868_, 2);
                v_type_1885_ = crate::leanh::lean_ctor_get(v_toConstantVal_1873_, 2);
                v___x_1886_ = l_Lean_Environment_hasUnsafe(v_env_1872_, v_type_1885_);
                if v___x_1886_ == 0 {
                    v___x_1887_ = l_Lean_Environment_hasUnsafe(v_env_1872_, v_value_1874_);
                    v___y_1877_ = v___x_1887_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_1872_);
                    v___y_1877_ = v___x_1886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1877_ == 0 {
                    v___x_1878_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1878_, 0, v_thm_1868_);
                    v___x_1879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1879_, 0, v___x_1878_);
                    return v___x_1879_;
                } else {
                    crate::leanh::lean_inc(v_all_1875_);
                    crate::leanh::lean_inc_ref(v_value_1874_);
                    crate::leanh::lean_inc_ref(v_toConstantVal_1873_);
                    crate::leanh::lean_dec_ref(v_thm_1868_);
                    v___x_1880_ = crate::leanh::lean_box(0);
                    v___x_1881_ = 0;
                    v___x_1882_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1882_, 0, v_toConstantVal_1873_);
                    crate::leanh::lean_ctor_set(v___x_1882_, 1, v_value_1874_);
                    crate::leanh::lean_ctor_set(v___x_1882_, 2, v___x_1880_);
                    crate::leanh::lean_ctor_set(v___x_1882_, 3, v_all_1875_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1882_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_1881_,
                    );
                    v___x_1883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1883_, 0, v___x_1882_);
                    v___x_1884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1884_, 0, v___x_1883_);
                    return v___x_1884_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_thm_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1891_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_thm_1888_, v___y_1889_);
    crate::leanh::lean_dec(v___y_1889_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0(
    mut v_thm_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
    mut v___y_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_thm_1892_, v___y_1896_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___boxed(
    mut v_thm_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
    mut v___y_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0(v_thm_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
    crate::leanh::lean_dec(v___y_1903_);
    crate::leanh::lean_dec_ref(v___y_1902_);
    crate::leanh::lean_dec(v___y_1901_);
    crate::leanh::lean_dec_ref(v___y_1900_);
    return v_res_1905_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(
    mut v_name_1906_: *mut crate::leanh::LeanObject,
    mut v_val_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
    mut v___y_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1913_ =
                    l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_mkHInjectiveTheorem_x3f(
                        v_name_1906_,
                        v_val_1907_,
                        v___y_1908_,
                        v___y_1909_,
                        v___y_1910_,
                        v___y_1911_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1913_) == 0 {
                    v_a_1914_ = crate::leanh::lean_ctor_get(v___x_1913_, 0);
                    crate::leanh::lean_inc(v_a_1914_);
                    crate::leanh::lean_dec_ref_known(v___x_1913_, 1);
                    v___x_1915_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__spec__0___redArg(v_a_1914_, v___y_1911_);
                    v_a_1916_ = crate::leanh::lean_ctor_get(v___x_1915_, 0);
                    crate::leanh::lean_inc(v_a_1916_);
                    crate::leanh::lean_dec_ref(v___x_1915_);
                    v___x_1917_ = 0;
                    v___x_1918_ = l_Lean_addDecl(v_a_1916_, v___x_1917_, v___y_1910_, v___y_1911_);
                    return v___x_1918_;
                } else {
                    v_a_1919_ = crate::leanh::lean_ctor_get(v___x_1913_, 0);
                    v_isSharedCheck_1926_ = (!crate::leanh::lean_is_exclusive(v___x_1913_)) as u8;
                    if v_isSharedCheck_1926_ == 0 {
                        v___x_1921_ = v___x_1913_;
                        v_isShared_1922_ = v_isSharedCheck_1926_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1919_);
                        crate::leanh::lean_dec(v___x_1913_);
                        v___x_1921_ = crate::leanh::lean_box(0);
                        v_isShared_1922_ = v_isSharedCheck_1926_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1922_ == 0 {
                    v___x_1924_ = v___x_1921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
                    v___x_1924_ = v_reuseFailAlloc_1925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(
    mut v_name_1927_: *mut crate::leanh::LeanObject,
    mut v_val_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(v_name_1927_, v_val_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
    crate::leanh::lean_dec(v___y_1932_);
    crate::leanh::lean_dec_ref(v___y_1931_);
    crate::leanh::lean_dec(v___y_1930_);
    crate::leanh::lean_dec_ref(v___y_1929_);
    return v_res_1934_;
}
pub unsafe fn _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1935_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1935_;
}
pub unsafe fn _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1936_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
    v___x_1937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1937_, 0, v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1938_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1939_ = lean_mk_empty_array_with_capacity(v___x_1938_);
    v___x_1940_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1940_, 0, v___x_1939_);
    return v___x_1940_;
}
pub unsafe fn _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1941_: usize = 0;
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = 5usize;
    v___x_1942_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1943_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1944_ = lean_mk_empty_array_with_capacity(v___x_1943_);
    v___x_1945_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
    v___x_1946_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1946_, 0, v___x_1945_);
    crate::leanh::lean_ctor_set(v___x_1946_, 1, v___x_1944_);
    crate::leanh::lean_ctor_set(v___x_1946_, 2, v___x_1942_);
    crate::leanh::lean_ctor_set(v___x_1946_, 3, v___x_1942_);
    crate::leanh::lean_ctor_set_usize(v___x_1946_, 4, v___x_1941_);
    return v___x_1946_;
}
pub unsafe fn _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1947_ = crate::leanh::lean_box(1);
    v___x_1948_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
    v___x_1949_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
    v___x_1950_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1950_, 0, v___x_1949_);
    crate::leanh::lean_ctor_set(v___x_1950_, 1, v___x_1948_);
    crate::leanh::lean_ctor_set(v___x_1950_, 2, v___x_1947_);
    return v___x_1950_;
}
pub unsafe fn _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1953_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
    v___x_1954_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1955_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1955_, 0, v___x_1954_);
    crate::leanh::lean_ctor_set(v___x_1955_, 1, v___x_1954_);
    crate::leanh::lean_ctor_set(v___x_1955_, 2, v___x_1954_);
    crate::leanh::lean_ctor_set(v___x_1955_, 3, v___x_1954_);
    crate::leanh::lean_ctor_set(v___x_1955_, 4, v___x_1953_);
    crate::leanh::lean_ctor_set(v___x_1955_, 5, v___x_1953_);
    crate::leanh::lean_ctor_set(v___x_1955_, 6, v___x_1953_);
    crate::leanh::lean_ctor_set(v___x_1955_, 7, v___x_1953_);
    crate::leanh::lean_ctor_set(v___x_1955_, 8, v___x_1953_);
    crate::leanh::lean_ctor_set(v___x_1955_, 9, v___x_1953_);
    return v___x_1955_;
}
pub unsafe fn _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1956_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
    v___x_1957_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1957_, 0, v___x_1956_);
    crate::leanh::lean_ctor_set(v___x_1957_, 1, v___x_1956_);
    crate::leanh::lean_ctor_set(v___x_1957_, 2, v___x_1956_);
    crate::leanh::lean_ctor_set(v___x_1957_, 3, v___x_1956_);
    crate::leanh::lean_ctor_set(v___x_1957_, 4, v___x_1956_);
    crate::leanh::lean_ctor_set(v___x_1957_, 5, v___x_1956_);
    return v___x_1957_;
}
pub unsafe fn _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
    v___x_1959_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1959_, 0, v___x_1958_);
    crate::leanh::lean_ctor_set(v___x_1959_, 1, v___x_1958_);
    crate::leanh::lean_ctor_set(v___x_1959_, 2, v___x_1958_);
    crate::leanh::lean_ctor_set(v___x_1959_, 3, v___x_1958_);
    crate::leanh::lean_ctor_set(v___x_1959_, 4, v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(
    mut v___x_1960_: *mut crate::leanh::LeanObject,
    mut v_name_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1966_: u8 = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: u8 = 0;
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1978_: u8 = 0;
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: u64 = 0;
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut v_unused_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut v___x_2015_: u8 = 0;
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_name_1961_) == 1 {
                    v_pre_1969_ = crate::leanh::lean_ctor_get(v_name_1961_, 0);
                    crate::leanh::lean_inc(v_pre_1969_);
                    v_str_1970_ = crate::leanh::lean_ctor_get(v_name_1961_, 1);
                    v___x_1971_ =
                        l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_hinjSuffix___closed__0;
                    v___x_1972_ = lean_string_dec_eq(v_str_1970_, v___x_1971_);
                    if v___x_1972_ == 0 {
                        crate::leanh::lean_dec(v_pre_1969_);
                        crate::leanh::lean_dec_ref_known(v_name_1961_, 2);
                        crate::leanh::lean_dec(v___x_1960_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1973_ = lean_st_ref_get(v___y_1963_);
                        v_env_1974_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                        crate::leanh::lean_inc_ref(v_env_1974_);
                        crate::leanh::lean_dec(v___x_1973_);
                        crate::leanh::lean_inc(v_pre_1969_);
                        v___x_1975_ = l_isCtorIdxCore_x3f(v_env_1974_, v_pre_1969_);
                        if crate::leanh::lean_obj_tag(v___x_1975_) == 1 {
                            v_val_1976_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                            crate::leanh::lean_inc(v_val_1976_);
                            crate::leanh::lean_dec_ref_known(v___x_1975_, 1);
                            v___x_1977_ = 0;
                            v___x_1978_ = 1;
                            v___x_1979_ = 0;
                            v___x_1980_ = 2;
                            v___x_1981_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 0 as u32, v___x_1977_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 1 as u32, v___x_1977_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 2 as u32, v___x_1977_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 3 as u32, v___x_1977_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 4 as u32, v___x_1977_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 5 as u32, v___x_1972_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 6 as u32, v___x_1972_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 7 as u32, v___x_1977_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 8 as u32, v___x_1972_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 9 as u32, v___x_1978_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 10 as u32, v___x_1979_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 11 as u32, v___x_1972_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 12 as u32, v___x_1972_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 13 as u32, v___x_1972_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 14 as u32, v___x_1980_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 15 as u32, v___x_1972_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 16 as u32, v___x_1972_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 17 as u32, v___x_1972_);
                            crate::leanh::lean_ctor_set_uint8(v___x_1981_, 18 as u32, v___x_1972_);
                            v___x_1982_ =
                                l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1981_);
                            v___x_1983_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                            crate::leanh::lean_ctor_set(v___x_1983_, 0, v___x_1981_);
                            crate::leanh::lean_ctor_set_uint64(
                                v___x_1983_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_1982_,
                            );
                            v___x_1984_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1985_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
                            v___x_1986_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
                            v___x_1987_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
                            v___x_1988_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___x_1960_);
                            v___x_1989_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                            crate::leanh::lean_ctor_set(v___x_1989_, 0, v___x_1983_);
                            crate::leanh::lean_ctor_set(v___x_1989_, 1, v___x_1960_);
                            crate::leanh::lean_ctor_set(v___x_1989_, 2, v___x_1986_);
                            crate::leanh::lean_ctor_set(v___x_1989_, 3, v___x_1987_);
                            crate::leanh::lean_ctor_set(v___x_1989_, 4, v___x_1988_);
                            crate::leanh::lean_ctor_set(v___x_1989_, 5, v___x_1984_);
                            crate::leanh::lean_ctor_set(v___x_1989_, 6, v___x_1988_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1989_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                                v___x_1977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1989_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1)
                                    as u32,
                                v___x_1977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1989_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2)
                                    as u32,
                                v___x_1977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1989_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3)
                                    as u32,
                                v___x_1972_,
                            );
                            v___x_1990_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
                            v___x_1991_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
                            v___x_1992_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_);
                            v___x_1993_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1993_, 0, v___x_1990_);
                            crate::leanh::lean_ctor_set(v___x_1993_, 1, v___x_1991_);
                            crate::leanh::lean_ctor_set(v___x_1993_, 2, v___x_1960_);
                            crate::leanh::lean_ctor_set(v___x_1993_, 3, v___x_1985_);
                            crate::leanh::lean_ctor_set(v___x_1993_, 4, v___x_1992_);
                            v___x_1994_ = lean_st_mk_ref(v___x_1993_);
                            crate::leanh::lean_inc_ref(v_name_1961_);
                            v___f_1995_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 7, 2);
                            crate::leanh::lean_closure_set(v___f_1995_, 0, v_name_1961_);
                            crate::leanh::lean_closure_set(v___f_1995_, 1, v_val_1976_);
                            v___x_1996_ = l_Lean_Meta_realizeConst(
                                v_pre_1969_,
                                v_name_1961_,
                                v___f_1995_,
                                v___x_1989_,
                                v___x_1994_,
                                v___y_1962_,
                                v___y_1963_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_1989_, 7);
                            if crate::leanh::lean_obj_tag(v___x_1996_) == 0 {
                                v_isSharedCheck_2005_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1996_)) as u8;
                                if v_isSharedCheck_2005_ == 0 {
                                    v_unused_2006_ = crate::leanh::lean_ctor_get(v___x_1996_, 0);
                                    crate::leanh::lean_dec(v_unused_2006_);
                                    v___x_1998_ = v___x_1996_;
                                    v_isShared_1999_ = v_isSharedCheck_2005_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_1996_);
                                    v___x_1998_ = crate::leanh::lean_box(0);
                                    v_isShared_1999_ = v_isSharedCheck_2005_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1994_);
                                v_a_2007_ = crate::leanh::lean_ctor_get(v___x_1996_, 0);
                                v_isSharedCheck_2014_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1996_)) as u8;
                                if v_isSharedCheck_2014_ == 0 {
                                    v___x_2009_ = v___x_1996_;
                                    v_isShared_2010_ = v_isSharedCheck_2014_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2007_);
                                    crate::leanh::lean_dec(v___x_1996_);
                                    v___x_2009_ = crate::leanh::lean_box(0);
                                    v_isShared_2010_ = v_isSharedCheck_2014_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1975_);
                            crate::leanh::lean_dec(v_pre_1969_);
                            crate::leanh::lean_dec_ref_known(v_name_1961_, 2);
                            crate::leanh::lean_dec(v___x_1960_);
                            v___x_2015_ = 0;
                            v___x_2016_ = crate::leanh::lean_box((v___x_2015_) as usize);
                            v___x_2017_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2017_, 0, v___x_2016_);
                            return v___x_2017_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_name_1961_);
                    crate::leanh::lean_dec(v___x_1960_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1966_ = 0;
                v___x_1967_ = crate::leanh::lean_box((v___x_1966_) as usize);
                v___x_1968_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1968_, 0, v___x_1967_);
                return v___x_1968_;
            }
            2 => {
                v___x_2000_ = lean_st_ref_get(v___x_1994_);
                crate::leanh::lean_dec(v___x_1994_);
                crate::leanh::lean_dec(v___x_2000_);
                v___x_2001_ = crate::leanh::lean_box((v___x_1972_) as usize);
                if v_isShared_1999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1998_, 0, v___x_2001_);
                    v___x_2003_ = v___x_1998_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
                    v___x_2003_ = v_reuseFailAlloc_2004_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2003_;
            }
            4 => {
                if v_isShared_2010_ == 0 {
                    v___x_2012_ = v___x_2009_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
                    v___x_2012_ = v_reuseFailAlloc_2013_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(
    mut v___x_2018_: *mut crate::leanh::LeanObject,
    mut v_name_2019_: *mut crate::leanh::LeanObject,
    mut v___y_2020_: *mut crate::leanh::LeanObject,
    mut v___y_2021_: *mut crate::leanh::LeanObject,
    mut v___y_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2023_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_(v___x_2018_, v_name_2019_, v___y_2020_, v___y_2021_);
    crate::leanh::lean_dec(v___y_2021_);
    crate::leanh::lean_dec_ref(v___y_2020_);
    return v_res_2023_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2027_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_;
    v___x_2028_ = l_Lean_registerReservedNameAction(v___f_2027_);
    return v___x_2028_;
}
pub unsafe fn l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2____boxed(
    mut v_a_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2030_ = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_();
    return v_res_2030_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CtorIdxHInj(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_3745005406____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_CtorIdxHInj_0__Lean_Meta_initFn_00___x40_Lean_Meta_CtorIdxHInj_1686831688____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CtorIdxHInj(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CtorIdxHInj(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Subst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorIdxHInj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CtorIdxHInj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_CtorIdxHInj(builtin);
}
