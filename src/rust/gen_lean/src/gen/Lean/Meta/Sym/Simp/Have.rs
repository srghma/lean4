// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Have
// Imports: Lean.Meta.Sym.Simp.Lambda Lean.Meta.Sym.InstantiateS Lean.Meta.Sym.ReplaceS Lean.Meta.Sym.AbstractS Lean.Meta.Sym.InferType Lean.Meta.AppBuilder Lean.Meta.HaveTelescope Lean.Util.CollectFVars Init.Omega Init.While
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_set, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_instantiate_rev, lean_mk_array,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub,
    lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_sym_simp,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_instInhabited, l_Array_reverse___redArg};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instMonad___redArg, l_instInhabitedForall___redArg___lam__0___boxed,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_betaRev, l_Lean_Expr_bindingBody_x21,
    l_Lean_Expr_bindingDomain_x21, l_Lean_Expr_bvar___override, l_Lean_Expr_const___override,
    l_Lean_Expr_forallE___override, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_letNondep_x21, l_Lean_Expr_looseBVarRange, l_Lean_Expr_mdata___override,
    l_Lean_Expr_proj___override, l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr,
    l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp6, l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst,
    l_Lean_mkFVar,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_normalize, l_Lean_mkLevelIMax_x27};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkExpectedPropHint,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::HaveTelescope::{
    initialize_Lean_Meta_HaveTelescope, l_Lean_Meta_zetaUnused,
    runtime_initialize_Lean_Meta_HaveTelescope,
};
use crate::r#gen::Lean::Meta::Sym::AbstractS::{
    initialize_Lean_Meta_Sym_AbstractS, l_Lean_Meta_Sym_mkLambdaFVarsS,
    runtime_initialize_Lean_Meta_Sym_AbstractS,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    l_Lean_Meta_Sym_Internal_Builder_assertShared,
    l_Lean_Meta_Sym_Internal_Builder_share1___redArg, l_Lean_Meta_Sym_Internal_Sym_assertShared,
    l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::InferType::{
    initialize_Lean_Meta_Sym_InferType, l_Lean_Meta_Sym_getLevel___redArg,
    l_Lean_Meta_Sym_inferType___redArg, runtime_initialize_Lean_Meta_Sym_InferType,
};
use crate::r#gen::Lean::Meta::Sym::InstantiateS::{
    initialize_Lean_Meta_Sym_InstantiateS, l_Lean_Meta_Sym_instantiateRevRangeS,
    runtime_initialize_Lean_Meta_Sym_InstantiateS,
};
use crate::r#gen::Lean::Meta::Sym::ReplaceS::{
    initialize_Lean_Meta_Sym_ReplaceS, l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save,
    runtime_initialize_Lean_Meta_Sym_ReplaceS,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Lambda::{
    initialize_Lean_Meta_Sym_Simp_Lambda, l_Lean_Meta_Sym_Simp_simpLambda___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_Lambda,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    l_Lean_Meta_Sym_Simp_instInhabitedSimpM, l_Lean_Meta_Sym_Simp_mkRflResultCD,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_instInhabitedSymM, l_Lean_Meta_Sym_shareCommonInc___redArg,
};
use crate::r#gen::Lean::Util::CollectFVars::{
    initialize_Lean_Util_CollectFVars, l_Lean_collectFVars,
    runtime_initialize_Lean_Util_CollectFVars,
};
pub static l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__0_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 81, 117, 101, 114, 105, 101, 115, 0]};
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__1_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 67, 111, 110, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__2_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [75, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 109, 97, 112, 0]};
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__2_value) as *mut leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0_value) as *mut leanh::LeanObject,7839396180116328695 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 101, 102, 108, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2_value) as *mut leanh::LeanObject,13480818501600609864 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(0 as *mut leanh::LeanObject)] };
pub static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_toBetaApp___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Sym_Simp_toBetaApp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 72, 97, 118, 101, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2_value: leanh::LeanStringObject<66> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 66, m_capacity: 66, m_length: 65, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 72, 97, 118, 101, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 101, 108, 105, 109, 65, 117, 120, 65, 112, 112, 115, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_value: leanh::LeanStringObject<61> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 110, 117, 109, 65, 114, 103, 115, 32, 61, 61, 32, 101, 120, 112, 101, 99, 116, 101, 100, 78, 117, 109, 65, 114, 103, 115, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0_value: leanh::LeanStringObject<64> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 72, 97, 118, 101, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 116, 111, 72, 97, 118, 101, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0_value: leanh::LeanStringObject<61> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 72, 97, 118, 101, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 116, 111, 72, 97, 118, 101, 0]};
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0_value
) as *mut leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value) as *mut leanh::LeanObject,2642306550782628284 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 111, 110, 103, 114, 70, 117, 110, 39, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value) as *mut leanh::LeanObject,13901408594950942683 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value) as *mut leanh::LeanObject,11699215918282396216 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6_value: leanh::LeanStringObject<69> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 72, 97, 118, 101, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 83, 105, 109, 112, 46, 115, 105, 109, 112, 66, 101, 116, 97, 65, 112, 112, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0_value) as *mut leanh::LeanObject,17532416664988428445 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpLet___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Sym_Simp_simpLambda___boxed as *const core::ffi::c_void,
        m_arity: 11,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_simpLet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpLet___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2916_ = leanh::lean_box(0);
    v___x_2917_ = l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1;
    v___x_2918_ = l_Lean_Expr_const___override(v___x_2917_, v___x_2916_);
    return v___x_2918_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2921_ = l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3;
    v___x_2922_ = leanh::lean_box(0);
    v___x_2923_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2_once
        ),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2,
    );
    v___x_2924_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2924_, 0, v___x_2923_);
    leanh::lean_ctor_set(v___x_2924_, 1, v___x_2922_);
    leanh::lean_ctor_set(v___x_2924_, 2, v___x_2923_);
    leanh::lean_ctor_set(v___x_2924_, 3, v___x_2923_);
    leanh::lean_ctor_set(v___x_2924_, 4, v___x_2921_);
    leanh::lean_ctor_set(v___x_2924_, 5, v___x_2923_);
    return v___x_2924_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default()
-> *mut leanh::LeanObject {
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2925_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4_once
        ),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4,
    );
    return v___x_2925_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult()
-> *mut leanh::LeanObject {
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2926_ = l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default;
    return v___x_2926_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(
    mut v_k_2927_: *mut leanh::LeanObject,
    mut v_t_2928_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: u8 = 0;
    let mut v___x_2934_: u8 = 0;
    let mut v___x_2936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2928_) == 0 {
                    v_k_2929_ = leanh::lean_ctor_get(v_t_2928_, 1);
                    v_l_2930_ = leanh::lean_ctor_get(v_t_2928_, 3);
                    v_r_2931_ = leanh::lean_ctor_get(v_t_2928_, 4);
                    v___x_2932_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2927_, v_k_2929_);
                    match v___x_2932_ {
                        0 => {
                            v_t_2928_ = v_l_2930_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_2934_ = 1;
                            return v___x_2934_;
                        }
                        _ => {
                            v_t_2928_ = v_r_2931_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2936_ = 0;
                    return v___x_2936_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg___boxed(
    mut v_k_2937_: *mut leanh::LeanObject,
    mut v_t_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2939_: u8 = 0;
    let mut v_r_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2939_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_2937_, v_t_2938_);
    leanh::lean_dec(v_t_2938_);
    leanh::lean_dec(v_k_2937_);
    v_r_2940_ = leanh::lean_box((v_res_2939_) as usize);
    return v_r_2940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(
    mut v_fvarIdToPos_2941_: *mut leanh::LeanObject,
    mut v_as_2942_: *mut leanh::LeanObject,
    mut v_i_2943_: usize,
    mut v_stop_2944_: usize,
    mut v_b_2945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: usize = 0;
    let mut v___x_2949_: usize = 0;
    let mut v___x_2951_: u8 = 0;
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: u8 = 0;
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2951_ = lean_usize_dec_eq(v_i_2943_, v_stop_2944_);
                if v___x_2951_ == 0 {
                    v___x_2952_ = lean_array_uget_borrowed(v_as_2942_, v_i_2943_);
                    v___x_2953_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v___x_2952_, v_fvarIdToPos_2941_);
                    if v___x_2953_ == 0 {
                        v___y_2947_ = v_b_2945_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_2952_);
                        v___x_2954_ = lean_array_push(v_b_2945_, v___x_2952_);
                        v___y_2947_ = v___x_2954_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2945_;
                }
            }
            1 => {
                v___x_2948_ = 1usize;
                v___x_2949_ = lean_usize_add(v_i_2943_, v___x_2948_);
                v_i_2943_ = v___x_2949_;
                v_b_2945_ = v___y_2947_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3___boxed(
    mut v_fvarIdToPos_2955_: *mut leanh::LeanObject,
    mut v_as_2956_: *mut leanh::LeanObject,
    mut v_i_2957_: *mut leanh::LeanObject,
    mut v_stop_2958_: *mut leanh::LeanObject,
    mut v_b_2959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2960_: usize = 0;
    let mut v_stop_boxed_2961_: usize = 0;
    let mut v_res_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2960_ = leanh::lean_unbox_usize(v_i_2957_);
    leanh::lean_dec(v_i_2957_);
    v_stop_boxed_2961_ = leanh::lean_unbox_usize(v_stop_2958_);
    leanh::lean_dec(v_stop_2958_);
    v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_2955_, v_as_2956_, v_i_boxed_2960_, v_stop_boxed_2961_, v_b_2959_);
    leanh::lean_dec_ref(v_as_2956_);
    leanh::lean_dec(v_fvarIdToPos_2955_);
    return v_res_2962_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(
    mut v_msg_2963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2964_ = leanh::lean_unsigned_to_nat(0);
    v___x_2965_ = lean_panic_fn_borrowed(v___x_2964_, v_msg_2963_);
    return v___x_2965_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2969_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__2;
    v___x_2970_ = leanh::lean_unsigned_to_nat(13);
    v___x_2971_ = leanh::lean_unsigned_to_nat(227);
    v___x_2972_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__1;
    v___x_2973_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__0;
    v___x_2974_ = l_mkPanicMessageWithDecl(
        v___x_2973_,
        v___x_2972_,
        v___x_2971_,
        v___x_2970_,
        v___x_2969_,
    );
    return v___x_2974_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(
    mut v_t_2975_: *mut leanh::LeanObject,
    mut v_k_2976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2975_) == 0 {
                    v_k_2977_ = leanh::lean_ctor_get(v_t_2975_, 1);
                    v_v_2978_ = leanh::lean_ctor_get(v_t_2975_, 2);
                    v_l_2979_ = leanh::lean_ctor_get(v_t_2975_, 3);
                    v_r_2980_ = leanh::lean_ctor_get(v_t_2975_, 4);
                    v___x_2981_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2976_, v_k_2977_);
                    match v___x_2981_ {
                        0 => {
                            v_t_2975_ = v_l_2979_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_2978_);
                            return v_v_2978_;
                        }
                        _ => {
                            v_t_2975_ = v_r_2980_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2984_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___closed__3);
                    v___x_2985_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(v___x_2984_);
                    return v___x_2985_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___boxed(
    mut v_t_2986_: *mut leanh::LeanObject,
    mut v_k_2987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2988_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_t_2986_, v_k_2987_);
    leanh::lean_dec(v_k_2987_);
    leanh::lean_dec(v_t_2986_);
    return v_res_2988_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(
    mut v_fvarIdToPos_2989_: *mut leanh::LeanObject,
    mut v_fvarId_u2081_2990_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_2991_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_pos_u2081_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_u2082_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: u8 = 0;
    v_pos_u2081_2992_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_2989_, v_fvarId_u2081_2990_);
    v_pos_u2082_2993_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_2989_, v_fvarId_u2082_2991_);
    v___x_2994_ = lean_nat_dec_lt(v_pos_u2081_2992_, v_pos_u2082_2993_);
    leanh::lean_dec(v_pos_u2082_2993_);
    leanh::lean_dec(v_pos_u2081_2992_);
    return v___x_2994_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed(
    mut v_fvarIdToPos_2995_: *mut leanh::LeanObject,
    mut v_fvarId_u2081_2996_: *mut leanh::LeanObject,
    mut v_fvarId_u2082_2997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2998_: u8 = 0;
    let mut v_r_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2998_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_2995_, v_fvarId_u2081_2996_, v_fvarId_u2082_2997_);
    leanh::lean_dec(v_fvarId_u2082_2997_);
    leanh::lean_dec(v_fvarId_u2081_2996_);
    leanh::lean_dec(v_fvarIdToPos_2995_);
    v_r_2999_ = leanh::lean_box((v_res_2998_) as usize);
    return v_r_2999_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(
    mut v_fvarIdToPos_3000_: *mut leanh::LeanObject,
    mut v_hi_3001_: *mut leanh::LeanObject,
    mut v_pivot_3002_: *mut leanh::LeanObject,
    mut v_as_3003_: *mut leanh::LeanObject,
    mut v_i_3004_: *mut leanh::LeanObject,
    mut v_k_3005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3006_: u8 = 0;
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_u2081_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_u2082_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3006_ = lean_nat_dec_lt(v_k_3005_, v_hi_3001_);
                if v___x_3006_ == 0 {
                    leanh::lean_dec(v_k_3005_);
                    v___x_3007_ = lean_array_fswap(v_as_3003_, v_i_3004_, v_hi_3001_);
                    v___x_3008_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3008_, 0, v_i_3004_);
                    leanh::lean_ctor_set(v___x_3008_, 1, v___x_3007_);
                    return v___x_3008_;
                } else {
                    v___x_3009_ = lean_array_fget_borrowed(v_as_3003_, v_k_3005_);
                    v_pos_u2081_3010_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_3000_, v___x_3009_);
                    v_pos_u2082_3011_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_3000_, v_pivot_3002_);
                    v___x_3012_ = lean_nat_dec_lt(v_pos_u2081_3010_, v_pos_u2082_3011_);
                    leanh::lean_dec(v_pos_u2082_3011_);
                    leanh::lean_dec(v_pos_u2081_3010_);
                    if v___x_3012_ == 0 {
                        v___x_3013_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3014_ = lean_nat_add(v_k_3005_, v___x_3013_);
                        leanh::lean_dec(v_k_3005_);
                        v_k_3005_ = v___x_3014_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3016_ = lean_array_fswap(v_as_3003_, v_i_3004_, v_k_3005_);
                        v___x_3017_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3018_ = lean_nat_add(v_i_3004_, v___x_3017_);
                        leanh::lean_dec(v_i_3004_);
                        v___x_3019_ = lean_nat_add(v_k_3005_, v___x_3017_);
                        leanh::lean_dec(v_k_3005_);
                        v_as_3003_ = v___x_3016_;
                        v_i_3004_ = v___x_3018_;
                        v_k_3005_ = v___x_3019_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg___boxed(
    mut v_fvarIdToPos_3021_: *mut leanh::LeanObject,
    mut v_hi_3022_: *mut leanh::LeanObject,
    mut v_pivot_3023_: *mut leanh::LeanObject,
    mut v_as_3024_: *mut leanh::LeanObject,
    mut v_i_3025_: *mut leanh::LeanObject,
    mut v_k_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_3021_, v_hi_3022_, v_pivot_3023_, v_as_3024_, v_i_3025_, v_k_3026_);
    leanh::lean_dec(v_pivot_3023_);
    leanh::lean_dec(v_hi_3022_);
    leanh::lean_dec(v_fvarIdToPos_3021_);
    return v_res_3027_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(
    mut v_fvarIdToPos_3028_: *mut leanh::LeanObject,
    mut v_n_3029_: *mut leanh::LeanObject,
    mut v_as_3030_: *mut leanh::LeanObject,
    mut v_lo_3031_: *mut leanh::LeanObject,
    mut v_hi_3032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: u8 = 0;
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: u8 = 0;
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: u8 = 0;
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: u8 = 0;
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3044_ = lean_nat_dec_lt(v_lo_3031_, v_hi_3032_);
                if v___x_3044_ == 0 {
                    leanh::lean_dec(v_lo_3031_);
                    return v_as_3030_;
                } else {
                    v___x_3045_ = lean_nat_add(v_lo_3031_, v_hi_3032_);
                    v___x_3046_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_3047_ = lean_nat_shiftr(v___x_3045_, v___x_3046_);
                    leanh::lean_dec(v___x_3045_);
                    v___x_3060_ = lean_array_fget_borrowed(v_as_3030_, v_mid_3047_);
                    v___x_3061_ = lean_array_fget_borrowed(v_as_3030_, v_lo_3031_);
                    v___x_3062_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_3028_, v___x_3060_, v___x_3061_);
                    if v___x_3062_ == 0 {
                        v___y_3055_ = v_as_3030_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3063_ = lean_array_fswap(v_as_3030_, v_lo_3031_, v_mid_3047_);
                        v___y_3055_ = v___x_3063_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3035_ = lean_array_fget(v___y_3034_, v_hi_3032_);
                leanh::lean_inc_n(v_lo_3031_, 2);
                v___x_3036_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_3028_, v_hi_3032_, v_pivot_3035_, v___y_3034_, v_lo_3031_, v_lo_3031_);
                leanh::lean_dec(v_pivot_3035_);
                v_fst_3037_ = leanh::lean_ctor_get(v___x_3036_, 0);
                leanh::lean_inc(v_fst_3037_);
                v_snd_3038_ = leanh::lean_ctor_get(v___x_3036_, 1);
                leanh::lean_inc(v_snd_3038_);
                leanh::lean_dec_ref(v___x_3036_);
                v___x_3039_ = lean_nat_dec_le(v_hi_3032_, v_fst_3037_);
                if v___x_3039_ == 0 {
                    v___x_3040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_3028_, v_n_3029_, v_snd_3038_, v_lo_3031_, v_fst_3037_);
                    v___x_3041_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3042_ = lean_nat_add(v_fst_3037_, v___x_3041_);
                    leanh::lean_dec(v_fst_3037_);
                    v_as_3030_ = v___x_3040_;
                    v_lo_3031_ = v___x_3042_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_3037_);
                    leanh::lean_dec(v_lo_3031_);
                    return v_snd_3038_;
                }
            }
            2 => {
                v___x_3050_ = lean_array_fget_borrowed(v___y_3049_, v_mid_3047_);
                v___x_3051_ = lean_array_fget_borrowed(v___y_3049_, v_hi_3032_);
                v___x_3052_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_3028_, v___x_3050_, v___x_3051_);
                if v___x_3052_ == 0 {
                    leanh::lean_dec(v_mid_3047_);
                    v___y_3034_ = v___y_3049_;
                    state = 1;
                    continue;
                } else {
                    v___x_3053_ = lean_array_fswap(v___y_3049_, v_mid_3047_, v_hi_3032_);
                    leanh::lean_dec(v_mid_3047_);
                    v___y_3034_ = v___x_3053_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3056_ = lean_array_fget_borrowed(v___y_3055_, v_hi_3032_);
                v___x_3057_ = lean_array_fget_borrowed(v___y_3055_, v_lo_3031_);
                v___x_3058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v_fvarIdToPos_3028_, v___x_3056_, v___x_3057_);
                if v___x_3058_ == 0 {
                    v___y_3049_ = v___y_3055_;
                    state = 2;
                    continue;
                } else {
                    v___x_3059_ = lean_array_fswap(v___y_3055_, v_lo_3031_, v_hi_3032_);
                    v___y_3049_ = v___x_3059_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___boxed(
    mut v_fvarIdToPos_3064_: *mut leanh::LeanObject,
    mut v_n_3065_: *mut leanh::LeanObject,
    mut v_as_3066_: *mut leanh::LeanObject,
    mut v_lo_3067_: *mut leanh::LeanObject,
    mut v_hi_3068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3069_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_3064_, v_n_3065_, v_as_3066_, v_lo_3067_, v_hi_3068_);
    leanh::lean_dec(v_hi_3068_);
    leanh::lean_dec(v_n_3065_);
    leanh::lean_dec(v_fvarIdToPos_3064_);
    return v_res_3069_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3070_ = leanh::lean_box(0);
    v___x_3071_ = leanh::lean_unsigned_to_nat(16);
    v___x_3072_ = lean_mk_array(v___x_3071_, v___x_3070_);
    return v___x_3072_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once), _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0);
    v___x_3074_ = leanh::lean_unsigned_to_nat(0);
    v___x_3075_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3075_, 0, v___x_3074_);
    leanh::lean_ctor_set(v___x_3075_, 1, v___x_3073_);
    return v___x_3075_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3078_ =
        l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2;
    v___x_3079_ = leanh::lean_box(1);
    v___x_3080_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1);
    v___x_3081_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3081_, 0, v___x_3080_);
    leanh::lean_ctor_set(v___x_3081_, 1, v___x_3079_);
    leanh::lean_ctor_set(v___x_3081_, 2, v___x_3078_);
    return v___x_3081_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(
    mut v_e_3082_: *mut leanh::LeanObject,
    mut v_fvarIdToPos_3083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: u8 = 0;
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: usize = 0;
    let mut v___x_3108_: usize = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: usize = 0;
    let mut v___x_3111_: usize = 0;
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3092_ = leanh::lean_unsigned_to_nat(0);
                v___x_3100_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2;
                v___x_3101_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once), _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3);
                v_s_3102_ = l_Lean_collectFVars(v___x_3101_, v_e_3082_);
                v_fvarIds_3103_ = leanh::lean_ctor_get(v_s_3102_, 2);
                leanh::lean_inc_ref(v_fvarIds_3103_);
                leanh::lean_dec_ref(v_s_3102_);
                v___x_3104_ = lean_array_get_size(v_fvarIds_3103_);
                v___x_3105_ = lean_nat_dec_lt(v___x_3092_, v___x_3104_);
                if v___x_3105_ == 0 {
                    leanh::lean_dec_ref(v_fvarIds_3103_);
                    v___y_3094_ = v___x_3100_;
                    state = 2;
                    continue;
                } else {
                    v___x_3106_ = lean_nat_dec_le(v___x_3104_, v___x_3104_);
                    if v___x_3106_ == 0 {
                        if v___x_3105_ == 0 {
                            leanh::lean_dec_ref(v_fvarIds_3103_);
                            v___y_3094_ = v___x_3100_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3107_ = 0usize;
                            v___x_3108_ = lean_usize_of_nat(v___x_3104_);
                            v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_3083_, v_fvarIds_3103_, v___x_3107_, v___x_3108_, v___x_3100_);
                            leanh::lean_dec_ref(v_fvarIds_3103_);
                            v___y_3094_ = v___x_3109_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_3110_ = 0usize;
                        v___x_3111_ = lean_usize_of_nat(v___x_3104_);
                        v___x_3112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_3083_, v_fvarIds_3103_, v___x_3110_, v___x_3111_, v___x_3100_);
                        leanh::lean_dec_ref(v_fvarIds_3103_);
                        v___y_3094_ = v___x_3112_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3089_ = lean_nat_dec_le(v___y_3088_, v___y_3087_);
                if v___x_3089_ == 0 {
                    leanh::lean_dec(v___y_3087_);
                    leanh::lean_inc(v___y_3088_);
                    v___x_3090_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_3083_, v___y_3085_, v___y_3086_, v___y_3088_, v___y_3088_);
                    leanh::lean_dec(v___y_3088_);
                    leanh::lean_dec(v___y_3085_);
                    return v___x_3090_;
                } else {
                    v___x_3091_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_3083_, v___y_3085_, v___y_3086_, v___y_3088_, v___y_3087_);
                    leanh::lean_dec(v___y_3087_);
                    leanh::lean_dec(v___y_3085_);
                    return v___x_3091_;
                }
            }
            2 => {
                v___x_3095_ = lean_array_get_size(v___y_3094_);
                v___x_3096_ = lean_nat_dec_eq(v___x_3095_, v___x_3092_);
                if v___x_3096_ == 0 {
                    v___x_3097_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3098_ = lean_nat_sub(v___x_3095_, v___x_3097_);
                    v___x_3099_ = lean_nat_dec_le(v___x_3092_, v___x_3098_);
                    if v___x_3099_ == 0 {
                        leanh::lean_inc(v___x_3098_);
                        v___y_3085_ = v___x_3095_;
                        v___y_3086_ = v___y_3094_;
                        v___y_3087_ = v___x_3098_;
                        v___y_3088_ = v___x_3098_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3085_ = v___x_3095_;
                        v___y_3086_ = v___y_3094_;
                        v___y_3087_ = v___x_3098_;
                        v___y_3088_ = v___x_3092_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_3094_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___boxed(
    mut v_e_3113_: *mut leanh::LeanObject,
    mut v_fvarIdToPos_3114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3115_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(
        v_e_3113_,
        v_fvarIdToPos_3114_,
    );
    leanh::lean_dec(v_fvarIdToPos_3114_);
    return v_res_3115_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(
    mut v_00_u03b2_3116_: *mut leanh::LeanObject,
    mut v_k_3117_: *mut leanh::LeanObject,
    mut v_t_3118_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3119_: u8 = 0;
    v___x_3119_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_3117_, v_t_3118_);
    return v___x_3119_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(
    mut v_00_u03b2_3120_: *mut leanh::LeanObject,
    mut v_k_3121_: *mut leanh::LeanObject,
    mut v_t_3122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3123_: u8 = 0;
    let mut v_r_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3123_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(v_00_u03b2_3120_, v_k_3121_, v_t_3122_);
    leanh::lean_dec(v_t_3122_);
    leanh::lean_dec(v_k_3121_);
    v_r_3124_ = leanh::lean_box((v_res_3123_) as usize);
    return v_r_3124_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(
    mut v_fvarIdToPos_3125_: *mut leanh::LeanObject,
    mut v_n_3126_: *mut leanh::LeanObject,
    mut v_as_3127_: *mut leanh::LeanObject,
    mut v_lo_3128_: *mut leanh::LeanObject,
    mut v_hi_3129_: *mut leanh::LeanObject,
    mut v_w_3130_: *mut leanh::LeanObject,
    mut v_hlo_3131_: *mut leanh::LeanObject,
    mut v_hhi_3132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3133_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_3125_, v_n_3126_, v_as_3127_, v_lo_3128_, v_hi_3129_);
    return v___x_3133_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(
    mut v_fvarIdToPos_3134_: *mut leanh::LeanObject,
    mut v_n_3135_: *mut leanh::LeanObject,
    mut v_as_3136_: *mut leanh::LeanObject,
    mut v_lo_3137_: *mut leanh::LeanObject,
    mut v_hi_3138_: *mut leanh::LeanObject,
    mut v_w_3139_: *mut leanh::LeanObject,
    mut v_hlo_3140_: *mut leanh::LeanObject,
    mut v_hhi_3141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3142_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(v_fvarIdToPos_3134_, v_n_3135_, v_as_3136_, v_lo_3137_, v_hi_3138_, v_w_3139_, v_hlo_3140_, v_hhi_3141_);
    leanh::lean_dec(v_hi_3138_);
    leanh::lean_dec(v_n_3135_);
    leanh::lean_dec(v_fvarIdToPos_3134_);
    return v_res_3142_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(
    mut v_fvarIdToPos_3143_: *mut leanh::LeanObject,
    mut v_n_3144_: *mut leanh::LeanObject,
    mut v_lo_3145_: *mut leanh::LeanObject,
    mut v_hi_3146_: *mut leanh::LeanObject,
    mut v_hhi_3147_: *mut leanh::LeanObject,
    mut v_pivot_3148_: *mut leanh::LeanObject,
    mut v_as_3149_: *mut leanh::LeanObject,
    mut v_i_3150_: *mut leanh::LeanObject,
    mut v_k_3151_: *mut leanh::LeanObject,
    mut v_ilo_3152_: *mut leanh::LeanObject,
    mut v_ik_3153_: *mut leanh::LeanObject,
    mut v_w_3154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3155_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___redArg(v_fvarIdToPos_3143_, v_hi_3146_, v_pivot_3148_, v_as_3149_, v_i_3150_, v_k_3151_);
    return v___x_3155_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3___boxed(
    mut v_fvarIdToPos_3156_: *mut leanh::LeanObject,
    mut v_n_3157_: *mut leanh::LeanObject,
    mut v_lo_3158_: *mut leanh::LeanObject,
    mut v_hi_3159_: *mut leanh::LeanObject,
    mut v_hhi_3160_: *mut leanh::LeanObject,
    mut v_pivot_3161_: *mut leanh::LeanObject,
    mut v_as_3162_: *mut leanh::LeanObject,
    mut v_i_3163_: *mut leanh::LeanObject,
    mut v_k_3164_: *mut leanh::LeanObject,
    mut v_ilo_3165_: *mut leanh::LeanObject,
    mut v_ik_3166_: *mut leanh::LeanObject,
    mut v_w_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3168_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2_spec__3(v_fvarIdToPos_3156_, v_n_3157_, v_lo_3158_, v_hi_3159_, v_hhi_3160_, v_pivot_3161_, v_as_3162_, v_i_3163_, v_k_3164_, v_ilo_3165_, v_ik_3166_, v_w_3167_);
    leanh::lean_dec(v_pivot_3161_);
    leanh::lean_dec(v_hi_3159_);
    leanh::lean_dec(v_lo_3158_);
    leanh::lean_dec(v_n_3157_);
    leanh::lean_dec(v_fvarIdToPos_3156_);
    return v_res_3168_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(
    mut v_x_3169_: *mut leanh::LeanObject,
    mut v_bi_3170_: u8,
    mut v_t_3171_: *mut leanh::LeanObject,
    mut v_b_3172_: *mut leanh::LeanObject,
    mut v___y_3173_: *mut leanh::LeanObject,
    mut v___y_3174_: *mut leanh::LeanObject,
    mut v___y_3175_: *mut leanh::LeanObject,
    mut v___y_3176_: *mut leanh::LeanObject,
    mut v___y_3177_: *mut leanh::LeanObject,
    mut v___y_3178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3185_: u8 = 0;
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut v_a_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3199_: u8 = 0;
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3184_ = lean_st_ref_get(v___y_3174_);
                v_debug_3185_ = leanh::lean_ctor_get_uint8(
                    v___x_3184_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                leanh::lean_dec(v___x_3184_);
                if v_debug_3185_ == 0 {
                    v___y_3181_ = v___y_3174_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_t_3171_);
                    v___x_3186_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_t_3171_,
                        v___y_3173_,
                        v___y_3174_,
                        v___y_3175_,
                        v___y_3176_,
                        v___y_3177_,
                        v___y_3178_,
                    );
                    if leanh::lean_obj_tag(v___x_3186_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3186_, 1);
                        leanh::lean_inc_ref(v_b_3172_);
                        v___x_3187_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_b_3172_,
                            v___y_3173_,
                            v___y_3174_,
                            v___y_3175_,
                            v___y_3176_,
                            v___y_3177_,
                            v___y_3178_,
                        );
                        if leanh::lean_obj_tag(v___x_3187_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3187_, 1);
                            v___y_3181_ = v___y_3174_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_3172_);
                            leanh::lean_dec_ref(v_t_3171_);
                            leanh::lean_dec(v_x_3169_);
                            v_a_3188_ = leanh::lean_ctor_get(v___x_3187_, 0);
                            v_isSharedCheck_3195_ =
                                (!leanh::lean_is_exclusive(v___x_3187_)) as u8;
                            if v_isSharedCheck_3195_ == 0 {
                                v___x_3190_ = v___x_3187_;
                                v_isShared_3191_ = v_isSharedCheck_3195_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3188_);
                                leanh::lean_dec(v___x_3187_);
                                v___x_3190_ = leanh::lean_box(0);
                                v_isShared_3191_ = v_isSharedCheck_3195_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_3172_);
                        leanh::lean_dec_ref(v_t_3171_);
                        leanh::lean_dec(v_x_3169_);
                        v_a_3196_ = leanh::lean_ctor_get(v___x_3186_, 0);
                        v_isSharedCheck_3203_ =
                            (!leanh::lean_is_exclusive(v___x_3186_)) as u8;
                        if v_isSharedCheck_3203_ == 0 {
                            v___x_3198_ = v___x_3186_;
                            v_isShared_3199_ = v_isSharedCheck_3203_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3196_);
                            leanh::lean_dec(v___x_3186_);
                            v___x_3198_ = leanh::lean_box(0);
                            v_isShared_3199_ = v_isSharedCheck_3203_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3182_ =
                    l_Lean_Expr_forallE___override(v_x_3169_, v_t_3171_, v_b_3172_, v_bi_3170_);
                v___x_3183_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3182_, v___y_3181_);
                return v___x_3183_;
            }
            2 => {
                if v_isShared_3191_ == 0 {
                    v___x_3193_ = v___x_3190_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3194_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
                    v___x_3193_ = v_reuseFailAlloc_3194_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3193_;
            }
            4 => {
                if v_isShared_3199_ == 0 {
                    v___x_3201_ = v___x_3198_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
                    v___x_3201_ = v_reuseFailAlloc_3202_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(
    mut v_x_3204_: *mut leanh::LeanObject,
    mut v_bi_3205_: *mut leanh::LeanObject,
    mut v_t_3206_: *mut leanh::LeanObject,
    mut v_b_3207_: *mut leanh::LeanObject,
    mut v___y_3208_: *mut leanh::LeanObject,
    mut v___y_3209_: *mut leanh::LeanObject,
    mut v___y_3210_: *mut leanh::LeanObject,
    mut v___y_3211_: *mut leanh::LeanObject,
    mut v___y_3212_: *mut leanh::LeanObject,
    mut v___y_3213_: *mut leanh::LeanObject,
    mut v___y_3214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3215_: u8 = 0;
    let mut v_res_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3215_ = (leanh::lean_unbox(v_bi_3205_) as u8);
    v_res_3216_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_3204_, v_bi_boxed_3215_, v_t_3206_, v_b_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
    leanh::lean_dec(v___y_3213_);
    leanh::lean_dec_ref(v___y_3212_);
    leanh::lean_dec(v___y_3211_);
    leanh::lean_dec_ref(v___y_3210_);
    leanh::lean_dec(v___y_3209_);
    leanh::lean_dec_ref(v___y_3208_);
    return v_res_3216_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(
    mut v_00_u03b1s_3220_: *mut leanh::LeanObject,
    mut v_i_3221_: *mut leanh::LeanObject,
    mut v_00_u03b2_3222_: *mut leanh::LeanObject,
    mut v_a_3223_: *mut leanh::LeanObject,
    mut v_a_3224_: *mut leanh::LeanObject,
    mut v_a_3225_: *mut leanh::LeanObject,
    mut v_a_3226_: *mut leanh::LeanObject,
    mut v_a_3227_: *mut leanh::LeanObject,
    mut v_a_3228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3231_: u8 = 0;
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u8 = 0;
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3230_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3231_ = lean_nat_dec_eq(v_i_3221_, v_zero_3230_);
                if v_isZero_3231_ == 1 {
                    leanh::lean_dec(v_i_3221_);
                    v___x_3232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3232_, 0, v_00_u03b2_3222_);
                    return v___x_3232_;
                } else {
                    v_one_3233_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3234_ = lean_nat_sub(v_i_3221_, v_one_3233_);
                    leanh::lean_dec(v_i_3221_);
                    v___x_3235_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1;
                    v___x_3236_ = 0;
                    v___x_3237_ = lean_array_fget_borrowed(v_00_u03b1s_3220_, v_n_3234_);
                    leanh::lean_inc(v___x_3237_);
                    v___x_3238_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v___x_3235_, v___x_3236_, v___x_3237_, v_00_u03b2_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
                    if leanh::lean_obj_tag(v___x_3238_) == 0 {
                        v_a_3239_ = leanh::lean_ctor_get(v___x_3238_, 0);
                        leanh::lean_inc(v_a_3239_);
                        leanh::lean_dec_ref_known(v___x_3238_, 1);
                        v_i_3221_ = v_n_3234_;
                        v_00_u03b2_3222_ = v_a_3239_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_n_3234_);
                        return v___x_3238_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(
    mut v_00_u03b1s_3241_: *mut leanh::LeanObject,
    mut v_i_3242_: *mut leanh::LeanObject,
    mut v_00_u03b2_3243_: *mut leanh::LeanObject,
    mut v_a_3244_: *mut leanh::LeanObject,
    mut v_a_3245_: *mut leanh::LeanObject,
    mut v_a_3246_: *mut leanh::LeanObject,
    mut v_a_3247_: *mut leanh::LeanObject,
    mut v_a_3248_: *mut leanh::LeanObject,
    mut v_a_3249_: *mut leanh::LeanObject,
    mut v_a_3250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3251_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(
        v_00_u03b1s_3241_,
        v_i_3242_,
        v_00_u03b2_3243_,
        v_a_3244_,
        v_a_3245_,
        v_a_3246_,
        v_a_3247_,
        v_a_3248_,
        v_a_3249_,
    );
    leanh::lean_dec(v_a_3249_);
    leanh::lean_dec_ref(v_a_3248_);
    leanh::lean_dec(v_a_3247_);
    leanh::lean_dec_ref(v_a_3246_);
    leanh::lean_dec(v_a_3245_);
    leanh::lean_dec_ref(v_a_3244_);
    leanh::lean_dec_ref(v_00_u03b1s_3241_);
    return v_res_3251_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(
    mut v_00_u03b1s_3252_: *mut leanh::LeanObject,
    mut v_i_3253_: *mut leanh::LeanObject,
    mut v_00_u03b2_3254_: *mut leanh::LeanObject,
    mut v_h_3255_: *mut leanh::LeanObject,
    mut v_a_3256_: *mut leanh::LeanObject,
    mut v_a_3257_: *mut leanh::LeanObject,
    mut v_a_3258_: *mut leanh::LeanObject,
    mut v_a_3259_: *mut leanh::LeanObject,
    mut v_a_3260_: *mut leanh::LeanObject,
    mut v_a_3261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3263_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(
        v_00_u03b1s_3252_,
        v_i_3253_,
        v_00_u03b2_3254_,
        v_a_3256_,
        v_a_3257_,
        v_a_3258_,
        v_a_3259_,
        v_a_3260_,
        v_a_3261_,
    );
    return v___x_3263_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(
    mut v_00_u03b1s_3264_: *mut leanh::LeanObject,
    mut v_i_3265_: *mut leanh::LeanObject,
    mut v_00_u03b2_3266_: *mut leanh::LeanObject,
    mut v_h_3267_: *mut leanh::LeanObject,
    mut v_a_3268_: *mut leanh::LeanObject,
    mut v_a_3269_: *mut leanh::LeanObject,
    mut v_a_3270_: *mut leanh::LeanObject,
    mut v_a_3271_: *mut leanh::LeanObject,
    mut v_a_3272_: *mut leanh::LeanObject,
    mut v_a_3273_: *mut leanh::LeanObject,
    mut v_a_3274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3275_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(
        v_00_u03b1s_3264_,
        v_i_3265_,
        v_00_u03b2_3266_,
        v_h_3267_,
        v_a_3268_,
        v_a_3269_,
        v_a_3270_,
        v_a_3271_,
        v_a_3272_,
        v_a_3273_,
    );
    leanh::lean_dec(v_a_3273_);
    leanh::lean_dec_ref(v_a_3272_);
    leanh::lean_dec(v_a_3271_);
    leanh::lean_dec_ref(v_a_3270_);
    leanh::lean_dec(v_a_3269_);
    leanh::lean_dec_ref(v_a_3268_);
    leanh::lean_dec_ref(v_00_u03b1s_3264_);
    return v_res_3275_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(
    mut v_00_u03b1s_3276_: *mut leanh::LeanObject,
    mut v_00_u03b2_3277_: *mut leanh::LeanObject,
    mut v_a_3278_: *mut leanh::LeanObject,
    mut v_a_3279_: *mut leanh::LeanObject,
    mut v_a_3280_: *mut leanh::LeanObject,
    mut v_a_3281_: *mut leanh::LeanObject,
    mut v_a_3282_: *mut leanh::LeanObject,
    mut v_a_3283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3285_ = lean_array_get_size(v_00_u03b1s_3276_);
    v___x_3286_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(
        v_00_u03b1s_3276_,
        v___x_3285_,
        v_00_u03b2_3277_,
        v_a_3278_,
        v_a_3279_,
        v_a_3280_,
        v_a_3281_,
        v_a_3282_,
        v_a_3283_,
    );
    return v___x_3286_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(
    mut v_00_u03b1s_3287_: *mut leanh::LeanObject,
    mut v_00_u03b2_3288_: *mut leanh::LeanObject,
    mut v_a_3289_: *mut leanh::LeanObject,
    mut v_a_3290_: *mut leanh::LeanObject,
    mut v_a_3291_: *mut leanh::LeanObject,
    mut v_a_3292_: *mut leanh::LeanObject,
    mut v_a_3293_: *mut leanh::LeanObject,
    mut v_a_3294_: *mut leanh::LeanObject,
    mut v_a_3295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3296_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(
        v_00_u03b1s_3287_,
        v_00_u03b2_3288_,
        v_a_3289_,
        v_a_3290_,
        v_a_3291_,
        v_a_3292_,
        v_a_3293_,
        v_a_3294_,
    );
    leanh::lean_dec(v_a_3294_);
    leanh::lean_dec_ref(v_a_3293_);
    leanh::lean_dec(v_a_3292_);
    leanh::lean_dec_ref(v_a_3291_);
    leanh::lean_dec(v_a_3290_);
    leanh::lean_dec_ref(v_a_3289_);
    leanh::lean_dec_ref(v_00_u03b1s_3287_);
    return v_res_3296_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(
    mut v_fvarIdToPos_3297_: *mut leanh::LeanObject,
    mut v_subst_3298_: *mut leanh::LeanObject,
    mut v_sz_3299_: usize,
    mut v_i_3300_: usize,
    mut v_bs_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3302_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: usize = 0;
    let mut v___x_3310_: usize = 0;
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3302_ = lean_usize_dec_lt(v_i_3300_, v_sz_3299_);
                if v___x_3302_ == 0 {
                    return v_bs_3301_;
                } else {
                    v___x_3303_ = l_Lean_instInhabitedExpr;
                    v_v_3304_ = lean_array_uget(v_bs_3301_, v_i_3300_);
                    v___x_3305_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3306_ = lean_array_uset(v_bs_3301_, v_i_3300_, v___x_3305_);
                    v___x_3307_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_fvarIdToPos_3297_, v_v_3304_);
                    leanh::lean_dec(v_v_3304_);
                    v___x_3308_ = lean_array_get_borrowed(v___x_3303_, v_subst_3298_, v___x_3307_);
                    leanh::lean_dec(v___x_3307_);
                    v___x_3309_ = 1usize;
                    v___x_3310_ = lean_usize_add(v_i_3300_, v___x_3309_);
                    leanh::lean_inc(v___x_3308_);
                    v___x_3311_ = lean_array_uset(v_bs_x27_3306_, v_i_3300_, v___x_3308_);
                    v_i_3300_ = v___x_3310_;
                    v_bs_3301_ = v___x_3311_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(
    mut v_fvarIdToPos_3313_: *mut leanh::LeanObject,
    mut v_subst_3314_: *mut leanh::LeanObject,
    mut v_sz_3315_: *mut leanh::LeanObject,
    mut v_i_3316_: *mut leanh::LeanObject,
    mut v_bs_3317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3318_: usize = 0;
    let mut v_i_boxed_3319_: usize = 0;
    let mut v_res_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3318_ = leanh::lean_unbox_usize(v_sz_3315_);
    leanh::lean_dec(v_sz_3315_);
    v_i_boxed_3319_ = leanh::lean_unbox_usize(v_i_3316_);
    leanh::lean_dec(v_i_3316_);
    v_res_3320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_3313_, v_subst_3314_, v_sz_boxed_3318_, v_i_boxed_3319_, v_bs_3317_);
    leanh::lean_dec_ref(v_subst_3314_);
    leanh::lean_dec(v_fvarIdToPos_3313_);
    return v_res_3320_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(
    mut v_sz_3321_: usize,
    mut v_i_3322_: usize,
    mut v_bs_3323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3324_: u8 = 0;
    let mut v_v_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: usize = 0;
    let mut v___x_3330_: usize = 0;
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3324_ = lean_usize_dec_lt(v_i_3322_, v_sz_3321_);
                if v___x_3324_ == 0 {
                    return v_bs_3323_;
                } else {
                    v_v_3325_ = lean_array_uget(v_bs_3323_, v_i_3322_);
                    v___x_3326_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3327_ = lean_array_uset(v_bs_3323_, v_i_3322_, v___x_3326_);
                    v___x_3328_ = l_Lean_mkFVar(v_v_3325_);
                    v___x_3329_ = 1usize;
                    v___x_3330_ = lean_usize_add(v_i_3322_, v___x_3329_);
                    v___x_3331_ = lean_array_uset(v_bs_x27_3327_, v_i_3322_, v___x_3328_);
                    v_i_3322_ = v___x_3330_;
                    v_bs_3323_ = v___x_3331_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(
    mut v_sz_3333_: *mut leanh::LeanObject,
    mut v_i_3334_: *mut leanh::LeanObject,
    mut v_bs_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3336_: usize = 0;
    let mut v_i_boxed_3337_: usize = 0;
    let mut v_res_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3336_ = leanh::lean_unbox_usize(v_sz_3333_);
    leanh::lean_dec(v_sz_3333_);
    v_i_boxed_3337_ = leanh::lean_unbox_usize(v_i_3334_);
    leanh::lean_dec(v_i_3334_);
    v_res_3338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_3336_, v_i_boxed_3337_, v_bs_3335_);
    return v_res_3338_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(
    mut v_k_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
    mut v___y_3341_: *mut leanh::LeanObject,
    mut v_b_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
    mut v___y_3344_: *mut leanh::LeanObject,
    mut v___y_3345_: *mut leanh::LeanObject,
    mut v___y_3346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3346_);
    leanh::lean_inc_ref(v___y_3345_);
    leanh::lean_inc(v___y_3344_);
    leanh::lean_inc_ref(v___y_3343_);
    leanh::lean_inc(v___y_3341_);
    leanh::lean_inc_ref(v___y_3340_);
    v___x_3348_ = leanh::lean_apply_8(
        v_k_3339_,
        v_b_3342_,
        v___y_3340_,
        v___y_3341_,
        v___y_3343_,
        v___y_3344_,
        v___y_3345_,
        v___y_3346_,
        leanh::lean_box(0),
    );
    return v___x_3348_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(
    mut v_k_3349_: *mut leanh::LeanObject,
    mut v___y_3350_: *mut leanh::LeanObject,
    mut v___y_3351_: *mut leanh::LeanObject,
    mut v_b_3352_: *mut leanh::LeanObject,
    mut v___y_3353_: *mut leanh::LeanObject,
    mut v___y_3354_: *mut leanh::LeanObject,
    mut v___y_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
    mut v___y_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3358_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_3349_, v___y_3350_, v___y_3351_, v_b_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
    leanh::lean_dec(v___y_3356_);
    leanh::lean_dec_ref(v___y_3355_);
    leanh::lean_dec(v___y_3354_);
    leanh::lean_dec_ref(v___y_3353_);
    leanh::lean_dec(v___y_3351_);
    leanh::lean_dec_ref(v___y_3350_);
    return v_res_3358_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(
    mut v_name_3359_: *mut leanh::LeanObject,
    mut v_bi_3360_: u8,
    mut v_type_3361_: *mut leanh::LeanObject,
    mut v_k_3362_: *mut leanh::LeanObject,
    mut v_kind_3363_: u8,
    mut v___y_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
    mut v___y_3366_: *mut leanh::LeanObject,
    mut v___y_3367_: *mut leanh::LeanObject,
    mut v___y_3368_: *mut leanh::LeanObject,
    mut v___y_3369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3376_: u8 = 0;
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3365_);
                leanh::lean_inc_ref(v___y_3364_);
                v___f_3371_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                leanh::lean_closure_set(v___f_3371_, 0, v_k_3362_);
                leanh::lean_closure_set(v___f_3371_, 1, v___y_3364_);
                leanh::lean_closure_set(v___f_3371_, 2, v___y_3365_);
                v___x_3372_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_3359_,
                    v_bi_3360_,
                    v_type_3361_,
                    v___f_3371_,
                    v_kind_3363_,
                    v___y_3366_,
                    v___y_3367_,
                    v___y_3368_,
                    v___y_3369_,
                );
                if leanh::lean_obj_tag(v___x_3372_) == 0 {
                    return v___x_3372_;
                } else {
                    v_a_3373_ = leanh::lean_ctor_get(v___x_3372_, 0);
                    v_isSharedCheck_3380_ = (!leanh::lean_is_exclusive(v___x_3372_)) as u8;
                    if v_isSharedCheck_3380_ == 0 {
                        v___x_3375_ = v___x_3372_;
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3373_);
                        leanh::lean_dec(v___x_3372_);
                        v___x_3375_ = leanh::lean_box(0);
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3376_ == 0 {
                    v___x_3378_ = v___x_3375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3379_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
                    v___x_3378_ = v_reuseFailAlloc_3379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(
    mut v_name_3381_: *mut leanh::LeanObject,
    mut v_bi_3382_: *mut leanh::LeanObject,
    mut v_type_3383_: *mut leanh::LeanObject,
    mut v_k_3384_: *mut leanh::LeanObject,
    mut v_kind_3385_: *mut leanh::LeanObject,
    mut v___y_3386_: *mut leanh::LeanObject,
    mut v___y_3387_: *mut leanh::LeanObject,
    mut v___y_3388_: *mut leanh::LeanObject,
    mut v___y_3389_: *mut leanh::LeanObject,
    mut v___y_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3393_: u8 = 0;
    let mut v_kind_boxed_3394_: u8 = 0;
    let mut v_res_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3393_ = (leanh::lean_unbox(v_bi_3382_) as u8);
    v_kind_boxed_3394_ = (leanh::lean_unbox(v_kind_3385_) as u8);
    v_res_3395_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_3381_, v_bi_boxed_3393_, v_type_3383_, v_k_3384_, v_kind_boxed_3394_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    leanh::lean_dec(v___y_3391_);
    leanh::lean_dec_ref(v___y_3390_);
    leanh::lean_dec(v___y_3389_);
    leanh::lean_dec_ref(v___y_3388_);
    leanh::lean_dec(v___y_3387_);
    leanh::lean_dec_ref(v___y_3386_);
    return v_res_3395_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(
    mut v_name_3396_: *mut leanh::LeanObject,
    mut v_type_3397_: *mut leanh::LeanObject,
    mut v_k_3398_: *mut leanh::LeanObject,
    mut v___y_3399_: *mut leanh::LeanObject,
    mut v___y_3400_: *mut leanh::LeanObject,
    mut v___y_3401_: *mut leanh::LeanObject,
    mut v___y_3402_: *mut leanh::LeanObject,
    mut v___y_3403_: *mut leanh::LeanObject,
    mut v___y_3404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3406_: u8 = 0;
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3406_ = 0;
    v___x_3407_ = 0;
    v___x_3408_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_3396_, v___x_3406_, v_type_3397_, v_k_3398_, v___x_3407_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
    return v___x_3408_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(
    mut v_name_3409_: *mut leanh::LeanObject,
    mut v_type_3410_: *mut leanh::LeanObject,
    mut v_k_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
    mut v___y_3413_: *mut leanh::LeanObject,
    mut v___y_3414_: *mut leanh::LeanObject,
    mut v___y_3415_: *mut leanh::LeanObject,
    mut v___y_3416_: *mut leanh::LeanObject,
    mut v___y_3417_: *mut leanh::LeanObject,
    mut v___y_3418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3419_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_3409_, v_type_3410_, v_k_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
    leanh::lean_dec(v___y_3417_);
    leanh::lean_dec_ref(v___y_3416_);
    leanh::lean_dec(v___y_3415_);
    leanh::lean_dec_ref(v___y_3414_);
    leanh::lean_dec(v___y_3413_);
    leanh::lean_dec_ref(v___y_3412_);
    return v_res_3419_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(
    mut v_t_3420_: *mut leanh::LeanObject,
    mut v_k_3421_: *mut leanh::LeanObject,
    mut v_fallback_3422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3420_) == 0 {
                    v_k_3423_ = leanh::lean_ctor_get(v_t_3420_, 1);
                    v_v_3424_ = leanh::lean_ctor_get(v_t_3420_, 2);
                    v_l_3425_ = leanh::lean_ctor_get(v_t_3420_, 3);
                    v_r_3426_ = leanh::lean_ctor_get(v_t_3420_, 4);
                    v___x_3427_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3421_, v_k_3423_);
                    match v___x_3427_ {
                        0 => {
                            v_t_3420_ = v_l_3425_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_3424_);
                            return v_v_3424_;
                        }
                        _ => {
                            v_t_3420_ = v_r_3426_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_fallback_3422_);
                    return v_fallback_3422_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(
    mut v_t_3430_: *mut leanh::LeanObject,
    mut v_k_3431_: *mut leanh::LeanObject,
    mut v_fallback_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3433_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_3430_, v_k_3431_, v_fallback_3432_);
    leanh::lean_dec(v_fallback_3432_);
    leanh::lean_dec(v_k_3431_);
    leanh::lean_dec(v_t_3430_);
    return v_res_3433_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(
    mut v_fvarIdToPos_3434_: *mut leanh::LeanObject,
    mut v_sz_3435_: usize,
    mut v_i_3436_: usize,
    mut v_bs_3437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3438_: u8 = 0;
    let mut v_v_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: usize = 0;
    let mut v___x_3444_: usize = 0;
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3438_ = lean_usize_dec_lt(v_i_3436_, v_sz_3435_);
                if v___x_3438_ == 0 {
                    return v_bs_3437_;
                } else {
                    v_v_3439_ = lean_array_uget(v_bs_3437_, v_i_3436_);
                    v___x_3440_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3441_ = lean_array_uset(v_bs_3437_, v_i_3436_, v___x_3440_);
                    v___x_3442_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_3434_, v_v_3439_, v___x_3440_);
                    leanh::lean_dec(v_v_3439_);
                    v___x_3443_ = 1usize;
                    v___x_3444_ = lean_usize_add(v_i_3436_, v___x_3443_);
                    v___x_3445_ = lean_array_uset(v_bs_x27_3441_, v_i_3436_, v___x_3442_);
                    v_i_3436_ = v___x_3444_;
                    v_bs_3437_ = v___x_3445_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(
    mut v_fvarIdToPos_3447_: *mut leanh::LeanObject,
    mut v_sz_3448_: *mut leanh::LeanObject,
    mut v_i_3449_: *mut leanh::LeanObject,
    mut v_bs_3450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3451_: usize = 0;
    let mut v_i_boxed_3452_: usize = 0;
    let mut v_res_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3451_ = leanh::lean_unbox_usize(v_sz_3448_);
    leanh::lean_dec(v_sz_3448_);
    v_i_boxed_3452_ = leanh::lean_unbox_usize(v_i_3449_);
    leanh::lean_dec(v_i_3449_);
    v_res_3453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_3447_, v_sz_boxed_3451_, v_i_boxed_3452_, v_bs_3450_);
    leanh::lean_dec(v_fvarIdToPos_3447_);
    return v_res_3453_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarIdToPos_3463_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_subst_3464_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_3465_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_3466_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_fvarIds_3467_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_x_3468_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_xs_3469_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_xs_x27_3470_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_args_3471_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_3472_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_types_3473_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_3474_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_varDeps_3475_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_varPos_3476_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_haveExpr_3477_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_body_3478_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_x_x27_3479_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_3480_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_3481_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_3482_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_3483_: *mut leanh::LeanObject = *_args.add(20);
    let mut v___y_3484_: *mut leanh::LeanObject = *_args.add(21);
    let mut v___y_3485_: *mut leanh::LeanObject = *_args.add(22);
    let mut v___y_3486_: *mut leanh::LeanObject = *_args.add(23);
    let mut v_sz_boxed_3487_: usize = 0;
    let mut v___x_6520__boxed_3488_: usize = 0;
    let mut v_res_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3487_ = leanh::lean_unbox_usize(v_sz_3465_);
    leanh::lean_dec(v_sz_3465_);
    v___x_6520__boxed_3488_ = leanh::lean_unbox_usize(v___x_3466_);
    leanh::lean_dec(v___x_3466_);
    v_res_3489_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(
        v_fvarIdToPos_3463_,
        v_subst_3464_,
        v_sz_boxed_3487_,
        v___x_6520__boxed_3488_,
        v_fvarIds_3467_,
        v_x_3468_,
        v_xs_3469_,
        v_xs_x27_3470_,
        v_args_3471_,
        v_a_3472_,
        v_types_3473_,
        v_a_3474_,
        v_varDeps_3475_,
        v_varPos_3476_,
        v_haveExpr_3477_,
        v_body_3478_,
        v_x_x27_3479_,
        v___y_3480_,
        v___y_3481_,
        v___y_3482_,
        v___y_3483_,
        v___y_3484_,
        v___y_3485_,
    );
    leanh::lean_dec(v___y_3485_);
    leanh::lean_dec_ref(v___y_3484_);
    leanh::lean_dec(v___y_3483_);
    leanh::lean_dec_ref(v___y_3482_);
    leanh::lean_dec(v___y_3481_);
    leanh::lean_dec_ref(v___y_3480_);
    return v_res_3489_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(
    mut v_v_3490_: *mut leanh::LeanObject,
    mut v_fvarIdToPos_3491_: *mut leanh::LeanObject,
    mut v_nondep_3492_: u8,
    mut v_t_3493_: *mut leanh::LeanObject,
    mut v_subst_3494_: *mut leanh::LeanObject,
    mut v_xs_3495_: *mut leanh::LeanObject,
    mut v_xs_x27_3496_: *mut leanh::LeanObject,
    mut v_args_3497_: *mut leanh::LeanObject,
    mut v_types_3498_: *mut leanh::LeanObject,
    mut v_varDeps_3499_: *mut leanh::LeanObject,
    mut v_haveExpr_3500_: *mut leanh::LeanObject,
    mut v_body_3501_: *mut leanh::LeanObject,
    mut v_declName_3502_: *mut leanh::LeanObject,
    mut v_x_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
    mut v___y_3505_: *mut leanh::LeanObject,
    mut v___y_3506_: *mut leanh::LeanObject,
    mut v___y_3507_: *mut leanh::LeanObject,
    mut v___y_3508_: *mut leanh::LeanObject,
    mut v___y_3509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarIds_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3512_: usize = 0;
    let mut v___x_3513_: usize = 0;
    let mut v_varPos_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: u8 = 0;
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3535_: u8 = 0;
    let mut v_a_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut v_a_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3547_: u8 = 0;
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_v_3490_);
                v_fvarIds_3511_ =
                    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(
                        v_v_3490_,
                        v_fvarIdToPos_3491_,
                    );
                v_sz_3512_ = lean_array_size(v_fvarIds_3511_);
                v___x_3513_ = 0usize;
                leanh::lean_inc_ref_n(v_fvarIds_3511_, 2);
                v_varPos_3514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_3491_, v_sz_3512_, v___x_3513_, v_fvarIds_3511_);
                v_ys_3515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_3512_, v___x_3513_, v_fvarIds_3511_);
                v___x_3516_ = 0;
                v___x_3517_ = 1;
                v___x_3518_ = l_Lean_Meta_mkLambdaFVars(
                    v_ys_3515_,
                    v_v_3490_,
                    v___x_3516_,
                    v_nondep_3492_,
                    v___x_3516_,
                    v_nondep_3492_,
                    v___x_3517_,
                    v___y_3506_,
                    v___y_3507_,
                    v___y_3508_,
                    v___y_3509_,
                );
                if leanh::lean_obj_tag(v___x_3518_) == 0 {
                    v_a_3519_ = leanh::lean_ctor_get(v___x_3518_, 0);
                    leanh::lean_inc(v_a_3519_);
                    leanh::lean_dec_ref_known(v___x_3518_, 1);
                    v___x_3520_ = l_Lean_Meta_mkForallFVars(
                        v_ys_3515_,
                        v_t_3493_,
                        v___x_3516_,
                        v_nondep_3492_,
                        v_nondep_3492_,
                        v___x_3517_,
                        v___y_3506_,
                        v___y_3507_,
                        v___y_3508_,
                        v___y_3509_,
                    );
                    leanh::lean_dec_ref(v_ys_3515_);
                    if leanh::lean_obj_tag(v___x_3520_) == 0 {
                        v_a_3521_ = leanh::lean_ctor_get(v___x_3520_, 0);
                        leanh::lean_inc(v_a_3521_);
                        leanh::lean_dec_ref_known(v___x_3520_, 1);
                        v___x_3522_ =
                            l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_3521_, v___y_3505_);
                        if leanh::lean_obj_tag(v___x_3522_) == 0 {
                            v_a_3523_ = leanh::lean_ctor_get(v___x_3522_, 0);
                            leanh::lean_inc_n(v_a_3523_, 2);
                            leanh::lean_dec_ref_known(v___x_3522_, 1);
                            v___x_3524_ = leanh::lean_box_usize(v_sz_3512_);
                            v___x_3525_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1;
                            v___f_3526_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed as *mut core::ffi::c_void, 24, 16);
                            leanh::lean_closure_set(v___f_3526_, 0, v_fvarIdToPos_3491_);
                            leanh::lean_closure_set(v___f_3526_, 1, v_subst_3494_);
                            leanh::lean_closure_set(v___f_3526_, 2, v___x_3524_);
                            leanh::lean_closure_set(v___f_3526_, 3, v___x_3525_);
                            leanh::lean_closure_set(v___f_3526_, 4, v_fvarIds_3511_);
                            leanh::lean_closure_set(v___f_3526_, 5, v_x_3503_);
                            leanh::lean_closure_set(v___f_3526_, 6, v_xs_3495_);
                            leanh::lean_closure_set(v___f_3526_, 7, v_xs_x27_3496_);
                            leanh::lean_closure_set(v___f_3526_, 8, v_args_3497_);
                            leanh::lean_closure_set(v___f_3526_, 9, v_a_3519_);
                            leanh::lean_closure_set(v___f_3526_, 10, v_types_3498_);
                            leanh::lean_closure_set(v___f_3526_, 11, v_a_3523_);
                            leanh::lean_closure_set(v___f_3526_, 12, v_varDeps_3499_);
                            leanh::lean_closure_set(v___f_3526_, 13, v_varPos_3514_);
                            leanh::lean_closure_set(v___f_3526_, 14, v_haveExpr_3500_);
                            leanh::lean_closure_set(v___f_3526_, 15, v_body_3501_);
                            v___x_3527_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_3502_, v_a_3523_, v___f_3526_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
                            return v___x_3527_;
                        } else {
                            leanh::lean_dec(v_a_3519_);
                            leanh::lean_dec_ref(v_varPos_3514_);
                            leanh::lean_dec_ref(v_fvarIds_3511_);
                            leanh::lean_dec_ref(v_x_3503_);
                            leanh::lean_dec(v_declName_3502_);
                            leanh::lean_dec_ref(v_body_3501_);
                            leanh::lean_dec_ref(v_haveExpr_3500_);
                            leanh::lean_dec_ref(v_varDeps_3499_);
                            leanh::lean_dec_ref(v_types_3498_);
                            leanh::lean_dec_ref(v_args_3497_);
                            leanh::lean_dec_ref(v_xs_x27_3496_);
                            leanh::lean_dec_ref(v_xs_3495_);
                            leanh::lean_dec_ref(v_subst_3494_);
                            leanh::lean_dec(v_fvarIdToPos_3491_);
                            v_a_3528_ = leanh::lean_ctor_get(v___x_3522_, 0);
                            v_isSharedCheck_3535_ =
                                (!leanh::lean_is_exclusive(v___x_3522_)) as u8;
                            if v_isSharedCheck_3535_ == 0 {
                                v___x_3530_ = v___x_3522_;
                                v_isShared_3531_ = v_isSharedCheck_3535_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3528_);
                                leanh::lean_dec(v___x_3522_);
                                v___x_3530_ = leanh::lean_box(0);
                                v_isShared_3531_ = v_isSharedCheck_3535_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3519_);
                        leanh::lean_dec_ref(v_varPos_3514_);
                        leanh::lean_dec_ref(v_fvarIds_3511_);
                        leanh::lean_dec_ref(v_x_3503_);
                        leanh::lean_dec(v_declName_3502_);
                        leanh::lean_dec_ref(v_body_3501_);
                        leanh::lean_dec_ref(v_haveExpr_3500_);
                        leanh::lean_dec_ref(v_varDeps_3499_);
                        leanh::lean_dec_ref(v_types_3498_);
                        leanh::lean_dec_ref(v_args_3497_);
                        leanh::lean_dec_ref(v_xs_x27_3496_);
                        leanh::lean_dec_ref(v_xs_3495_);
                        leanh::lean_dec_ref(v_subst_3494_);
                        leanh::lean_dec(v_fvarIdToPos_3491_);
                        v_a_3536_ = leanh::lean_ctor_get(v___x_3520_, 0);
                        v_isSharedCheck_3543_ =
                            (!leanh::lean_is_exclusive(v___x_3520_)) as u8;
                        if v_isSharedCheck_3543_ == 0 {
                            v___x_3538_ = v___x_3520_;
                            v_isShared_3539_ = v_isSharedCheck_3543_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3536_);
                            leanh::lean_dec(v___x_3520_);
                            v___x_3538_ = leanh::lean_box(0);
                            v_isShared_3539_ = v_isSharedCheck_3543_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_ys_3515_);
                    leanh::lean_dec_ref(v_varPos_3514_);
                    leanh::lean_dec_ref(v_fvarIds_3511_);
                    leanh::lean_dec_ref(v_x_3503_);
                    leanh::lean_dec(v_declName_3502_);
                    leanh::lean_dec_ref(v_body_3501_);
                    leanh::lean_dec_ref(v_haveExpr_3500_);
                    leanh::lean_dec_ref(v_varDeps_3499_);
                    leanh::lean_dec_ref(v_types_3498_);
                    leanh::lean_dec_ref(v_args_3497_);
                    leanh::lean_dec_ref(v_xs_x27_3496_);
                    leanh::lean_dec_ref(v_xs_3495_);
                    leanh::lean_dec_ref(v_subst_3494_);
                    leanh::lean_dec_ref(v_t_3493_);
                    leanh::lean_dec(v_fvarIdToPos_3491_);
                    v_a_3544_ = leanh::lean_ctor_get(v___x_3518_, 0);
                    v_isSharedCheck_3551_ = (!leanh::lean_is_exclusive(v___x_3518_)) as u8;
                    if v_isSharedCheck_3551_ == 0 {
                        v___x_3546_ = v___x_3518_;
                        v_isShared_3547_ = v_isSharedCheck_3551_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3544_);
                        leanh::lean_dec(v___x_3518_);
                        v___x_3546_ = leanh::lean_box(0);
                        v_isShared_3547_ = v_isSharedCheck_3551_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3531_ == 0 {
                    v___x_3533_ = v___x_3530_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
                    v___x_3533_ = v_reuseFailAlloc_3534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3533_;
            }
            3 => {
                if v_isShared_3539_ == 0 {
                    v___x_3541_ = v___x_3538_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
                    v___x_3541_ = v_reuseFailAlloc_3542_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3541_;
            }
            5 => {
                if v_isShared_3547_ == 0 {
                    v___x_3549_ = v___x_3546_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3550_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
                    v___x_3549_ = v_reuseFailAlloc_3550_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_3552_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_fvarIdToPos_3553_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_nondep_3554_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_t_3555_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_subst_3556_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_xs_3557_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_xs_x27_3558_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_args_3559_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_types_3560_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_varDeps_3561_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_haveExpr_3562_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_body_3563_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_declName_3564_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_x_3565_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_3566_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_3567_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3568_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_3569_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_3570_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_3571_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_3572_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_nondep_6547__boxed_3573_: u8 = 0;
    let mut v_res_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_6547__boxed_3573_ = (leanh::lean_unbox(v_nondep_3554_) as u8);
    v_res_3574_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(
        v_v_3552_,
        v_fvarIdToPos_3553_,
        v_nondep_6547__boxed_3573_,
        v_t_3555_,
        v_subst_3556_,
        v_xs_3557_,
        v_xs_x27_3558_,
        v_args_3559_,
        v_types_3560_,
        v_varDeps_3561_,
        v_haveExpr_3562_,
        v_body_3563_,
        v_declName_3564_,
        v_x_3565_,
        v___y_3566_,
        v___y_3567_,
        v___y_3568_,
        v___y_3569_,
        v___y_3570_,
        v___y_3571_,
    );
    leanh::lean_dec(v___y_3571_);
    leanh::lean_dec_ref(v___y_3570_);
    leanh::lean_dec(v___y_3569_);
    leanh::lean_dec_ref(v___y_3568_);
    leanh::lean_dec(v___y_3567_);
    leanh::lean_dec_ref(v___y_3566_);
    return v_res_3574_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(
    mut v_haveExpr_3575_: *mut leanh::LeanObject,
    mut v_e_3576_: *mut leanh::LeanObject,
    mut v_xs_3577_: *mut leanh::LeanObject,
    mut v_xs_x27_3578_: *mut leanh::LeanObject,
    mut v_args_3579_: *mut leanh::LeanObject,
    mut v_subst_3580_: *mut leanh::LeanObject,
    mut v_types_3581_: *mut leanh::LeanObject,
    mut v_varDeps_3582_: *mut leanh::LeanObject,
    mut v_fvarIdToPos_3583_: *mut leanh::LeanObject,
    mut v_a_3584_: *mut leanh::LeanObject,
    mut v_a_3585_: *mut leanh::LeanObject,
    mut v_a_3586_: *mut leanh::LeanObject,
    mut v_a_3587_: *mut leanh::LeanObject,
    mut v_a_3588_: *mut leanh::LeanObject,
    mut v_a_3589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3629_: u8 = 0;
    let mut v_a_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3633_: u8 = 0;
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3637_: u8 = 0;
    let mut v_a_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut v_a_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3649_: u8 = 0;
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_a_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v_a_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut v_a_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3673_: u8 = 0;
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_nondep_3678_: u8 = 0;
    let mut v_declName_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_3576_) == 8 {
                    v_nondep_3678_ = leanh::lean_ctor_get_uint8(
                        v_e_3576_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    if v_nondep_3678_ == 1 {
                        v_declName_3679_ = leanh::lean_ctor_get(v_e_3576_, 0);
                        leanh::lean_inc_n(v_declName_3679_, 2);
                        v_type_3680_ = leanh::lean_ctor_get(v_e_3576_, 1);
                        leanh::lean_inc_ref(v_type_3680_);
                        v_value_3681_ = leanh::lean_ctor_get(v_e_3576_, 2);
                        leanh::lean_inc_ref(v_value_3681_);
                        v_body_3682_ = leanh::lean_ctor_get(v_e_3576_, 3);
                        leanh::lean_inc_ref(v_body_3682_);
                        leanh::lean_dec_ref_known(v_e_3576_, 4);
                        v_t_3683_ = lean_expr_instantiate_rev(v_type_3680_, v_xs_3577_);
                        leanh::lean_dec_ref(v_type_3680_);
                        v_v_3684_ = lean_expr_instantiate_rev(v_value_3681_, v_xs_3577_);
                        leanh::lean_dec_ref(v_value_3681_);
                        v___x_3685_ = leanh::lean_box((v_nondep_3678_) as usize);
                        leanh::lean_inc_ref(v_t_3683_);
                        v___f_3686_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed as *mut core::ffi::c_void, 21, 13);
                        leanh::lean_closure_set(v___f_3686_, 0, v_v_3684_);
                        leanh::lean_closure_set(v___f_3686_, 1, v_fvarIdToPos_3583_);
                        leanh::lean_closure_set(v___f_3686_, 2, v___x_3685_);
                        leanh::lean_closure_set(v___f_3686_, 3, v_t_3683_);
                        leanh::lean_closure_set(v___f_3686_, 4, v_subst_3580_);
                        leanh::lean_closure_set(v___f_3686_, 5, v_xs_3577_);
                        leanh::lean_closure_set(v___f_3686_, 6, v_xs_x27_3578_);
                        leanh::lean_closure_set(v___f_3686_, 7, v_args_3579_);
                        leanh::lean_closure_set(v___f_3686_, 8, v_types_3581_);
                        leanh::lean_closure_set(v___f_3686_, 9, v_varDeps_3582_);
                        leanh::lean_closure_set(v___f_3686_, 10, v_haveExpr_3575_);
                        leanh::lean_closure_set(v___f_3686_, 11, v_body_3682_);
                        leanh::lean_closure_set(v___f_3686_, 12, v_declName_3679_);
                        v___x_3687_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_3679_, v_t_3683_, v___f_3686_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_);
                        return v___x_3687_;
                    } else {
                        leanh::lean_dec(v_fvarIdToPos_3583_);
                        leanh::lean_dec_ref(v_xs_3577_);
                        v___y_3592_ = v_a_3584_;
                        v___y_3593_ = v_a_3585_;
                        v___y_3594_ = v_a_3586_;
                        v___y_3595_ = v_a_3587_;
                        v___y_3596_ = v_a_3588_;
                        v___y_3597_ = v_a_3589_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fvarIdToPos_3583_);
                    leanh::lean_dec_ref(v_xs_3577_);
                    v___y_3592_ = v_a_3584_;
                    v___y_3593_ = v_a_3585_;
                    v___y_3594_ = v_a_3586_;
                    v___y_3595_ = v_a_3587_;
                    v___y_3596_ = v_a_3588_;
                    v___y_3597_ = v_a_3589_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3598_ = leanh::lean_unsigned_to_nat(0);
                v___x_3599_ = lean_array_get_size(v_subst_3580_);
                v___x_3600_ = l_Lean_Meta_Sym_instantiateRevRangeS(
                    v_e_3576_,
                    v___x_3598_,
                    v___x_3599_,
                    v_subst_3580_,
                    v___y_3592_,
                    v___y_3593_,
                    v___y_3594_,
                    v___y_3595_,
                    v___y_3596_,
                    v___y_3597_,
                );
                leanh::lean_dec_ref(v_subst_3580_);
                if leanh::lean_obj_tag(v___x_3600_) == 0 {
                    v_a_3601_ = leanh::lean_ctor_get(v___x_3600_, 0);
                    leanh::lean_inc_n(v_a_3601_, 2);
                    leanh::lean_dec_ref_known(v___x_3600_, 1);
                    v___x_3602_ = l_Lean_Meta_Sym_inferType___redArg(
                        v_a_3601_,
                        v___y_3593_,
                        v___y_3594_,
                        v___y_3595_,
                        v___y_3596_,
                        v___y_3597_,
                    );
                    if leanh::lean_obj_tag(v___x_3602_) == 0 {
                        v_a_3603_ = leanh::lean_ctor_get(v___x_3602_, 0);
                        leanh::lean_inc_n(v_a_3603_, 2);
                        leanh::lean_dec_ref_known(v___x_3602_, 1);
                        v___x_3604_ = l_Lean_Meta_Sym_getLevel___redArg(
                            v_a_3603_,
                            v___y_3593_,
                            v___y_3594_,
                            v___y_3595_,
                            v___y_3596_,
                            v___y_3597_,
                        );
                        if leanh::lean_obj_tag(v___x_3604_) == 0 {
                            v_a_3605_ = leanh::lean_ctor_get(v___x_3604_, 0);
                            leanh::lean_inc(v_a_3605_);
                            leanh::lean_dec_ref_known(v___x_3604_, 1);
                            leanh::lean_inc(v_a_3603_);
                            v___x_3606_ =
                                l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(
                                    v_types_3581_,
                                    v_a_3603_,
                                    v___y_3592_,
                                    v___y_3593_,
                                    v___y_3594_,
                                    v___y_3595_,
                                    v___y_3596_,
                                    v___y_3597_,
                                );
                            leanh::lean_dec_ref(v_types_3581_);
                            if leanh::lean_obj_tag(v___x_3606_) == 0 {
                                v_a_3607_ = leanh::lean_ctor_get(v___x_3606_, 0);
                                leanh::lean_inc(v_a_3607_);
                                leanh::lean_dec_ref_known(v___x_3606_, 1);
                                v___x_3608_ = l_Lean_Meta_Sym_mkLambdaFVarsS(
                                    v_xs_x27_3578_,
                                    v_a_3601_,
                                    v___y_3592_,
                                    v___y_3593_,
                                    v___y_3594_,
                                    v___y_3595_,
                                    v___y_3596_,
                                    v___y_3597_,
                                );
                                leanh::lean_dec_ref(v_xs_x27_3578_);
                                if leanh::lean_obj_tag(v___x_3608_) == 0 {
                                    v_a_3609_ = leanh::lean_ctor_get(v___x_3608_, 0);
                                    leanh::lean_inc(v_a_3609_);
                                    leanh::lean_dec_ref_known(v___x_3608_, 1);
                                    v___x_3610_ = l_Lean_mkAppN(v_a_3609_, v_args_3579_);
                                    leanh::lean_dec_ref(v_args_3579_);
                                    v___x_3611_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                        v___x_3610_,
                                        v___y_3593_,
                                    );
                                    if leanh::lean_obj_tag(v___x_3611_) == 0 {
                                        v_a_3612_ = leanh::lean_ctor_get(v___x_3611_, 0);
                                        v_isSharedCheck_3629_ =
                                            (!leanh::lean_is_exclusive(v___x_3611_)) as u8;
                                        if v_isSharedCheck_3629_ == 0 {
                                            v___x_3614_ = v___x_3611_;
                                            v_isShared_3615_ = v_isSharedCheck_3629_;
                                            state = 2;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3612_);
                                            leanh::lean_dec(v___x_3611_);
                                            v___x_3614_ = leanh::lean_box(0);
                                            v_isShared_3615_ = v_isSharedCheck_3629_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_3607_);
                                        leanh::lean_dec(v_a_3605_);
                                        leanh::lean_dec(v_a_3603_);
                                        leanh::lean_dec_ref(v_varDeps_3582_);
                                        leanh::lean_dec_ref(v_haveExpr_3575_);
                                        v_a_3630_ = leanh::lean_ctor_get(v___x_3611_, 0);
                                        v_isSharedCheck_3637_ =
                                            (!leanh::lean_is_exclusive(v___x_3611_)) as u8;
                                        if v_isSharedCheck_3637_ == 0 {
                                            v___x_3632_ = v___x_3611_;
                                            v_isShared_3633_ = v_isSharedCheck_3637_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3630_);
                                            leanh::lean_dec(v___x_3611_);
                                            v___x_3632_ = leanh::lean_box(0);
                                            v_isShared_3633_ = v_isSharedCheck_3637_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_3607_);
                                    leanh::lean_dec(v_a_3605_);
                                    leanh::lean_dec(v_a_3603_);
                                    leanh::lean_dec_ref(v_varDeps_3582_);
                                    leanh::lean_dec_ref(v_args_3579_);
                                    leanh::lean_dec_ref(v_haveExpr_3575_);
                                    v_a_3638_ = leanh::lean_ctor_get(v___x_3608_, 0);
                                    v_isSharedCheck_3645_ =
                                        (!leanh::lean_is_exclusive(v___x_3608_)) as u8;
                                    if v_isSharedCheck_3645_ == 0 {
                                        v___x_3640_ = v___x_3608_;
                                        v_isShared_3641_ = v_isSharedCheck_3645_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3638_);
                                        leanh::lean_dec(v___x_3608_);
                                        v___x_3640_ = leanh::lean_box(0);
                                        v_isShared_3641_ = v_isSharedCheck_3645_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_3605_);
                                leanh::lean_dec(v_a_3603_);
                                leanh::lean_dec(v_a_3601_);
                                leanh::lean_dec_ref(v_varDeps_3582_);
                                leanh::lean_dec_ref(v_args_3579_);
                                leanh::lean_dec_ref(v_xs_x27_3578_);
                                leanh::lean_dec_ref(v_haveExpr_3575_);
                                v_a_3646_ = leanh::lean_ctor_get(v___x_3606_, 0);
                                v_isSharedCheck_3653_ =
                                    (!leanh::lean_is_exclusive(v___x_3606_)) as u8;
                                if v_isSharedCheck_3653_ == 0 {
                                    v___x_3648_ = v___x_3606_;
                                    v_isShared_3649_ = v_isSharedCheck_3653_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3646_);
                                    leanh::lean_dec(v___x_3606_);
                                    v___x_3648_ = leanh::lean_box(0);
                                    v_isShared_3649_ = v_isSharedCheck_3653_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_3603_);
                            leanh::lean_dec(v_a_3601_);
                            leanh::lean_dec_ref(v_varDeps_3582_);
                            leanh::lean_dec_ref(v_types_3581_);
                            leanh::lean_dec_ref(v_args_3579_);
                            leanh::lean_dec_ref(v_xs_x27_3578_);
                            leanh::lean_dec_ref(v_haveExpr_3575_);
                            v_a_3654_ = leanh::lean_ctor_get(v___x_3604_, 0);
                            v_isSharedCheck_3661_ =
                                (!leanh::lean_is_exclusive(v___x_3604_)) as u8;
                            if v_isSharedCheck_3661_ == 0 {
                                v___x_3656_ = v___x_3604_;
                                v_isShared_3657_ = v_isSharedCheck_3661_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3654_);
                                leanh::lean_dec(v___x_3604_);
                                v___x_3656_ = leanh::lean_box(0);
                                v_isShared_3657_ = v_isSharedCheck_3661_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3601_);
                        leanh::lean_dec_ref(v_varDeps_3582_);
                        leanh::lean_dec_ref(v_types_3581_);
                        leanh::lean_dec_ref(v_args_3579_);
                        leanh::lean_dec_ref(v_xs_x27_3578_);
                        leanh::lean_dec_ref(v_haveExpr_3575_);
                        v_a_3662_ = leanh::lean_ctor_get(v___x_3602_, 0);
                        v_isSharedCheck_3669_ =
                            (!leanh::lean_is_exclusive(v___x_3602_)) as u8;
                        if v_isSharedCheck_3669_ == 0 {
                            v___x_3664_ = v___x_3602_;
                            v_isShared_3665_ = v_isSharedCheck_3669_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3662_);
                            leanh::lean_dec(v___x_3602_);
                            v___x_3664_ = leanh::lean_box(0);
                            v_isShared_3665_ = v_isSharedCheck_3669_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_varDeps_3582_);
                    leanh::lean_dec_ref(v_types_3581_);
                    leanh::lean_dec_ref(v_args_3579_);
                    leanh::lean_dec_ref(v_xs_x27_3578_);
                    leanh::lean_dec_ref(v_haveExpr_3575_);
                    v_a_3670_ = leanh::lean_ctor_get(v___x_3600_, 0);
                    v_isSharedCheck_3677_ = (!leanh::lean_is_exclusive(v___x_3600_)) as u8;
                    if v_isSharedCheck_3677_ == 0 {
                        v___x_3672_ = v___x_3600_;
                        v_isShared_3673_ = v_isSharedCheck_3677_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3670_);
                        leanh::lean_dec(v___x_3600_);
                        v___x_3672_ = leanh::lean_box(0);
                        v_isShared_3673_ = v_isSharedCheck_3677_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3616_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1;
                v___x_3617_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_3605_);
                v___x_3618_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3618_, 0, v_a_3605_);
                leanh::lean_ctor_set(v___x_3618_, 1, v___x_3617_);
                leanh::lean_inc_ref(v___x_3618_);
                v___x_3619_ = l_Lean_mkConst(v___x_3616_, v___x_3618_);
                leanh::lean_inc(v_a_3612_);
                leanh::lean_inc_ref(v_haveExpr_3575_);
                leanh::lean_inc_n(v_a_3603_, 2);
                v___x_3620_ = l_Lean_mkApp3(v___x_3619_, v_a_3603_, v_haveExpr_3575_, v_a_3612_);
                v___x_3621_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3;
                v___x_3622_ = l_Lean_mkConst(v___x_3621_, v___x_3618_);
                v___x_3623_ = l_Lean_mkAppB(v___x_3622_, v_a_3603_, v_haveExpr_3575_);
                v___x_3624_ = l_Lean_Meta_mkExpectedPropHint(v___x_3623_, v___x_3620_);
                v___x_3625_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_3625_, 0, v_a_3603_);
                leanh::lean_ctor_set(v___x_3625_, 1, v_a_3605_);
                leanh::lean_ctor_set(v___x_3625_, 2, v_a_3612_);
                leanh::lean_ctor_set(v___x_3625_, 3, v___x_3624_);
                leanh::lean_ctor_set(v___x_3625_, 4, v_varDeps_3582_);
                leanh::lean_ctor_set(v___x_3625_, 5, v_a_3607_);
                if v_isShared_3615_ == 0 {
                    leanh::lean_ctor_set(v___x_3614_, 0, v___x_3625_);
                    v___x_3627_ = v___x_3614_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3628_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
                    v___x_3627_ = v_reuseFailAlloc_3628_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3627_;
            }
            4 => {
                if v_isShared_3633_ == 0 {
                    v___x_3635_ = v___x_3632_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3636_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
                    v___x_3635_ = v_reuseFailAlloc_3636_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3635_;
            }
            6 => {
                if v_isShared_3641_ == 0 {
                    v___x_3643_ = v___x_3640_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
                    v___x_3643_ = v_reuseFailAlloc_3644_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3643_;
            }
            8 => {
                if v_isShared_3649_ == 0 {
                    v___x_3651_ = v___x_3648_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
                    v___x_3651_ = v_reuseFailAlloc_3652_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3651_;
            }
            10 => {
                if v_isShared_3657_ == 0 {
                    v___x_3659_ = v___x_3656_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3659_;
            }
            12 => {
                if v_isShared_3665_ == 0 {
                    v___x_3667_ = v___x_3664_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3668_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
                    v___x_3667_ = v_reuseFailAlloc_3668_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3667_;
            }
            14 => {
                if v_isShared_3673_ == 0 {
                    v___x_3675_ = v___x_3672_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3676_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
                    v___x_3675_ = v_reuseFailAlloc_3676_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(
    mut v_fvarIdToPos_3688_: *mut leanh::LeanObject,
    mut v_subst_3689_: *mut leanh::LeanObject,
    mut v_sz_3690_: usize,
    mut v___x_3691_: usize,
    mut v_fvarIds_3692_: *mut leanh::LeanObject,
    mut v_x_3693_: *mut leanh::LeanObject,
    mut v_xs_3694_: *mut leanh::LeanObject,
    mut v_xs_x27_3695_: *mut leanh::LeanObject,
    mut v_args_3696_: *mut leanh::LeanObject,
    mut v_a_3697_: *mut leanh::LeanObject,
    mut v_types_3698_: *mut leanh::LeanObject,
    mut v_a_3699_: *mut leanh::LeanObject,
    mut v_varDeps_3700_: *mut leanh::LeanObject,
    mut v_varPos_3701_: *mut leanh::LeanObject,
    mut v_haveExpr_3702_: *mut leanh::LeanObject,
    mut v_body_3703_: *mut leanh::LeanObject,
    mut v_x_x27_3704_: *mut leanh::LeanObject,
    mut v___y_3705_: *mut leanh::LeanObject,
    mut v___y_3706_: *mut leanh::LeanObject,
    mut v___y_3707_: *mut leanh::LeanObject,
    mut v___y_3708_: *mut leanh::LeanObject,
    mut v___y_3709_: *mut leanh::LeanObject,
    mut v___y_3710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_3688_, v_subst_3689_, v_sz_3690_, v___x_3691_, v_fvarIds_3692_);
                leanh::lean_inc_ref(v_x_x27_3704_);
                v___x_3713_ = l_Lean_mkAppN(v_x_x27_3704_, v___x_3712_);
                leanh::lean_dec_ref(v___x_3712_);
                v___x_3714_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_3713_, v___y_3706_);
                if leanh::lean_obj_tag(v___x_3714_) == 0 {
                    v_a_3715_ = leanh::lean_ctor_get(v___x_3714_, 0);
                    leanh::lean_inc(v_a_3715_);
                    leanh::lean_dec_ref_known(v___x_3714_, 1);
                    v___x_3716_ = l_Lean_Expr_fvarId_x21(v_x_3693_);
                    v___x_3717_ = lean_array_get_size(v_xs_3694_);
                    v___x_3718_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_3716_, v___x_3717_, v_fvarIdToPos_3688_);
                    v___x_3719_ = lean_array_push(v_xs_3694_, v_x_3693_);
                    v___x_3720_ = lean_array_push(v_xs_x27_3695_, v_x_x27_3704_);
                    v___x_3721_ = lean_array_push(v_args_3696_, v_a_3697_);
                    v___x_3722_ = lean_array_push(v_subst_3689_, v_a_3715_);
                    v___x_3723_ = lean_array_push(v_types_3698_, v_a_3699_);
                    v___x_3724_ = lean_array_push(v_varDeps_3700_, v_varPos_3701_);
                    v___x_3725_ =
                        l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(
                            v_haveExpr_3702_,
                            v_body_3703_,
                            v___x_3719_,
                            v___x_3720_,
                            v___x_3721_,
                            v___x_3722_,
                            v___x_3723_,
                            v___x_3724_,
                            v___x_3718_,
                            v___y_3705_,
                            v___y_3706_,
                            v___y_3707_,
                            v___y_3708_,
                            v___y_3709_,
                            v___y_3710_,
                        );
                    return v___x_3725_;
                } else {
                    leanh::lean_dec_ref(v_x_x27_3704_);
                    leanh::lean_dec_ref(v_body_3703_);
                    leanh::lean_dec_ref(v_haveExpr_3702_);
                    leanh::lean_dec_ref(v_varPos_3701_);
                    leanh::lean_dec_ref(v_varDeps_3700_);
                    leanh::lean_dec_ref(v_a_3699_);
                    leanh::lean_dec_ref(v_types_3698_);
                    leanh::lean_dec_ref(v_a_3697_);
                    leanh::lean_dec_ref(v_args_3696_);
                    leanh::lean_dec_ref(v_xs_x27_3695_);
                    leanh::lean_dec_ref(v_xs_3694_);
                    leanh::lean_dec_ref(v_x_3693_);
                    leanh::lean_dec_ref(v_subst_3689_);
                    leanh::lean_dec(v_fvarIdToPos_3688_);
                    v_a_3726_ = leanh::lean_ctor_get(v___x_3714_, 0);
                    v_isSharedCheck_3733_ = (!leanh::lean_is_exclusive(v___x_3714_)) as u8;
                    if v_isSharedCheck_3733_ == 0 {
                        v___x_3728_ = v___x_3714_;
                        v_isShared_3729_ = v_isSharedCheck_3733_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3726_);
                        leanh::lean_dec(v___x_3714_);
                        v___x_3728_ = leanh::lean_box(0);
                        v_isShared_3729_ = v_isSharedCheck_3733_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3729_ == 0 {
                    v___x_3731_ = v___x_3728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
                    v___x_3731_ = v_reuseFailAlloc_3732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(
    mut v_haveExpr_3734_: *mut leanh::LeanObject,
    mut v_e_3735_: *mut leanh::LeanObject,
    mut v_xs_3736_: *mut leanh::LeanObject,
    mut v_xs_x27_3737_: *mut leanh::LeanObject,
    mut v_args_3738_: *mut leanh::LeanObject,
    mut v_subst_3739_: *mut leanh::LeanObject,
    mut v_types_3740_: *mut leanh::LeanObject,
    mut v_varDeps_3741_: *mut leanh::LeanObject,
    mut v_fvarIdToPos_3742_: *mut leanh::LeanObject,
    mut v_a_3743_: *mut leanh::LeanObject,
    mut v_a_3744_: *mut leanh::LeanObject,
    mut v_a_3745_: *mut leanh::LeanObject,
    mut v_a_3746_: *mut leanh::LeanObject,
    mut v_a_3747_: *mut leanh::LeanObject,
    mut v_a_3748_: *mut leanh::LeanObject,
    mut v_a_3749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3750_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(
        v_haveExpr_3734_,
        v_e_3735_,
        v_xs_3736_,
        v_xs_x27_3737_,
        v_args_3738_,
        v_subst_3739_,
        v_types_3740_,
        v_varDeps_3741_,
        v_fvarIdToPos_3742_,
        v_a_3743_,
        v_a_3744_,
        v_a_3745_,
        v_a_3746_,
        v_a_3747_,
        v_a_3748_,
    );
    leanh::lean_dec(v_a_3748_);
    leanh::lean_dec_ref(v_a_3747_);
    leanh::lean_dec(v_a_3746_);
    leanh::lean_dec_ref(v_a_3745_);
    leanh::lean_dec(v_a_3744_);
    leanh::lean_dec_ref(v_a_3743_);
    return v_res_3750_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(
    mut v_00_u03b4_3751_: *mut leanh::LeanObject,
    mut v_t_3752_: *mut leanh::LeanObject,
    mut v_k_3753_: *mut leanh::LeanObject,
    mut v_fallback_3754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3755_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_3752_, v_k_3753_, v_fallback_3754_);
    return v___x_3755_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(
    mut v_00_u03b4_3756_: *mut leanh::LeanObject,
    mut v_t_3757_: *mut leanh::LeanObject,
    mut v_k_3758_: *mut leanh::LeanObject,
    mut v_fallback_3759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_3756_, v_t_3757_, v_k_3758_, v_fallback_3759_);
    leanh::lean_dec(v_fallback_3759_);
    leanh::lean_dec(v_k_3758_);
    leanh::lean_dec(v_t_3757_);
    return v_res_3760_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(
    mut v_00_u03b1_3761_: *mut leanh::LeanObject,
    mut v_name_3762_: *mut leanh::LeanObject,
    mut v_bi_3763_: u8,
    mut v_type_3764_: *mut leanh::LeanObject,
    mut v_k_3765_: *mut leanh::LeanObject,
    mut v_kind_3766_: u8,
    mut v___y_3767_: *mut leanh::LeanObject,
    mut v___y_3768_: *mut leanh::LeanObject,
    mut v___y_3769_: *mut leanh::LeanObject,
    mut v___y_3770_: *mut leanh::LeanObject,
    mut v___y_3771_: *mut leanh::LeanObject,
    mut v___y_3772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3774_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_3762_, v_bi_3763_, v_type_3764_, v_k_3765_, v_kind_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
    return v___x_3774_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(
    mut v_00_u03b1_3775_: *mut leanh::LeanObject,
    mut v_name_3776_: *mut leanh::LeanObject,
    mut v_bi_3777_: *mut leanh::LeanObject,
    mut v_type_3778_: *mut leanh::LeanObject,
    mut v_k_3779_: *mut leanh::LeanObject,
    mut v_kind_3780_: *mut leanh::LeanObject,
    mut v___y_3781_: *mut leanh::LeanObject,
    mut v___y_3782_: *mut leanh::LeanObject,
    mut v___y_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
    mut v___y_3785_: *mut leanh::LeanObject,
    mut v___y_3786_: *mut leanh::LeanObject,
    mut v___y_3787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3788_: u8 = 0;
    let mut v_kind_boxed_3789_: u8 = 0;
    let mut v_res_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3788_ = (leanh::lean_unbox(v_bi_3777_) as u8);
    v_kind_boxed_3789_ = (leanh::lean_unbox(v_kind_3780_) as u8);
    v_res_3790_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_3775_, v_name_3776_, v_bi_boxed_3788_, v_type_3778_, v_k_3779_, v_kind_boxed_3789_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
    leanh::lean_dec(v___y_3786_);
    leanh::lean_dec_ref(v___y_3785_);
    leanh::lean_dec(v___y_3784_);
    leanh::lean_dec_ref(v___y_3783_);
    leanh::lean_dec(v___y_3782_);
    leanh::lean_dec_ref(v___y_3781_);
    return v_res_3790_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(
    mut v_00_u03b1_3791_: *mut leanh::LeanObject,
    mut v_name_3792_: *mut leanh::LeanObject,
    mut v_type_3793_: *mut leanh::LeanObject,
    mut v_k_3794_: *mut leanh::LeanObject,
    mut v___y_3795_: *mut leanh::LeanObject,
    mut v___y_3796_: *mut leanh::LeanObject,
    mut v___y_3797_: *mut leanh::LeanObject,
    mut v___y_3798_: *mut leanh::LeanObject,
    mut v___y_3799_: *mut leanh::LeanObject,
    mut v___y_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3802_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_3792_, v_type_3793_, v_k_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
    return v___x_3802_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(
    mut v_00_u03b1_3803_: *mut leanh::LeanObject,
    mut v_name_3804_: *mut leanh::LeanObject,
    mut v_type_3805_: *mut leanh::LeanObject,
    mut v_k_3806_: *mut leanh::LeanObject,
    mut v___y_3807_: *mut leanh::LeanObject,
    mut v___y_3808_: *mut leanh::LeanObject,
    mut v___y_3809_: *mut leanh::LeanObject,
    mut v___y_3810_: *mut leanh::LeanObject,
    mut v___y_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
    mut v___y_3813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3814_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_3803_, v_name_3804_, v_type_3805_, v_k_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
    leanh::lean_dec(v___y_3812_);
    leanh::lean_dec_ref(v___y_3811_);
    leanh::lean_dec(v___y_3810_);
    leanh::lean_dec_ref(v___y_3809_);
    leanh::lean_dec(v___y_3808_);
    leanh::lean_dec_ref(v___y_3807_);
    return v_res_3814_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_toBetaApp(
    mut v_haveExpr_3817_: *mut leanh::LeanObject,
    mut v_a_3818_: *mut leanh::LeanObject,
    mut v_a_3819_: *mut leanh::LeanObject,
    mut v_a_3820_: *mut leanh::LeanObject,
    mut v_a_3821_: *mut leanh::LeanObject,
    mut v_a_3822_: *mut leanh::LeanObject,
    mut v_a_3823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = l_Lean_Meta_Sym_Simp_toBetaApp___closed__0;
    v___x_3826_ = leanh::lean_box(1);
    leanh::lean_inc_ref(v_haveExpr_3817_);
    v___x_3827_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(
        v_haveExpr_3817_,
        v_haveExpr_3817_,
        v___x_3825_,
        v___x_3825_,
        v___x_3825_,
        v___x_3825_,
        v___x_3825_,
        v___x_3825_,
        v___x_3826_,
        v_a_3818_,
        v_a_3819_,
        v_a_3820_,
        v_a_3821_,
        v_a_3822_,
        v_a_3823_,
    );
    return v___x_3827_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_toBetaApp___boxed(
    mut v_haveExpr_3828_: *mut leanh::LeanObject,
    mut v_a_3829_: *mut leanh::LeanObject,
    mut v_a_3830_: *mut leanh::LeanObject,
    mut v_a_3831_: *mut leanh::LeanObject,
    mut v_a_3832_: *mut leanh::LeanObject,
    mut v_a_3833_: *mut leanh::LeanObject,
    mut v_a_3834_: *mut leanh::LeanObject,
    mut v_a_3835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3836_ = l_Lean_Meta_Sym_Simp_toBetaApp(
        v_haveExpr_3828_,
        v_a_3829_,
        v_a_3830_,
        v_a_3831_,
        v_a_3832_,
        v_a_3833_,
        v_a_3834_,
    );
    leanh::lean_dec(v_a_3834_);
    leanh::lean_dec_ref(v_a_3833_);
    leanh::lean_dec(v_a_3832_);
    leanh::lean_dec_ref(v_a_3831_);
    leanh::lean_dec(v_a_3830_);
    leanh::lean_dec_ref(v_a_3829_);
    return v_res_3836_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(
    mut v_type_3837_: *mut leanh::LeanObject,
    mut v_n_3838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3840_: u8 = 0;
    let mut v_one_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3839_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3840_ = lean_nat_dec_eq(v_n_3838_, v_zero_3839_);
                if v_isZero_3840_ == 1 {
                    leanh::lean_dec(v_n_3838_);
                    return v_type_3837_;
                } else {
                    v_one_3841_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3842_ = lean_nat_sub(v_n_3838_, v_one_3841_);
                    leanh::lean_dec(v_n_3838_);
                    v___x_3843_ = l_Lean_Expr_bindingBody_x21(v_type_3837_);
                    leanh::lean_dec_ref(v_type_3837_);
                    v_type_3837_ = v___x_3843_;
                    v_n_3838_ = v_n_3842_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3845_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3845_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3846_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0);
    v___x_3847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3847_, 0, v___x_3846_);
    return v___x_3847_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(
    mut v_00_u03b2_3848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3849_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1);
    return v___x_3849_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(
    mut v_idx_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3852_ = l_Lean_Expr_bvar___override(v_idx_3850_);
    v___x_3853_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3852_, v___y_3851_);
    return v___x_3853_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(
    mut v_idx_3854_: *mut leanh::LeanObject,
    mut v___y_3855_: u8,
    mut v___y_3856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3857_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v_idx_3854_, v___y_3856_);
    return v___x_3857_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(
    mut v_idx_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_21807__boxed_3861_: u8 = 0;
    let mut v_res_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_21807__boxed_3861_ = (leanh::lean_unbox(v___y_3859_) as u8);
    v_res_3862_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_idx_3858_, v___y_21807__boxed_3861_, v___y_3860_);
    return v_res_3862_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(
    mut v_msg_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: u8,
    mut v___y_3872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737__overap_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3873_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0;
    v___f_3874_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1;
    v___f_3875_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2;
    v___f_3876_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3;
    v___f_3877_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4;
    v___f_3878_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5;
    v___f_3879_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6;
    v___x_3880_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3880_, 0, v___f_3873_);
    leanh::lean_ctor_set(v___x_3880_, 1, v___f_3874_);
    v___x_3881_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3881_, 0, v___x_3880_);
    leanh::lean_ctor_set(v___x_3881_, 1, v___f_3875_);
    leanh::lean_ctor_set(v___x_3881_, 2, v___f_3876_);
    leanh::lean_ctor_set(v___x_3881_, 3, v___f_3877_);
    leanh::lean_ctor_set(v___x_3881_, 4, v___f_3878_);
    v___x_3882_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3882_, 0, v___x_3881_);
    leanh::lean_ctor_set(v___x_3882_, 1, v___f_3879_);
    leanh::lean_inc_ref_n(v___x_3882_, 6);
    v___f_3883_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3883_, 0, v___x_3882_);
    v___f_3884_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3884_, 0, v___x_3882_);
    v___f_3885_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3885_, 0, v___x_3882_);
    v___f_3886_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3886_, 0, v___x_3882_);
    v___x_3887_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_3887_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3887_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3887_, 2, v___x_3882_);
    v___x_3888_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3888_, 0, v___x_3887_);
    leanh::lean_ctor_set(v___x_3888_, 1, v___f_3883_);
    v___x_3889_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_3889_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3889_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3889_, 2, v___x_3882_);
    v___x_3890_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3890_, 0, v___x_3888_);
    leanh::lean_ctor_set(v___x_3890_, 1, v___x_3889_);
    leanh::lean_ctor_set(v___x_3890_, 2, v___f_3884_);
    leanh::lean_ctor_set(v___x_3890_, 3, v___f_3885_);
    leanh::lean_ctor_set(v___x_3890_, 4, v___f_3886_);
    v___x_3891_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_3891_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3891_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3891_, 2, v___x_3882_);
    v___x_3892_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3892_, 0, v___x_3890_);
    leanh::lean_ctor_set(v___x_3892_, 1, v___x_3891_);
    v___x_3893_ = leanh::lean_box(0);
    v___x_3894_ = l_instInhabitedOfMonad___redArg(v___x_3892_, v___x_3893_);
    v___f_3895_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3895_, 0, v___x_3894_);
    v___x_1737__overap_3896_ = lean_panic_fn_borrowed(v___f_3895_, v_msg_3870_);
    leanh::lean_dec_ref(v___f_3895_);
    v___x_3897_ = leanh::lean_box((v___y_3871_) as usize);
    v___x_3898_ = leanh::lean_apply_2(v___x_1737__overap_3896_, v___x_3897_, v___y_3872_);
    return v___x_3898_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(
    mut v_msg_3899_: *mut leanh::LeanObject,
    mut v___y_3900_: *mut leanh::LeanObject,
    mut v___y_3901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_21829__boxed_3902_: u8 = 0;
    let mut v_res_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_21829__boxed_3902_ = (leanh::lean_unbox(v___y_3900_) as u8);
    v_res_3903_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_msg_3899_, v___y_21829__boxed_3902_, v___y_3901_);
    return v_res_3903_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(
    mut v_structName_3904_: *mut leanh::LeanObject,
    mut v_idx_3905_: *mut leanh::LeanObject,
    mut v_struct_3906_: *mut leanh::LeanObject,
    mut v___y_3907_: *mut leanh::LeanObject,
    mut v___y_3908_: u8,
    mut v___y_3909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3919_: u8 = 0;
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_3908_ == 0 {
                    v___y_3911_ = v___y_3907_;
                    v___y_3912_ = v___y_3909_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_struct_3906_);
                    v___x_3925_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_struct_3906_,
                        v___y_3908_,
                        v___y_3909_,
                    );
                    v_snd_3926_ = leanh::lean_ctor_get(v___x_3925_, 1);
                    leanh::lean_inc(v_snd_3926_);
                    leanh::lean_dec_ref(v___x_3925_);
                    v___y_3911_ = v___y_3907_;
                    v___y_3912_ = v_snd_3926_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3913_ =
                    l_Lean_Expr_proj___override(v_structName_3904_, v_idx_3905_, v_struct_3906_);
                v___x_3914_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3913_, v___y_3912_);
                v_fst_3915_ = leanh::lean_ctor_get(v___x_3914_, 0);
                v_snd_3916_ = leanh::lean_ctor_get(v___x_3914_, 1);
                v_isSharedCheck_3924_ = (!leanh::lean_is_exclusive(v___x_3914_)) as u8;
                if v_isSharedCheck_3924_ == 0 {
                    v___x_3918_ = v___x_3914_;
                    v_isShared_3919_ = v_isSharedCheck_3924_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3916_);
                    leanh::lean_inc(v_fst_3915_);
                    leanh::lean_dec(v___x_3914_);
                    v___x_3918_ = leanh::lean_box(0);
                    v_isShared_3919_ = v_isSharedCheck_3924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3919_ == 0 {
                    leanh::lean_ctor_set(v___x_3918_, 1, v___y_3911_);
                    v___x_3921_ = v___x_3918_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_fst_3915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 1, v___y_3911_);
                    v___x_3921_ = v_reuseFailAlloc_3923_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3922_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3922_, 0, v___x_3921_);
                leanh::lean_ctor_set(v___x_3922_, 1, v_snd_3916_);
                return v___x_3922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9___boxed(
    mut v_structName_3927_: *mut leanh::LeanObject,
    mut v_idx_3928_: *mut leanh::LeanObject,
    mut v_struct_3929_: *mut leanh::LeanObject,
    mut v___y_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_21893__boxed_3933_: u8 = 0;
    let mut v_res_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_21893__boxed_3933_ = (leanh::lean_unbox(v___y_3931_) as u8);
    v_res_3934_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_structName_3927_, v_idx_3928_, v_struct_3929_, v___y_3930_, v___y_21893__boxed_3933_, v___y_3932_);
    return v_res_3934_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(
    mut v_x_3935_: *mut leanh::LeanObject,
    mut v_bi_3936_: u8,
    mut v_t_3937_: *mut leanh::LeanObject,
    mut v_b_3938_: *mut leanh::LeanObject,
    mut v___y_3939_: *mut leanh::LeanObject,
    mut v___y_3940_: u8,
    mut v___y_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3956_: u8 = 0;
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_3940_ == 0 {
                    v___y_3943_ = v___y_3939_;
                    v___y_3944_ = v___y_3941_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_t_3937_);
                    v___x_3957_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_3937_,
                        v___y_3940_,
                        v___y_3941_,
                    );
                    v_snd_3958_ = leanh::lean_ctor_get(v___x_3957_, 1);
                    leanh::lean_inc(v_snd_3958_);
                    leanh::lean_dec_ref(v___x_3957_);
                    leanh::lean_inc_ref(v_b_3938_);
                    v___x_3959_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_3938_,
                        v___y_3940_,
                        v_snd_3958_,
                    );
                    v_snd_3960_ = leanh::lean_ctor_get(v___x_3959_, 1);
                    leanh::lean_inc(v_snd_3960_);
                    leanh::lean_dec_ref(v___x_3959_);
                    v___y_3943_ = v___y_3939_;
                    v___y_3944_ = v_snd_3960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3945_ =
                    l_Lean_Expr_lam___override(v_x_3935_, v_t_3937_, v_b_3938_, v_bi_3936_);
                v___x_3946_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3945_, v___y_3944_);
                v_fst_3947_ = leanh::lean_ctor_get(v___x_3946_, 0);
                v_snd_3948_ = leanh::lean_ctor_get(v___x_3946_, 1);
                v_isSharedCheck_3956_ = (!leanh::lean_is_exclusive(v___x_3946_)) as u8;
                if v_isSharedCheck_3956_ == 0 {
                    v___x_3950_ = v___x_3946_;
                    v_isShared_3951_ = v_isSharedCheck_3956_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3948_);
                    leanh::lean_inc(v_fst_3947_);
                    leanh::lean_dec(v___x_3946_);
                    v___x_3950_ = leanh::lean_box(0);
                    v_isShared_3951_ = v_isSharedCheck_3956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3951_ == 0 {
                    leanh::lean_ctor_set(v___x_3950_, 1, v___y_3943_);
                    v___x_3953_ = v___x_3950_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3955_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_fst_3947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 1, v___y_3943_);
                    v___x_3953_ = v_reuseFailAlloc_3955_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3954_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3954_, 0, v___x_3953_);
                leanh::lean_ctor_set(v___x_3954_, 1, v_snd_3948_);
                return v___x_3954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5___boxed(
    mut v_x_3961_: *mut leanh::LeanObject,
    mut v_bi_3962_: *mut leanh::LeanObject,
    mut v_t_3963_: *mut leanh::LeanObject,
    mut v_b_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
    mut v___y_3967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3968_: u8 = 0;
    let mut v___y_21937__boxed_3969_: u8 = 0;
    let mut v_res_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3968_ = (leanh::lean_unbox(v_bi_3962_) as u8);
    v___y_21937__boxed_3969_ = (leanh::lean_unbox(v___y_3966_) as u8);
    v_res_3970_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_x_3961_, v_bi_boxed_3968_, v_t_3963_, v_b_3964_, v___y_3965_, v___y_21937__boxed_3969_, v___y_3967_);
    return v_res_3970_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(
    mut v_msg_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: u8,
    mut v___y_3974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_21471__overap_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3975_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0;
    v___f_3976_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1;
    v___f_3977_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2;
    v___f_3978_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3;
    v___f_3979_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4;
    v___f_3980_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5;
    v___f_3981_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6;
    v___x_3982_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3982_, 0, v___f_3975_);
    leanh::lean_ctor_set(v___x_3982_, 1, v___f_3976_);
    v___x_3983_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3983_, 0, v___x_3982_);
    leanh::lean_ctor_set(v___x_3983_, 1, v___f_3977_);
    leanh::lean_ctor_set(v___x_3983_, 2, v___f_3978_);
    leanh::lean_ctor_set(v___x_3983_, 3, v___f_3979_);
    leanh::lean_ctor_set(v___x_3983_, 4, v___f_3980_);
    v___x_3984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3984_, 0, v___x_3983_);
    leanh::lean_ctor_set(v___x_3984_, 1, v___f_3981_);
    leanh::lean_inc_ref_n(v___x_3984_, 6);
    v___f_3985_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3985_, 0, v___x_3984_);
    v___f_3986_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3986_, 0, v___x_3984_);
    v___f_3987_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3987_, 0, v___x_3984_);
    v___f_3988_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3988_, 0, v___x_3984_);
    v___x_3989_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_3989_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3989_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3989_, 2, v___x_3984_);
    v___x_3990_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3990_, 0, v___x_3989_);
    leanh::lean_ctor_set(v___x_3990_, 1, v___f_3985_);
    v___x_3991_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_3991_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3991_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3991_, 2, v___x_3984_);
    v___x_3992_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3992_, 0, v___x_3990_);
    leanh::lean_ctor_set(v___x_3992_, 1, v___x_3991_);
    leanh::lean_ctor_set(v___x_3992_, 2, v___f_3986_);
    leanh::lean_ctor_set(v___x_3992_, 3, v___f_3987_);
    leanh::lean_ctor_set(v___x_3992_, 4, v___f_3988_);
    v___x_3993_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_3993_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3993_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3993_, 2, v___x_3984_);
    v___x_3994_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3994_, 0, v___x_3992_);
    leanh::lean_ctor_set(v___x_3994_, 1, v___x_3993_);
    v___x_3995_ = l_ReaderT_instMonad___redArg(v___x_3994_);
    leanh::lean_inc_ref_n(v___x_3995_, 6);
    v___f_3996_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3996_, 0, v___x_3995_);
    v___f_3997_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3997_, 0, v___x_3995_);
    v___f_3998_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3998_, 0, v___x_3995_);
    v___f_3999_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3999_, 0, v___x_3995_);
    v___x_4000_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_4000_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4000_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4000_, 2, v___x_3995_);
    v___x_4001_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4001_, 0, v___x_4000_);
    leanh::lean_ctor_set(v___x_4001_, 1, v___f_3996_);
    v___x_4002_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_4002_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4002_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4002_, 2, v___x_3995_);
    v___x_4003_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_4003_, 0, v___x_4001_);
    leanh::lean_ctor_set(v___x_4003_, 1, v___x_4002_);
    leanh::lean_ctor_set(v___x_4003_, 2, v___f_3997_);
    leanh::lean_ctor_set(v___x_4003_, 3, v___f_3998_);
    leanh::lean_ctor_set(v___x_4003_, 4, v___f_3999_);
    v___x_4004_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_4004_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4004_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4004_, 2, v___x_3995_);
    v___x_4005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4005_, 0, v___x_4003_);
    leanh::lean_ctor_set(v___x_4005_, 1, v___x_4004_);
    v___x_4006_ = l_Lean_instInhabitedExpr;
    v___x_4007_ = l_instInhabitedOfMonad___redArg(v___x_4005_, v___x_4006_);
    v___x_21471__overap_4008_ = lean_panic_fn_borrowed(v___x_4007_, v_msg_3971_);
    leanh::lean_dec(v___x_4007_);
    v___x_4009_ = leanh::lean_box((v___y_3973_) as usize);
    v___x_4010_ = leanh::lean_apply_3(
        v___x_21471__overap_4008_,
        v___y_3972_,
        v___x_4009_,
        v___y_3974_,
    );
    return v___x_4010_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10___boxed(
    mut v_msg_4011_: *mut leanh::LeanObject,
    mut v___y_4012_: *mut leanh::LeanObject,
    mut v___y_4013_: *mut leanh::LeanObject,
    mut v___y_4014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_21993__boxed_4015_: u8 = 0;
    let mut v_res_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_21993__boxed_4015_ = (leanh::lean_unbox(v___y_4013_) as u8);
    v_res_4016_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v_msg_4011_, v___y_4012_, v___y_21993__boxed_4015_, v___y_4014_);
    return v_res_4016_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(
    mut v_f_4017_: *mut leanh::LeanObject,
    mut v_a_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: u8,
    mut v___y_4021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_4020_ == 0 {
                    v___y_4023_ = v___y_4019_;
                    v___y_4024_ = v___y_4021_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_f_4017_);
                    v___x_4037_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_f_4017_,
                        v___y_4020_,
                        v___y_4021_,
                    );
                    v_snd_4038_ = leanh::lean_ctor_get(v___x_4037_, 1);
                    leanh::lean_inc(v_snd_4038_);
                    leanh::lean_dec_ref(v___x_4037_);
                    leanh::lean_inc_ref(v_a_4018_);
                    v___x_4039_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_a_4018_,
                        v___y_4020_,
                        v_snd_4038_,
                    );
                    v_snd_4040_ = leanh::lean_ctor_get(v___x_4039_, 1);
                    leanh::lean_inc(v_snd_4040_);
                    leanh::lean_dec_ref(v___x_4039_);
                    v___y_4023_ = v___y_4019_;
                    v___y_4024_ = v_snd_4040_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4025_ = l_Lean_Expr_app___override(v_f_4017_, v_a_4018_);
                v___x_4026_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_4025_, v___y_4024_);
                v_fst_4027_ = leanh::lean_ctor_get(v___x_4026_, 0);
                v_snd_4028_ = leanh::lean_ctor_get(v___x_4026_, 1);
                v_isSharedCheck_4036_ = (!leanh::lean_is_exclusive(v___x_4026_)) as u8;
                if v_isSharedCheck_4036_ == 0 {
                    v___x_4030_ = v___x_4026_;
                    v_isShared_4031_ = v_isSharedCheck_4036_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4028_);
                    leanh::lean_inc(v_fst_4027_);
                    leanh::lean_dec(v___x_4026_);
                    v___x_4030_ = leanh::lean_box(0);
                    v_isShared_4031_ = v_isSharedCheck_4036_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4031_ == 0 {
                    leanh::lean_ctor_set(v___x_4030_, 1, v___y_4023_);
                    v___x_4033_ = v___x_4030_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_fst_4027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___y_4023_);
                    v___x_4033_ = v_reuseFailAlloc_4035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4034_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4034_, 0, v___x_4033_);
                leanh::lean_ctor_set(v___x_4034_, 1, v_snd_4028_);
                return v___x_4034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4___boxed(
    mut v_f_4041_: *mut leanh::LeanObject,
    mut v_a_4042_: *mut leanh::LeanObject,
    mut v___y_4043_: *mut leanh::LeanObject,
    mut v___y_4044_: *mut leanh::LeanObject,
    mut v___y_4045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_22072__boxed_4046_: u8 = 0;
    let mut v_res_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_22072__boxed_4046_ = (leanh::lean_unbox(v___y_4044_) as u8);
    v_res_4047_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_f_4041_, v_a_4042_, v___y_4043_, v___y_22072__boxed_4046_, v___y_4045_);
    return v_res_4047_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(
    mut v_x_4048_: *mut leanh::LeanObject,
    mut v_bi_4049_: u8,
    mut v_t_4050_: *mut leanh::LeanObject,
    mut v_b_4051_: *mut leanh::LeanObject,
    mut v___y_4052_: *mut leanh::LeanObject,
    mut v___y_4053_: u8,
    mut v___y_4054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4064_: u8 = 0;
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4069_: u8 = 0;
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_4053_ == 0 {
                    v___y_4056_ = v___y_4052_;
                    v___y_4057_ = v___y_4054_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_t_4050_);
                    v___x_4070_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_4050_,
                        v___y_4053_,
                        v___y_4054_,
                    );
                    v_snd_4071_ = leanh::lean_ctor_get(v___x_4070_, 1);
                    leanh::lean_inc(v_snd_4071_);
                    leanh::lean_dec_ref(v___x_4070_);
                    leanh::lean_inc_ref(v_b_4051_);
                    v___x_4072_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_4051_,
                        v___y_4053_,
                        v_snd_4071_,
                    );
                    v_snd_4073_ = leanh::lean_ctor_get(v___x_4072_, 1);
                    leanh::lean_inc(v_snd_4073_);
                    leanh::lean_dec_ref(v___x_4072_);
                    v___y_4056_ = v___y_4052_;
                    v___y_4057_ = v_snd_4073_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4058_ =
                    l_Lean_Expr_forallE___override(v_x_4048_, v_t_4050_, v_b_4051_, v_bi_4049_);
                v___x_4059_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_4058_, v___y_4057_);
                v_fst_4060_ = leanh::lean_ctor_get(v___x_4059_, 0);
                v_snd_4061_ = leanh::lean_ctor_get(v___x_4059_, 1);
                v_isSharedCheck_4069_ = (!leanh::lean_is_exclusive(v___x_4059_)) as u8;
                if v_isSharedCheck_4069_ == 0 {
                    v___x_4063_ = v___x_4059_;
                    v_isShared_4064_ = v_isSharedCheck_4069_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4061_);
                    leanh::lean_inc(v_fst_4060_);
                    leanh::lean_dec(v___x_4059_);
                    v___x_4063_ = leanh::lean_box(0);
                    v_isShared_4064_ = v_isSharedCheck_4069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4064_ == 0 {
                    leanh::lean_ctor_set(v___x_4063_, 1, v___y_4056_);
                    v___x_4066_ = v___x_4063_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_fst_4060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 1, v___y_4056_);
                    v___x_4066_ = v_reuseFailAlloc_4068_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4067_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4067_, 0, v___x_4066_);
                leanh::lean_ctor_set(v___x_4067_, 1, v_snd_4061_);
                return v___x_4067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6___boxed(
    mut v_x_4074_: *mut leanh::LeanObject,
    mut v_bi_4075_: *mut leanh::LeanObject,
    mut v_t_4076_: *mut leanh::LeanObject,
    mut v_b_4077_: *mut leanh::LeanObject,
    mut v___y_4078_: *mut leanh::LeanObject,
    mut v___y_4079_: *mut leanh::LeanObject,
    mut v___y_4080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4081_: u8 = 0;
    let mut v___y_22121__boxed_4082_: u8 = 0;
    let mut v_res_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4081_ = (leanh::lean_unbox(v_bi_4075_) as u8);
    v___y_22121__boxed_4082_ = (leanh::lean_unbox(v___y_4079_) as u8);
    v_res_4083_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_x_4074_, v_bi_boxed_4081_, v_t_4076_, v_b_4077_, v___y_4078_, v___y_22121__boxed_4082_, v___y_4080_);
    return v_res_4083_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(
    mut v_x_4084_: *mut leanh::LeanObject,
    mut v_t_4085_: *mut leanh::LeanObject,
    mut v_v_4086_: *mut leanh::LeanObject,
    mut v_b_4087_: *mut leanh::LeanObject,
    mut v_nondep_4088_: u8,
    mut v___y_4089_: *mut leanh::LeanObject,
    mut v___y_4090_: u8,
    mut v___y_4091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_4090_ == 0 {
                    v___y_4093_ = v___y_4089_;
                    v___y_4094_ = v___y_4091_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_t_4085_);
                    v___x_4107_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_4085_,
                        v___y_4090_,
                        v___y_4091_,
                    );
                    v_snd_4108_ = leanh::lean_ctor_get(v___x_4107_, 1);
                    leanh::lean_inc(v_snd_4108_);
                    leanh::lean_dec_ref(v___x_4107_);
                    leanh::lean_inc_ref(v_v_4086_);
                    v___x_4109_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_v_4086_,
                        v___y_4090_,
                        v_snd_4108_,
                    );
                    v_snd_4110_ = leanh::lean_ctor_get(v___x_4109_, 1);
                    leanh::lean_inc(v_snd_4110_);
                    leanh::lean_dec_ref(v___x_4109_);
                    leanh::lean_inc_ref(v_b_4087_);
                    v___x_4111_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_4087_,
                        v___y_4090_,
                        v_snd_4110_,
                    );
                    v_snd_4112_ = leanh::lean_ctor_get(v___x_4111_, 1);
                    leanh::lean_inc(v_snd_4112_);
                    leanh::lean_dec_ref(v___x_4111_);
                    v___y_4093_ = v___y_4089_;
                    v___y_4094_ = v_snd_4112_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4095_ = l_Lean_Expr_letE___override(
                    v_x_4084_,
                    v_t_4085_,
                    v_v_4086_,
                    v_b_4087_,
                    v_nondep_4088_,
                );
                v___x_4096_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_4095_, v___y_4094_);
                v_fst_4097_ = leanh::lean_ctor_get(v___x_4096_, 0);
                v_snd_4098_ = leanh::lean_ctor_get(v___x_4096_, 1);
                v_isSharedCheck_4106_ = (!leanh::lean_is_exclusive(v___x_4096_)) as u8;
                if v_isSharedCheck_4106_ == 0 {
                    v___x_4100_ = v___x_4096_;
                    v_isShared_4101_ = v_isSharedCheck_4106_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4098_);
                    leanh::lean_inc(v_fst_4097_);
                    leanh::lean_dec(v___x_4096_);
                    v___x_4100_ = leanh::lean_box(0);
                    v_isShared_4101_ = v_isSharedCheck_4106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4101_ == 0 {
                    leanh::lean_ctor_set(v___x_4100_, 1, v___y_4093_);
                    v___x_4103_ = v___x_4100_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4105_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_fst_4097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 1, v___y_4093_);
                    v___x_4103_ = v_reuseFailAlloc_4105_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4104_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4104_, 0, v___x_4103_);
                leanh::lean_ctor_set(v___x_4104_, 1, v_snd_4098_);
                return v___x_4104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7___boxed(
    mut v_x_4113_: *mut leanh::LeanObject,
    mut v_t_4114_: *mut leanh::LeanObject,
    mut v_v_4115_: *mut leanh::LeanObject,
    mut v_b_4116_: *mut leanh::LeanObject,
    mut v_nondep_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
    mut v___y_4120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_4121_: u8 = 0;
    let mut v___y_22170__boxed_4122_: u8 = 0;
    let mut v_res_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_4121_ = (leanh::lean_unbox(v_nondep_4117_) as u8);
    v___y_22170__boxed_4122_ = (leanh::lean_unbox(v___y_4119_) as u8);
    v_res_4123_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_x_4113_, v_t_4114_, v_v_4115_, v_b_4116_, v_nondep_boxed_4121_, v___y_4118_, v___y_22170__boxed_4122_, v___y_4120_);
    return v_res_4123_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(
    mut v_a_4124_: *mut leanh::LeanObject,
    mut v_x_4125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4131_: u8 = 0;
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: u8 = 0;
    let mut v___x_4139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4125_) == 0 {
                    v___x_4126_ = leanh::lean_box(0);
                    return v___x_4126_;
                } else {
                    v_key_4127_ = leanh::lean_ctor_get(v_x_4125_, 0);
                    v_value_4128_ = leanh::lean_ctor_get(v_x_4125_, 1);
                    v_tail_4129_ = leanh::lean_ctor_get(v_x_4125_, 2);
                    v_fst_4134_ = leanh::lean_ctor_get(v_key_4127_, 0);
                    v_snd_4135_ = leanh::lean_ctor_get(v_key_4127_, 1);
                    v_fst_4136_ = leanh::lean_ctor_get(v_a_4124_, 0);
                    v_snd_4137_ = leanh::lean_ctor_get(v_a_4124_, 1);
                    v___x_4138_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_4134_,
                            v_fst_4136_,
                        );
                    if v___x_4138_ == 0 {
                        v___y_4131_ = v___x_4138_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4139_ = lean_nat_dec_eq(v_snd_4135_, v_snd_4137_);
                        v___y_4131_ = v___x_4139_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_4131_ == 0 {
                    v_x_4125_ = v_tail_4129_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_value_4128_);
                    v___x_4133_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4133_, 0, v_value_4128_);
                    return v___x_4133_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg___boxed(
    mut v_a_4140_: *mut leanh::LeanObject,
    mut v_x_4141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4142_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_4140_, v_x_4141_);
    leanh::lean_dec(v_x_4141_);
    leanh::lean_dec_ref(v_a_4140_);
    return v_res_4142_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(
    mut v_m_4143_: *mut leanh::LeanObject,
    mut v_a_4144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: u64 = 0;
    let mut v___x_4150_: u64 = 0;
    let mut v___x_4151_: u64 = 0;
    let mut v___x_4152_: u64 = 0;
    let mut v___x_4153_: u64 = 0;
    let mut v_fold_4154_: u64 = 0;
    let mut v___x_4155_: u64 = 0;
    let mut v___x_4156_: u64 = 0;
    let mut v___x_4157_: u64 = 0;
    let mut v___x_4158_: usize = 0;
    let mut v___x_4159_: usize = 0;
    let mut v___x_4160_: usize = 0;
    let mut v___x_4161_: usize = 0;
    let mut v___x_4162_: usize = 0;
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4145_ = leanh::lean_ctor_get(v_m_4143_, 1);
    v_fst_4146_ = leanh::lean_ctor_get(v_a_4144_, 0);
    v_snd_4147_ = leanh::lean_ctor_get(v_a_4144_, 1);
    v___x_4148_ = lean_array_get_size(v_buckets_4145_);
    v___x_4149_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4146_);
    v___x_4150_ = lean_uint64_of_nat(v_snd_4147_);
    v___x_4151_ = lean_uint64_mix_hash(v___x_4149_, v___x_4150_);
    v___x_4152_ = 32u64;
    v___x_4153_ = lean_uint64_shift_right(v___x_4151_, v___x_4152_);
    v_fold_4154_ = lean_uint64_xor(v___x_4151_, v___x_4153_);
    v___x_4155_ = 16u64;
    v___x_4156_ = lean_uint64_shift_right(v_fold_4154_, v___x_4155_);
    v___x_4157_ = lean_uint64_xor(v_fold_4154_, v___x_4156_);
    v___x_4158_ = lean_uint64_to_usize(v___x_4157_);
    v___x_4159_ = lean_usize_of_nat(v___x_4148_);
    v___x_4160_ = 1usize;
    v___x_4161_ = lean_usize_sub(v___x_4159_, v___x_4160_);
    v___x_4162_ = lean_usize_land(v___x_4158_, v___x_4161_);
    v___x_4163_ = lean_array_uget_borrowed(v_buckets_4145_, v___x_4162_);
    v___x_4164_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_4144_, v___x_4163_);
    return v___x_4164_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg___boxed(
    mut v_m_4165_: *mut leanh::LeanObject,
    mut v_a_4166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4167_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_4165_, v_a_4166_);
    leanh::lean_dec_ref(v_a_4166_);
    leanh::lean_dec_ref(v_m_4165_);
    return v_res_4167_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(
    mut v_d_4168_: *mut leanh::LeanObject,
    mut v_e_4169_: *mut leanh::LeanObject,
    mut v___y_4170_: *mut leanh::LeanObject,
    mut v___y_4171_: u8,
    mut v___y_4172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4182_: u8 = 0;
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4187_: u8 = 0;
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_4171_ == 0 {
                    v___y_4174_ = v___y_4170_;
                    v___y_4175_ = v___y_4172_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_e_4169_);
                    v___x_4188_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_e_4169_,
                        v___y_4171_,
                        v___y_4172_,
                    );
                    v_snd_4189_ = leanh::lean_ctor_get(v___x_4188_, 1);
                    leanh::lean_inc(v_snd_4189_);
                    leanh::lean_dec_ref(v___x_4188_);
                    v___y_4174_ = v___y_4170_;
                    v___y_4175_ = v_snd_4189_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4176_ = l_Lean_Expr_mdata___override(v_d_4168_, v_e_4169_);
                v___x_4177_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_4176_, v___y_4175_);
                v_fst_4178_ = leanh::lean_ctor_get(v___x_4177_, 0);
                v_snd_4179_ = leanh::lean_ctor_get(v___x_4177_, 1);
                v_isSharedCheck_4187_ = (!leanh::lean_is_exclusive(v___x_4177_)) as u8;
                if v_isSharedCheck_4187_ == 0 {
                    v___x_4181_ = v___x_4177_;
                    v_isShared_4182_ = v_isSharedCheck_4187_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4179_);
                    leanh::lean_inc(v_fst_4178_);
                    leanh::lean_dec(v___x_4177_);
                    v___x_4181_ = leanh::lean_box(0);
                    v_isShared_4182_ = v_isSharedCheck_4187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4182_ == 0 {
                    leanh::lean_ctor_set(v___x_4181_, 1, v___y_4174_);
                    v___x_4184_ = v___x_4181_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_fst_4178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4186_, 1, v___y_4174_);
                    v___x_4184_ = v_reuseFailAlloc_4186_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4185_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4185_, 0, v___x_4184_);
                leanh::lean_ctor_set(v___x_4185_, 1, v_snd_4179_);
                return v___x_4185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8___boxed(
    mut v_d_4190_: *mut leanh::LeanObject,
    mut v_e_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
    mut v___y_4193_: *mut leanh::LeanObject,
    mut v___y_4194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_22293__boxed_4195_: u8 = 0;
    let mut v_res_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_22293__boxed_4195_ = (leanh::lean_unbox(v___y_4193_) as u8);
    v_res_4196_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_d_4190_, v_e_4191_, v___y_4192_, v___y_22293__boxed_4195_, v___y_4194_);
    return v_res_4196_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_4197_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4201_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3;
    v___x_4202_ = leanh::lean_unsigned_to_nat(12);
    v___x_4203_ = leanh::lean_unsigned_to_nat(234);
    v___x_4204_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2;
    v___x_4205_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1;
    v___x_4206_ = l_mkPanicMessageWithDecl(
        v___x_4205_,
        v___x_4204_,
        v___x_4203_,
        v___x_4202_,
        v___x_4201_,
    );
    return v___x_4206_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4210_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2;
    v___x_4211_ = leanh::lean_unsigned_to_nat(67);
    v___x_4212_ = leanh::lean_unsigned_to_nat(35);
    v___x_4213_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1;
    v___x_4214_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0;
    v___x_4215_ = l_mkPanicMessageWithDecl(
        v___x_4214_,
        v___x_4213_,
        v___x_4212_,
        v___x_4211_,
        v___x_4210_,
    );
    return v___x_4215_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(
    mut v_n_4216_: *mut leanh::LeanObject,
    mut v_varDeps_4217_: *mut leanh::LeanObject,
    mut v_xs_4218_: *mut leanh::LeanObject,
    mut v_e_4219_: *mut leanh::LeanObject,
    mut v_offset_4220_: *mut leanh::LeanObject,
    mut v_a_4221_: *mut leanh::LeanObject,
    mut v_a_4222_: u8,
    mut v_a_4223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4236_: u8 = 0;
    let mut v_fst_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v___y_4243_: u8 = 0;
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: u8 = 0;
    let mut v_isSharedCheck_4253_: u8 = 0;
    let mut v_isSharedCheck_4254_: u8 = 0;
    let mut v_binderName_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4258_: u8 = 0;
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4271_: u8 = 0;
    let mut v_fst_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v___y_4278_: u8 = 0;
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: u8 = 0;
    let mut v___x_4287_: u8 = 0;
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_isSharedCheck_4289_: u8 = 0;
    let mut v_binderName_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4293_: u8 = 0;
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v_fst_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4311_: u8 = 0;
    let mut v___y_4313_: u8 = 0;
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: u8 = 0;
    let mut v___x_4322_: u8 = 0;
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v_isSharedCheck_4324_: u8 = 0;
    let mut v_declName_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_4329_: u8 = 0;
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4347_: u8 = 0;
    let mut v_fst_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4352_: u8 = 0;
    let mut v___y_4354_: u8 = 0;
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4365_: u8 = 0;
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut v_isSharedCheck_4367_: u8 = 0;
    let mut v_data_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4375_: u8 = 0;
    let mut v_fst_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4381_: u8 = 0;
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut v_typeName_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4399_: u8 = 0;
    let mut v_fst_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v___x_4405_: u8 = 0;
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_4219_) {
                5 => {
                    v_fn_4224_ = leanh::lean_ctor_get(v_e_4219_, 0);
                    v_arg_4225_ = leanh::lean_ctor_get(v_e_4219_, 1);
                    leanh::lean_inc(v_offset_4220_);
                    leanh::lean_inc_ref(v_fn_4224_);
                    v___x_4226_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_fn_4224_, v_offset_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
                    v_fst_4227_ = leanh::lean_ctor_get(v___x_4226_, 0);
                    leanh::lean_inc(v_fst_4227_);
                    v_snd_4228_ = leanh::lean_ctor_get(v___x_4226_, 1);
                    leanh::lean_inc(v_snd_4228_);
                    leanh::lean_dec_ref(v___x_4226_);
                    v_fst_4229_ = leanh::lean_ctor_get(v_fst_4227_, 0);
                    leanh::lean_inc(v_fst_4229_);
                    v_snd_4230_ = leanh::lean_ctor_get(v_fst_4227_, 1);
                    leanh::lean_inc(v_snd_4230_);
                    leanh::lean_dec(v_fst_4227_);
                    leanh::lean_inc_ref(v_arg_4225_);
                    v___x_4231_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_arg_4225_, v_offset_4220_, v_snd_4230_, v_a_4222_, v_snd_4228_);
                    v_fst_4232_ = leanh::lean_ctor_get(v___x_4231_, 0);
                    v_snd_4233_ = leanh::lean_ctor_get(v___x_4231_, 1);
                    v_isSharedCheck_4254_ = (!leanh::lean_is_exclusive(v___x_4231_)) as u8;
                    if v_isSharedCheck_4254_ == 0 {
                        v___x_4235_ = v___x_4231_;
                        v_isShared_4236_ = v_isSharedCheck_4254_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4233_);
                        leanh::lean_inc(v_fst_4232_);
                        leanh::lean_dec(v___x_4231_);
                        v___x_4235_ = leanh::lean_box(0);
                        v_isShared_4236_ = v_isSharedCheck_4254_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_4255_ = leanh::lean_ctor_get(v_e_4219_, 0);
                    v_binderType_4256_ = leanh::lean_ctor_get(v_e_4219_, 1);
                    v_body_4257_ = leanh::lean_ctor_get(v_e_4219_, 2);
                    v_binderInfo_4258_ = leanh::lean_ctor_get_uint8(
                        v_e_4219_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc(v_offset_4220_);
                    leanh::lean_inc_ref(v_binderType_4256_);
                    v___x_4259_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_binderType_4256_, v_offset_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
                    v_fst_4260_ = leanh::lean_ctor_get(v___x_4259_, 0);
                    leanh::lean_inc(v_fst_4260_);
                    v_snd_4261_ = leanh::lean_ctor_get(v___x_4259_, 1);
                    leanh::lean_inc(v_snd_4261_);
                    leanh::lean_dec_ref(v___x_4259_);
                    v_fst_4262_ = leanh::lean_ctor_get(v_fst_4260_, 0);
                    leanh::lean_inc(v_fst_4262_);
                    v_snd_4263_ = leanh::lean_ctor_get(v_fst_4260_, 1);
                    leanh::lean_inc(v_snd_4263_);
                    leanh::lean_dec(v_fst_4260_);
                    v___x_4264_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4265_ = lean_nat_add(v_offset_4220_, v___x_4264_);
                    leanh::lean_dec(v_offset_4220_);
                    leanh::lean_inc_ref(v_body_4257_);
                    v___x_4266_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_body_4257_, v___x_4265_, v_snd_4263_, v_a_4222_, v_snd_4261_);
                    v_fst_4267_ = leanh::lean_ctor_get(v___x_4266_, 0);
                    v_snd_4268_ = leanh::lean_ctor_get(v___x_4266_, 1);
                    v_isSharedCheck_4289_ = (!leanh::lean_is_exclusive(v___x_4266_)) as u8;
                    if v_isSharedCheck_4289_ == 0 {
                        v___x_4270_ = v___x_4266_;
                        v_isShared_4271_ = v_isSharedCheck_4289_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4268_);
                        leanh::lean_inc(v_fst_4267_);
                        leanh::lean_dec(v___x_4266_);
                        v___x_4270_ = leanh::lean_box(0);
                        v_isShared_4271_ = v_isSharedCheck_4289_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_4290_ = leanh::lean_ctor_get(v_e_4219_, 0);
                    v_binderType_4291_ = leanh::lean_ctor_get(v_e_4219_, 1);
                    v_body_4292_ = leanh::lean_ctor_get(v_e_4219_, 2);
                    v_binderInfo_4293_ = leanh::lean_ctor_get_uint8(
                        v_e_4219_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc(v_offset_4220_);
                    leanh::lean_inc_ref(v_binderType_4291_);
                    v___x_4294_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_binderType_4291_, v_offset_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
                    v_fst_4295_ = leanh::lean_ctor_get(v___x_4294_, 0);
                    leanh::lean_inc(v_fst_4295_);
                    v_snd_4296_ = leanh::lean_ctor_get(v___x_4294_, 1);
                    leanh::lean_inc(v_snd_4296_);
                    leanh::lean_dec_ref(v___x_4294_);
                    v_fst_4297_ = leanh::lean_ctor_get(v_fst_4295_, 0);
                    leanh::lean_inc(v_fst_4297_);
                    v_snd_4298_ = leanh::lean_ctor_get(v_fst_4295_, 1);
                    leanh::lean_inc(v_snd_4298_);
                    leanh::lean_dec(v_fst_4295_);
                    v___x_4299_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4300_ = lean_nat_add(v_offset_4220_, v___x_4299_);
                    leanh::lean_dec(v_offset_4220_);
                    leanh::lean_inc_ref(v_body_4292_);
                    v___x_4301_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_body_4292_, v___x_4300_, v_snd_4298_, v_a_4222_, v_snd_4296_);
                    v_fst_4302_ = leanh::lean_ctor_get(v___x_4301_, 0);
                    v_snd_4303_ = leanh::lean_ctor_get(v___x_4301_, 1);
                    v_isSharedCheck_4324_ = (!leanh::lean_is_exclusive(v___x_4301_)) as u8;
                    if v_isSharedCheck_4324_ == 0 {
                        v___x_4305_ = v___x_4301_;
                        v_isShared_4306_ = v_isSharedCheck_4324_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4303_);
                        leanh::lean_inc(v_fst_4302_);
                        leanh::lean_dec(v___x_4301_);
                        v___x_4305_ = leanh::lean_box(0);
                        v_isShared_4306_ = v_isSharedCheck_4324_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_4325_ = leanh::lean_ctor_get(v_e_4219_, 0);
                    v_type_4326_ = leanh::lean_ctor_get(v_e_4219_, 1);
                    v_value_4327_ = leanh::lean_ctor_get(v_e_4219_, 2);
                    v_body_4328_ = leanh::lean_ctor_get(v_e_4219_, 3);
                    v_nondep_4329_ = leanh::lean_ctor_get_uint8(
                        v_e_4219_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc_n(v_offset_4220_, 2);
                    leanh::lean_inc_ref(v_type_4326_);
                    v___x_4330_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_type_4326_, v_offset_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
                    v_fst_4331_ = leanh::lean_ctor_get(v___x_4330_, 0);
                    leanh::lean_inc(v_fst_4331_);
                    v_snd_4332_ = leanh::lean_ctor_get(v___x_4330_, 1);
                    leanh::lean_inc(v_snd_4332_);
                    leanh::lean_dec_ref(v___x_4330_);
                    v_fst_4333_ = leanh::lean_ctor_get(v_fst_4331_, 0);
                    leanh::lean_inc(v_fst_4333_);
                    v_snd_4334_ = leanh::lean_ctor_get(v_fst_4331_, 1);
                    leanh::lean_inc(v_snd_4334_);
                    leanh::lean_dec(v_fst_4331_);
                    leanh::lean_inc_ref(v_value_4327_);
                    v___x_4335_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_value_4327_, v_offset_4220_, v_snd_4334_, v_a_4222_, v_snd_4332_);
                    v_fst_4336_ = leanh::lean_ctor_get(v___x_4335_, 0);
                    leanh::lean_inc(v_fst_4336_);
                    v_snd_4337_ = leanh::lean_ctor_get(v___x_4335_, 1);
                    leanh::lean_inc(v_snd_4337_);
                    leanh::lean_dec_ref(v___x_4335_);
                    v_fst_4338_ = leanh::lean_ctor_get(v_fst_4336_, 0);
                    leanh::lean_inc(v_fst_4338_);
                    v_snd_4339_ = leanh::lean_ctor_get(v_fst_4336_, 1);
                    leanh::lean_inc(v_snd_4339_);
                    leanh::lean_dec(v_fst_4336_);
                    v___x_4340_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4341_ = lean_nat_add(v_offset_4220_, v___x_4340_);
                    leanh::lean_dec(v_offset_4220_);
                    leanh::lean_inc_ref(v_body_4328_);
                    v___x_4342_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_body_4328_, v___x_4341_, v_snd_4339_, v_a_4222_, v_snd_4337_);
                    v_fst_4343_ = leanh::lean_ctor_get(v___x_4342_, 0);
                    v_snd_4344_ = leanh::lean_ctor_get(v___x_4342_, 1);
                    v_isSharedCheck_4367_ = (!leanh::lean_is_exclusive(v___x_4342_)) as u8;
                    if v_isSharedCheck_4367_ == 0 {
                        v___x_4346_ = v___x_4342_;
                        v_isShared_4347_ = v_isSharedCheck_4367_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4344_);
                        leanh::lean_inc(v_fst_4343_);
                        leanh::lean_dec(v___x_4342_);
                        v___x_4346_ = leanh::lean_box(0);
                        v_isShared_4347_ = v_isSharedCheck_4367_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_4368_ = leanh::lean_ctor_get(v_e_4219_, 0);
                    v_expr_4369_ = leanh::lean_ctor_get(v_e_4219_, 1);
                    leanh::lean_inc_ref(v_expr_4369_);
                    v___x_4370_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_expr_4369_, v_offset_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
                    v_fst_4371_ = leanh::lean_ctor_get(v___x_4370_, 0);
                    v_snd_4372_ = leanh::lean_ctor_get(v___x_4370_, 1);
                    v_isSharedCheck_4390_ = (!leanh::lean_is_exclusive(v___x_4370_)) as u8;
                    if v_isSharedCheck_4390_ == 0 {
                        v___x_4374_ = v___x_4370_;
                        v_isShared_4375_ = v_isSharedCheck_4390_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4372_);
                        leanh::lean_inc(v_fst_4371_);
                        leanh::lean_dec(v___x_4370_);
                        v___x_4374_ = leanh::lean_box(0);
                        v_isShared_4375_ = v_isSharedCheck_4390_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_4391_ = leanh::lean_ctor_get(v_e_4219_, 0);
                    v_idx_4392_ = leanh::lean_ctor_get(v_e_4219_, 1);
                    v_struct_4393_ = leanh::lean_ctor_get(v_e_4219_, 2);
                    leanh::lean_inc_ref(v_struct_4393_);
                    v___x_4394_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4216_, v_varDeps_4217_, v_xs_4218_, v_struct_4393_, v_offset_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
                    v_fst_4395_ = leanh::lean_ctor_get(v___x_4394_, 0);
                    v_snd_4396_ = leanh::lean_ctor_get(v___x_4394_, 1);
                    v_isSharedCheck_4414_ = (!leanh::lean_is_exclusive(v___x_4394_)) as u8;
                    if v_isSharedCheck_4414_ == 0 {
                        v___x_4398_ = v___x_4394_;
                        v_isShared_4399_ = v_isSharedCheck_4414_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4396_);
                        leanh::lean_inc(v_fst_4395_);
                        leanh::lean_dec(v___x_4394_);
                        v___x_4398_ = leanh::lean_box(0);
                        v_isShared_4399_ = v_isSharedCheck_4414_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_offset_4220_);
                    leanh::lean_dec_ref(v_e_4219_);
                    v___x_4415_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3);
                    v___x_4416_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v___x_4415_, v_a_4221_, v_a_4222_, v_a_4223_);
                    return v___x_4416_;
                }
            },
            1 => {
                v_fst_4237_ = leanh::lean_ctor_get(v_fst_4232_, 0);
                v_snd_4238_ = leanh::lean_ctor_get(v_fst_4232_, 1);
                v_isSharedCheck_4253_ = (!leanh::lean_is_exclusive(v_fst_4232_)) as u8;
                if v_isSharedCheck_4253_ == 0 {
                    v___x_4240_ = v_fst_4232_;
                    v_isShared_4241_ = v_isSharedCheck_4253_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4238_);
                    leanh::lean_inc(v_fst_4237_);
                    leanh::lean_dec(v_fst_4232_);
                    v___x_4240_ = leanh::lean_box(0);
                    v_isShared_4241_ = v_isSharedCheck_4253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4251_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fn_4224_,
                        v_fst_4229_,
                    );
                if v___x_4251_ == 0 {
                    v___y_4243_ = v___x_4251_;
                    state = 3;
                    continue;
                } else {
                    v___x_4252_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_4225_,
                            v_fst_4237_,
                        );
                    v___y_4243_ = v___x_4252_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_4243_ == 0 {
                    leanh::lean_del_object(v___x_4240_);
                    leanh::lean_del_object(v___x_4235_);
                    leanh::lean_dec_ref_known(v_e_4219_, 2);
                    v___x_4244_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_fst_4229_, v_fst_4237_, v_snd_4238_, v_a_4222_, v_snd_4233_);
                    return v___x_4244_;
                } else {
                    leanh::lean_dec(v_fst_4237_);
                    leanh::lean_dec(v_fst_4229_);
                    if v_isShared_4241_ == 0 {
                        leanh::lean_ctor_set(v___x_4240_, 0, v_e_4219_);
                        v___x_4246_ = v___x_4240_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4250_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_e_4219_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4250_, 1, v_snd_4238_);
                        v___x_4246_ = v_reuseFailAlloc_4250_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4236_ == 0 {
                    leanh::lean_ctor_set(v___x_4235_, 0, v___x_4246_);
                    v___x_4248_ = v___x_4235_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4249_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_snd_4233_);
                    v___x_4248_ = v_reuseFailAlloc_4249_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4248_;
            }
            6 => {
                v_fst_4272_ = leanh::lean_ctor_get(v_fst_4267_, 0);
                v_snd_4273_ = leanh::lean_ctor_get(v_fst_4267_, 1);
                v_isSharedCheck_4288_ = (!leanh::lean_is_exclusive(v_fst_4267_)) as u8;
                if v_isSharedCheck_4288_ == 0 {
                    v___x_4275_ = v_fst_4267_;
                    v_isShared_4276_ = v_isSharedCheck_4288_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4273_);
                    leanh::lean_inc(v_fst_4272_);
                    leanh::lean_dec(v_fst_4267_);
                    v___x_4275_ = leanh::lean_box(0);
                    v_isShared_4276_ = v_isSharedCheck_4288_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4286_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_4256_,
                        v_fst_4262_,
                    );
                if v___x_4286_ == 0 {
                    v___y_4278_ = v___x_4286_;
                    state = 8;
                    continue;
                } else {
                    v___x_4287_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_4257_,
                            v_fst_4272_,
                        );
                    v___y_4278_ = v___x_4287_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_4278_ == 0 {
                    leanh::lean_inc(v_binderName_4255_);
                    leanh::lean_del_object(v___x_4275_);
                    leanh::lean_del_object(v___x_4270_);
                    leanh::lean_dec_ref_known(v_e_4219_, 3);
                    v___x_4279_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_binderName_4255_, v_binderInfo_4258_, v_fst_4262_, v_fst_4272_, v_snd_4273_, v_a_4222_, v_snd_4268_);
                    return v___x_4279_;
                } else {
                    leanh::lean_dec(v_fst_4272_);
                    leanh::lean_dec(v_fst_4262_);
                    if v_isShared_4276_ == 0 {
                        leanh::lean_ctor_set(v___x_4275_, 0, v_e_4219_);
                        v___x_4281_ = v___x_4275_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4285_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_e_4219_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_snd_4273_);
                        v___x_4281_ = v_reuseFailAlloc_4285_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4271_ == 0 {
                    leanh::lean_ctor_set(v___x_4270_, 0, v___x_4281_);
                    v___x_4283_ = v___x_4270_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_snd_4268_);
                    v___x_4283_ = v_reuseFailAlloc_4284_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4283_;
            }
            11 => {
                v_fst_4307_ = leanh::lean_ctor_get(v_fst_4302_, 0);
                v_snd_4308_ = leanh::lean_ctor_get(v_fst_4302_, 1);
                v_isSharedCheck_4323_ = (!leanh::lean_is_exclusive(v_fst_4302_)) as u8;
                if v_isSharedCheck_4323_ == 0 {
                    v___x_4310_ = v_fst_4302_;
                    v_isShared_4311_ = v_isSharedCheck_4323_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4308_);
                    leanh::lean_inc(v_fst_4307_);
                    leanh::lean_dec(v_fst_4302_);
                    v___x_4310_ = leanh::lean_box(0);
                    v_isShared_4311_ = v_isSharedCheck_4323_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4321_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_4291_,
                        v_fst_4297_,
                    );
                if v___x_4321_ == 0 {
                    v___y_4313_ = v___x_4321_;
                    state = 13;
                    continue;
                } else {
                    v___x_4322_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_4292_,
                            v_fst_4307_,
                        );
                    v___y_4313_ = v___x_4322_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_4313_ == 0 {
                    leanh::lean_inc(v_binderName_4290_);
                    leanh::lean_del_object(v___x_4310_);
                    leanh::lean_del_object(v___x_4305_);
                    leanh::lean_dec_ref_known(v_e_4219_, 3);
                    v___x_4314_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_binderName_4290_, v_binderInfo_4293_, v_fst_4297_, v_fst_4307_, v_snd_4308_, v_a_4222_, v_snd_4303_);
                    return v___x_4314_;
                } else {
                    leanh::lean_dec(v_fst_4307_);
                    leanh::lean_dec(v_fst_4297_);
                    if v_isShared_4311_ == 0 {
                        leanh::lean_ctor_set(v___x_4310_, 0, v_e_4219_);
                        v___x_4316_ = v___x_4310_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4320_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_e_4219_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4320_, 1, v_snd_4308_);
                        v___x_4316_ = v_reuseFailAlloc_4320_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_4306_ == 0 {
                    leanh::lean_ctor_set(v___x_4305_, 0, v___x_4316_);
                    v___x_4318_ = v___x_4305_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_snd_4303_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4318_;
            }
            16 => {
                v_fst_4348_ = leanh::lean_ctor_get(v_fst_4343_, 0);
                v_snd_4349_ = leanh::lean_ctor_get(v_fst_4343_, 1);
                v_isSharedCheck_4366_ = (!leanh::lean_is_exclusive(v_fst_4343_)) as u8;
                if v_isSharedCheck_4366_ == 0 {
                    v___x_4351_ = v_fst_4343_;
                    v_isShared_4352_ = v_isSharedCheck_4366_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4349_);
                    leanh::lean_inc(v_fst_4348_);
                    leanh::lean_dec(v_fst_4343_);
                    v___x_4351_ = leanh::lean_box(0);
                    v_isShared_4352_ = v_isSharedCheck_4366_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4364_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_4326_,
                        v_fst_4333_,
                    );
                if v___x_4364_ == 0 {
                    v___y_4354_ = v___x_4364_;
                    state = 18;
                    continue;
                } else {
                    v___x_4365_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_value_4327_,
                            v_fst_4338_,
                        );
                    v___y_4354_ = v___x_4365_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_4354_ == 0 {
                    leanh::lean_inc(v_declName_4325_);
                    leanh::lean_del_object(v___x_4351_);
                    leanh::lean_del_object(v___x_4346_);
                    leanh::lean_dec_ref_known(v_e_4219_, 4);
                    v___x_4355_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_4325_, v_fst_4333_, v_fst_4338_, v_fst_4348_, v_nondep_4329_, v_snd_4349_, v_a_4222_, v_snd_4344_);
                    return v___x_4355_;
                } else {
                    v___x_4356_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_4328_,
                            v_fst_4348_,
                        );
                    if v___x_4356_ == 0 {
                        leanh::lean_inc(v_declName_4325_);
                        leanh::lean_del_object(v___x_4351_);
                        leanh::lean_del_object(v___x_4346_);
                        leanh::lean_dec_ref_known(v_e_4219_, 4);
                        v___x_4357_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_4325_, v_fst_4333_, v_fst_4338_, v_fst_4348_, v_nondep_4329_, v_snd_4349_, v_a_4222_, v_snd_4344_);
                        return v___x_4357_;
                    } else {
                        leanh::lean_dec(v_fst_4348_);
                        leanh::lean_dec(v_fst_4338_);
                        leanh::lean_dec(v_fst_4333_);
                        if v_isShared_4352_ == 0 {
                            leanh::lean_ctor_set(v___x_4351_, 0, v_e_4219_);
                            v___x_4359_ = v___x_4351_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_4363_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_e_4219_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_snd_4349_);
                            v___x_4359_ = v_reuseFailAlloc_4363_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_4347_ == 0 {
                    leanh::lean_ctor_set(v___x_4346_, 0, v___x_4359_);
                    v___x_4361_ = v___x_4346_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4362_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4362_, 1, v_snd_4344_);
                    v___x_4361_ = v_reuseFailAlloc_4362_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4361_;
            }
            21 => {
                v_fst_4376_ = leanh::lean_ctor_get(v_fst_4371_, 0);
                v_snd_4377_ = leanh::lean_ctor_get(v_fst_4371_, 1);
                v_isSharedCheck_4389_ = (!leanh::lean_is_exclusive(v_fst_4371_)) as u8;
                if v_isSharedCheck_4389_ == 0 {
                    v___x_4379_ = v_fst_4371_;
                    v_isShared_4380_ = v_isSharedCheck_4389_;
                    state = 22;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4377_);
                    leanh::lean_inc(v_fst_4376_);
                    leanh::lean_dec(v_fst_4371_);
                    v___x_4379_ = leanh::lean_box(0);
                    v_isShared_4380_ = v_isSharedCheck_4389_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_4381_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_expr_4369_,
                        v_fst_4376_,
                    );
                if v___x_4381_ == 0 {
                    leanh::lean_inc(v_data_4368_);
                    leanh::lean_del_object(v___x_4379_);
                    leanh::lean_del_object(v___x_4374_);
                    leanh::lean_dec_ref_known(v_e_4219_, 2);
                    v___x_4382_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_data_4368_, v_fst_4376_, v_snd_4377_, v_a_4222_, v_snd_4372_);
                    return v___x_4382_;
                } else {
                    leanh::lean_dec(v_fst_4376_);
                    if v_isShared_4380_ == 0 {
                        leanh::lean_ctor_set(v___x_4379_, 0, v_e_4219_);
                        v___x_4384_ = v___x_4379_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_4388_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_e_4219_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 1, v_snd_4377_);
                        v___x_4384_ = v_reuseFailAlloc_4388_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_4375_ == 0 {
                    leanh::lean_ctor_set(v___x_4374_, 0, v___x_4384_);
                    v___x_4386_ = v___x_4374_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4387_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_snd_4372_);
                    v___x_4386_ = v_reuseFailAlloc_4387_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4386_;
            }
            25 => {
                v_fst_4400_ = leanh::lean_ctor_get(v_fst_4395_, 0);
                v_snd_4401_ = leanh::lean_ctor_get(v_fst_4395_, 1);
                v_isSharedCheck_4413_ = (!leanh::lean_is_exclusive(v_fst_4395_)) as u8;
                if v_isSharedCheck_4413_ == 0 {
                    v___x_4403_ = v_fst_4395_;
                    v_isShared_4404_ = v_isSharedCheck_4413_;
                    state = 26;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4401_);
                    leanh::lean_inc(v_fst_4400_);
                    leanh::lean_dec(v_fst_4395_);
                    v___x_4403_ = leanh::lean_box(0);
                    v_isShared_4404_ = v_isSharedCheck_4413_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4405_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_struct_4393_,
                        v_fst_4400_,
                    );
                if v___x_4405_ == 0 {
                    leanh::lean_inc(v_idx_4392_);
                    leanh::lean_inc(v_typeName_4391_);
                    leanh::lean_del_object(v___x_4403_);
                    leanh::lean_del_object(v___x_4398_);
                    leanh::lean_dec_ref_known(v_e_4219_, 3);
                    v___x_4406_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_typeName_4391_, v_idx_4392_, v_fst_4400_, v_snd_4401_, v_a_4222_, v_snd_4396_);
                    return v___x_4406_;
                } else {
                    leanh::lean_dec(v_fst_4400_);
                    if v_isShared_4404_ == 0 {
                        leanh::lean_ctor_set(v___x_4403_, 0, v_e_4219_);
                        v___x_4408_ = v___x_4403_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_4412_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_e_4219_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_snd_4401_);
                        v___x_4408_ = v_reuseFailAlloc_4412_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_4399_ == 0 {
                    leanh::lean_ctor_set(v___x_4398_, 0, v___x_4408_);
                    v___x_4410_ = v___x_4398_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4411_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4408_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_snd_4396_);
                    v___x_4410_ = v_reuseFailAlloc_4411_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(
    mut v_n_4417_: *mut leanh::LeanObject,
    mut v_varDeps_4418_: *mut leanh::LeanObject,
    mut v_xs_4419_: *mut leanh::LeanObject,
    mut v_e_4420_: *mut leanh::LeanObject,
    mut v_offset_4421_: *mut leanh::LeanObject,
    mut v_a_4422_: *mut leanh::LeanObject,
    mut v_a_4423_: u8,
    mut v_a_4424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: u8 = 0;
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: u8 = 0;
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedNumArgs_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numArgs_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v___x_4466_: u8 = 0;
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_offset_4421_);
                leanh::lean_inc_ref(v_e_4420_);
                v_key_4425_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_key_4425_, 0, v_e_4420_);
                leanh::lean_ctor_set(v_key_4425_, 1, v_offset_4421_);
                v___x_4440_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_a_4422_, v_key_4425_);
                if leanh::lean_obj_tag(v___x_4440_) == 1 {
                    leanh::lean_dec_ref_known(v_key_4425_, 2);
                    leanh::lean_dec(v_offset_4421_);
                    leanh::lean_dec_ref(v_e_4420_);
                    v_val_4441_ = leanh::lean_ctor_get(v___x_4440_, 0);
                    leanh::lean_inc(v_val_4441_);
                    leanh::lean_dec_ref_known(v___x_4440_, 1);
                    v___x_4442_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4442_, 0, v_val_4441_);
                    leanh::lean_ctor_set(v___x_4442_, 1, v_a_4422_);
                    v___x_4443_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4443_, 0, v___x_4442_);
                    leanh::lean_ctor_set(v___x_4443_, 1, v_a_4424_);
                    return v___x_4443_;
                } else {
                    leanh::lean_dec(v___x_4440_);
                    v___x_4444_ = l_Lean_Expr_looseBVarRange(v_e_4420_);
                    v___x_4445_ = lean_nat_dec_le(v___x_4444_, v_offset_4421_);
                    leanh::lean_dec(v___x_4444_);
                    if v___x_4445_ == 0 {
                        v___x_4446_ = l_Lean_Expr_getAppFn(v_e_4420_);
                        if leanh::lean_obj_tag(v___x_4446_) == 0 {
                            v_deBruijnIndex_4447_ = leanh::lean_ctor_get(v___x_4446_, 0);
                            leanh::lean_inc(v_deBruijnIndex_4447_);
                            leanh::lean_dec_ref_known(v___x_4446_, 1);
                            v___x_4448_ = lean_nat_dec_le(v_offset_4421_, v_deBruijnIndex_4447_);
                            if v___x_4448_ == 0 {
                                leanh::lean_dec(v_deBruijnIndex_4447_);
                                leanh::lean_dec(v_offset_4421_);
                                v___x_4449_ =
                                    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                        v_key_4425_,
                                        v_e_4420_,
                                        v_a_4422_,
                                        v_a_4423_,
                                        v_a_4424_,
                                    );
                                return v___x_4449_;
                            } else {
                                v___x_4450_ = lean_nat_add(v_offset_4421_, v_n_4417_);
                                v___x_4451_ = lean_nat_dec_lt(v_deBruijnIndex_4447_, v___x_4450_);
                                leanh::lean_dec(v___x_4450_);
                                if v___x_4451_ == 0 {
                                    leanh::lean_dec(v_offset_4421_);
                                    leanh::lean_dec_ref(v_e_4420_);
                                    v___x_4452_ = lean_nat_sub(v_deBruijnIndex_4447_, v_n_4417_);
                                    leanh::lean_dec(v_deBruijnIndex_4447_);
                                    v___x_4453_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_4452_, v_a_4424_);
                                    v_fst_4454_ = leanh::lean_ctor_get(v___x_4453_, 0);
                                    leanh::lean_inc(v_fst_4454_);
                                    v_snd_4455_ = leanh::lean_ctor_get(v___x_4453_, 1);
                                    leanh::lean_inc(v_snd_4455_);
                                    leanh::lean_dec_ref(v___x_4453_);
                                    v___x_4456_ =
                                        l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                            v_key_4425_,
                                            v_fst_4454_,
                                            v_a_4422_,
                                            v_a_4423_,
                                            v_snd_4455_,
                                        );
                                    return v___x_4456_;
                                } else {
                                    v___x_4457_ =
                                        lean_nat_sub(v_deBruijnIndex_4447_, v_offset_4421_);
                                    leanh::lean_dec(v_deBruijnIndex_4447_);
                                    v___x_4458_ = lean_nat_sub(v_n_4417_, v___x_4457_);
                                    leanh::lean_dec(v___x_4457_);
                                    v___x_4459_ = leanh::lean_unsigned_to_nat(1);
                                    v_i_4460_ = lean_nat_sub(v___x_4458_, v___x_4459_);
                                    leanh::lean_dec(v___x_4458_);
                                    v___x_4461_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
                                    v___x_4462_ = lean_array_get_borrowed(
                                        v___x_4461_,
                                        v_varDeps_4418_,
                                        v_i_4460_,
                                    );
                                    v_expectedNumArgs_4463_ = lean_array_get_size(v___x_4462_);
                                    v_numArgs_4464_ = l_Lean_Expr_getAppNumArgs(v_e_4420_);
                                    v___x_4465_ =
                                        lean_nat_dec_lt(v_expectedNumArgs_4463_, v_numArgs_4464_);
                                    if v___x_4465_ == 0 {
                                        v___x_4466_ = lean_nat_dec_eq(
                                            v_numArgs_4464_,
                                            v_expectedNumArgs_4463_,
                                        );
                                        leanh::lean_dec(v_numArgs_4464_);
                                        if v___x_4466_ == 0 {
                                            leanh::lean_dec(v_i_4460_);
                                            v___x_4467_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__4_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__4);
                                            v___x_4468_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_4467_, v_a_4423_, v_a_4424_);
                                            v_fst_4469_ =
                                                leanh::lean_ctor_get(v___x_4468_, 0);
                                            leanh::lean_inc(v_fst_4469_);
                                            if leanh::lean_obj_tag(v_fst_4469_) == 1 {
                                                leanh::lean_dec(v_offset_4421_);
                                                leanh::lean_dec_ref(v_e_4420_);
                                                v_snd_4470_ =
                                                    leanh::lean_ctor_get(v___x_4468_, 1);
                                                leanh::lean_inc(v_snd_4470_);
                                                leanh::lean_dec_ref(v___x_4468_);
                                                v_val_4471_ =
                                                    leanh::lean_ctor_get(v_fst_4469_, 0);
                                                leanh::lean_inc(v_val_4471_);
                                                leanh::lean_dec_ref_known(v_fst_4469_, 1);
                                                v___x_4472_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_4425_, v_val_4471_, v_a_4422_, v_a_4423_, v_snd_4470_);
                                                return v___x_4472_;
                                            } else {
                                                leanh::lean_dec(v_fst_4469_);
                                                v_snd_4473_ =
                                                    leanh::lean_ctor_get(v___x_4468_, 1);
                                                leanh::lean_inc(v_snd_4473_);
                                                leanh::lean_dec_ref(v___x_4468_);
                                                v_snd_4427_ = v_snd_4473_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_offset_4421_);
                                            leanh::lean_dec_ref(v_e_4420_);
                                            v___x_4474_ =
                                                lean_array_fget_borrowed(v_xs_4419_, v_i_4460_);
                                            leanh::lean_dec(v_i_4460_);
                                            leanh::lean_inc(v___x_4474_);
                                            v___x_4475_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_4425_, v___x_4474_, v_a_4422_, v_a_4423_, v_a_4424_);
                                            return v___x_4475_;
                                        }
                                    } else {
                                        leanh::lean_dec(v_numArgs_4464_);
                                        leanh::lean_dec(v_i_4460_);
                                        v_snd_4427_ = v_a_4424_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_4446_);
                            v_snd_4427_ = v_a_4424_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_offset_4421_);
                        v___x_4476_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                            v_key_4425_,
                            v_e_4420_,
                            v_a_4422_,
                            v_a_4423_,
                            v_a_4424_,
                        );
                        return v___x_4476_;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_e_4420_) {
                9 => {
                    leanh::lean_dec(v_offset_4421_);
                    v___x_4428_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_4425_,
                        v_e_4420_,
                        v_a_4422_,
                        v_a_4423_,
                        v_snd_4427_,
                    );
                    return v___x_4428_;
                }
                2 => {
                    leanh::lean_dec(v_offset_4421_);
                    v___x_4429_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_4425_,
                        v_e_4420_,
                        v_a_4422_,
                        v_a_4423_,
                        v_snd_4427_,
                    );
                    return v___x_4429_;
                }
                0 => {
                    leanh::lean_dec(v_offset_4421_);
                    v___x_4430_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_4425_,
                        v_e_4420_,
                        v_a_4422_,
                        v_a_4423_,
                        v_snd_4427_,
                    );
                    return v___x_4430_;
                }
                1 => {
                    leanh::lean_dec(v_offset_4421_);
                    v___x_4431_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_4425_,
                        v_e_4420_,
                        v_a_4422_,
                        v_a_4423_,
                        v_snd_4427_,
                    );
                    return v___x_4431_;
                }
                4 => {
                    leanh::lean_dec(v_offset_4421_);
                    v___x_4432_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_4425_,
                        v_e_4420_,
                        v_a_4422_,
                        v_a_4423_,
                        v_snd_4427_,
                    );
                    return v___x_4432_;
                }
                3 => {
                    leanh::lean_dec(v_offset_4421_);
                    v___x_4433_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_4425_,
                        v_e_4420_,
                        v_a_4422_,
                        v_a_4423_,
                        v_snd_4427_,
                    );
                    return v___x_4433_;
                }
                _ => {
                    v___x_4434_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_4417_, v_varDeps_4418_, v_xs_4419_, v_e_4420_, v_offset_4421_, v_a_4422_, v_a_4423_, v_snd_4427_);
                    v_fst_4435_ = leanh::lean_ctor_get(v___x_4434_, 0);
                    leanh::lean_inc(v_fst_4435_);
                    v_snd_4436_ = leanh::lean_ctor_get(v___x_4434_, 1);
                    leanh::lean_inc(v_snd_4436_);
                    leanh::lean_dec_ref(v___x_4434_);
                    v_fst_4437_ = leanh::lean_ctor_get(v_fst_4435_, 0);
                    leanh::lean_inc(v_fst_4437_);
                    v_snd_4438_ = leanh::lean_ctor_get(v_fst_4435_, 1);
                    leanh::lean_inc(v_snd_4438_);
                    leanh::lean_dec(v_fst_4435_);
                    v___x_4439_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_4425_,
                        v_fst_4437_,
                        v_snd_4438_,
                        v_a_4423_,
                        v_snd_4436_,
                    );
                    return v___x_4439_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___boxed(
    mut v_n_4477_: *mut leanh::LeanObject,
    mut v_varDeps_4478_: *mut leanh::LeanObject,
    mut v_xs_4479_: *mut leanh::LeanObject,
    mut v_e_4480_: *mut leanh::LeanObject,
    mut v_offset_4481_: *mut leanh::LeanObject,
    mut v_a_4482_: *mut leanh::LeanObject,
    mut v_a_4483_: *mut leanh::LeanObject,
    mut v_a_4484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_4485_: u8 = 0;
    let mut v_res_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4485_ = (leanh::lean_unbox(v_a_4483_) as u8);
    v_res_4486_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_4477_, v_varDeps_4478_, v_xs_4479_, v_e_4480_, v_offset_4481_, v_a_4482_, v_a_boxed_4485_, v_a_4484_);
    leanh::lean_dec_ref(v_xs_4479_);
    leanh::lean_dec_ref(v_varDeps_4478_);
    leanh::lean_dec(v_n_4477_);
    return v_res_4486_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(
    mut v_n_4487_: *mut leanh::LeanObject,
    mut v_varDeps_4488_: *mut leanh::LeanObject,
    mut v_xs_4489_: *mut leanh::LeanObject,
    mut v_e_4490_: *mut leanh::LeanObject,
    mut v_offset_4491_: *mut leanh::LeanObject,
    mut v_a_4492_: *mut leanh::LeanObject,
    mut v_a_4493_: *mut leanh::LeanObject,
    mut v_a_4494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_4495_: u8 = 0;
    let mut v_res_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4495_ = (leanh::lean_unbox(v_a_4493_) as u8);
    v_res_4496_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_4487_, v_varDeps_4488_, v_xs_4489_, v_e_4490_, v_offset_4491_, v_a_4492_, v_a_boxed_4495_, v_a_4494_);
    leanh::lean_dec_ref(v_xs_4489_);
    leanh::lean_dec_ref(v_varDeps_4488_);
    leanh::lean_dec(v_n_4487_);
    return v_res_4496_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4497_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(leanh::lean_box(0));
    return v___x_4497_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4498_ = leanh::lean_box(0);
    v___x_4499_ = leanh::lean_unsigned_to_nat(16);
    v___x_4500_ = lean_mk_array(v___x_4499_, v___x_4498_);
    return v___x_4500_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4501_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1);
    v___x_4502_ = leanh::lean_unsigned_to_nat(0);
    v___x_4503_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4503_, 0, v___x_4502_);
    leanh::lean_ctor_set(v___x_4503_, 1, v___x_4501_);
    return v___x_4503_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(
    mut v_e_4504_: *mut leanh::LeanObject,
    mut v_xs_4505_: *mut leanh::LeanObject,
    mut v_varDeps_4506_: *mut leanh::LeanObject,
    mut v_a_4507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4520_: u8 = 0;
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4542_: u8 = 0;
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4545_: u8 = 0;
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut v_unused_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4553_: u8 = 0;
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: u8 = 0;
    let mut v_n_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: u8 = 0;
    let mut v___x_4568_: u8 = 0;
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedNumArgs_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numArgs_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: u8 = 0;
    let mut v___x_4581_: u8 = 0;
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4509_ = lean_st_ref_take(v_a_4507_);
                v_share_4510_ = leanh::lean_ctor_get(v___x_4509_, 0);
                v_maxFVar_4511_ = leanh::lean_ctor_get(v___x_4509_, 1);
                v_proofInstInfo_4512_ = leanh::lean_ctor_get(v___x_4509_, 2);
                v_inferType_4513_ = leanh::lean_ctor_get(v___x_4509_, 3);
                v_getLevel_4514_ = leanh::lean_ctor_get(v___x_4509_, 4);
                v_congrInfo_4515_ = leanh::lean_ctor_get(v___x_4509_, 5);
                v_defEqI_4516_ = leanh::lean_ctor_get(v___x_4509_, 6);
                v_extensions_4517_ = leanh::lean_ctor_get(v___x_4509_, 7);
                v_issues_4518_ = leanh::lean_ctor_get(v___x_4509_, 8);
                v_canon_4519_ = leanh::lean_ctor_get(v___x_4509_, 9);
                v_debug_4520_ = leanh::lean_ctor_get_uint8(
                    v___x_4509_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4590_ = (!leanh::lean_is_exclusive(v___x_4509_)) as u8;
                if v_isSharedCheck_4590_ == 0 {
                    v___x_4522_ = v___x_4509_;
                    v_isShared_4523_ = v_isSharedCheck_4590_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_canon_4519_);
                    leanh::lean_inc(v_issues_4518_);
                    leanh::lean_inc(v_extensions_4517_);
                    leanh::lean_inc(v_defEqI_4516_);
                    leanh::lean_inc(v_congrInfo_4515_);
                    leanh::lean_inc(v_getLevel_4514_);
                    leanh::lean_inc(v_inferType_4513_);
                    leanh::lean_inc(v_proofInstInfo_4512_);
                    leanh::lean_inc(v_maxFVar_4511_);
                    leanh::lean_inc(v_share_4510_);
                    leanh::lean_dec(v___x_4509_);
                    v___x_4522_ = leanh::lean_box(0);
                    v_isShared_4523_ = v_isSharedCheck_4590_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4524_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0_once), _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0);
                if v_isShared_4523_ == 0 {
                    leanh::lean_ctor_set(v___x_4522_, 0, v___x_4524_);
                    v___x_4526_ = v___x_4522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4589_ = leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_maxFVar_4511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 2, v_proofInstInfo_4512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 3, v_inferType_4513_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 4, v_getLevel_4514_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 5, v_congrInfo_4515_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 6, v_defEqI_4516_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 7, v_extensions_4517_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 8, v_issues_4518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 9, v_canon_4519_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4589_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        v_debug_4520_,
                    );
                    v___x_4526_ = v_reuseFailAlloc_4589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4527_ = lean_st_ref_set(v_a_4507_, v___x_4526_);
                v___x_4528_ = lean_st_ref_get(v_a_4507_);
                v_debug_4553_ = leanh::lean_ctor_get_uint8(
                    v___x_4528_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                leanh::lean_dec(v___x_4528_);
                v___x_4554_ = leanh::lean_unsigned_to_nat(0);
                v___x_4555_ = l_Lean_Expr_looseBVarRange(v_e_4504_);
                v___x_4556_ = lean_nat_dec_le(v___x_4555_, v___x_4554_);
                leanh::lean_dec(v___x_4555_);
                if v___x_4556_ == 0 {
                    v_n_4557_ = lean_array_get_size(v_xs_4505_);
                    v___x_4565_ = l_Lean_Expr_getAppFn(v_e_4504_);
                    if leanh::lean_obj_tag(v___x_4565_) == 0 {
                        v_deBruijnIndex_4566_ = leanh::lean_ctor_get(v___x_4565_, 0);
                        leanh::lean_inc(v_deBruijnIndex_4566_);
                        leanh::lean_dec_ref_known(v___x_4565_, 1);
                        v___x_4567_ = lean_nat_dec_le(v___x_4554_, v_deBruijnIndex_4566_);
                        if v___x_4567_ == 0 {
                            leanh::lean_dec(v_deBruijnIndex_4566_);
                            v_fst_4530_ = v_e_4504_;
                            v_snd_4531_ = v_share_4510_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4568_ = lean_nat_dec_lt(v_deBruijnIndex_4566_, v_n_4557_);
                            if v___x_4568_ == 0 {
                                leanh::lean_dec_ref(v_e_4504_);
                                v___x_4569_ = lean_nat_sub(v_deBruijnIndex_4566_, v_n_4557_);
                                leanh::lean_dec(v_deBruijnIndex_4566_);
                                v___x_4570_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_4569_, v_share_4510_);
                                v_fst_4571_ = leanh::lean_ctor_get(v___x_4570_, 0);
                                leanh::lean_inc(v_fst_4571_);
                                v_snd_4572_ = leanh::lean_ctor_get(v___x_4570_, 1);
                                leanh::lean_inc(v_snd_4572_);
                                leanh::lean_dec_ref(v___x_4570_);
                                v_fst_4530_ = v_fst_4571_;
                                v_snd_4531_ = v_snd_4572_;
                                state = 3;
                                continue;
                            } else {
                                v___x_4573_ = lean_nat_sub(v_n_4557_, v_deBruijnIndex_4566_);
                                leanh::lean_dec(v_deBruijnIndex_4566_);
                                v___x_4574_ = leanh::lean_unsigned_to_nat(1);
                                v_i_4575_ = lean_nat_sub(v___x_4573_, v___x_4574_);
                                leanh::lean_dec(v___x_4573_);
                                v___x_4576_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
                                v___x_4577_ = lean_array_get_borrowed(
                                    v___x_4576_,
                                    v_varDeps_4506_,
                                    v_i_4575_,
                                );
                                v_expectedNumArgs_4578_ = lean_array_get_size(v___x_4577_);
                                v_numArgs_4579_ = l_Lean_Expr_getAppNumArgs(v_e_4504_);
                                v___x_4580_ =
                                    lean_nat_dec_lt(v_expectedNumArgs_4578_, v_numArgs_4579_);
                                if v___x_4580_ == 0 {
                                    v___x_4581_ =
                                        lean_nat_dec_eq(v_numArgs_4579_, v_expectedNumArgs_4578_);
                                    leanh::lean_dec(v_numArgs_4579_);
                                    if v___x_4581_ == 0 {
                                        leanh::lean_dec(v_i_4575_);
                                        v___x_4582_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__4_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__4);
                                        v___x_4583_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_4582_, v_debug_4553_, v_share_4510_);
                                        v_fst_4584_ = leanh::lean_ctor_get(v___x_4583_, 0);
                                        leanh::lean_inc(v_fst_4584_);
                                        if leanh::lean_obj_tag(v_fst_4584_) == 1 {
                                            leanh::lean_dec_ref(v_e_4504_);
                                            v_snd_4585_ =
                                                leanh::lean_ctor_get(v___x_4583_, 1);
                                            leanh::lean_inc(v_snd_4585_);
                                            leanh::lean_dec_ref(v___x_4583_);
                                            v_val_4586_ =
                                                leanh::lean_ctor_get(v_fst_4584_, 0);
                                            leanh::lean_inc(v_val_4586_);
                                            leanh::lean_dec_ref_known(v_fst_4584_, 1);
                                            v_fst_4530_ = v_val_4586_;
                                            v_snd_4531_ = v_snd_4585_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v_fst_4584_);
                                            v_snd_4587_ =
                                                leanh::lean_ctor_get(v___x_4583_, 1);
                                            leanh::lean_inc(v_snd_4587_);
                                            leanh::lean_dec_ref(v___x_4583_);
                                            v_snd_4559_ = v_snd_4587_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_e_4504_);
                                        v___x_4588_ =
                                            lean_array_fget_borrowed(v_xs_4505_, v_i_4575_);
                                        leanh::lean_dec(v_i_4575_);
                                        leanh::lean_inc(v___x_4588_);
                                        v_fst_4530_ = v___x_4588_;
                                        v_snd_4531_ = v_share_4510_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_numArgs_4579_);
                                    leanh::lean_dec(v_i_4575_);
                                    v_snd_4559_ = v_share_4510_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_4565_);
                        v_snd_4559_ = v_share_4510_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_fst_4530_ = v_e_4504_;
                    v_snd_4531_ = v_share_4510_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4532_ = lean_st_ref_take(v_a_4507_);
                v_maxFVar_4533_ = leanh::lean_ctor_get(v___x_4532_, 1);
                v_proofInstInfo_4534_ = leanh::lean_ctor_get(v___x_4532_, 2);
                v_inferType_4535_ = leanh::lean_ctor_get(v___x_4532_, 3);
                v_getLevel_4536_ = leanh::lean_ctor_get(v___x_4532_, 4);
                v_congrInfo_4537_ = leanh::lean_ctor_get(v___x_4532_, 5);
                v_defEqI_4538_ = leanh::lean_ctor_get(v___x_4532_, 6);
                v_extensions_4539_ = leanh::lean_ctor_get(v___x_4532_, 7);
                v_issues_4540_ = leanh::lean_ctor_get(v___x_4532_, 8);
                v_canon_4541_ = leanh::lean_ctor_get(v___x_4532_, 9);
                v_debug_4542_ = leanh::lean_ctor_get_uint8(
                    v___x_4532_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4551_ = (!leanh::lean_is_exclusive(v___x_4532_)) as u8;
                if v_isSharedCheck_4551_ == 0 {
                    v_unused_4552_ = leanh::lean_ctor_get(v___x_4532_, 0);
                    leanh::lean_dec(v_unused_4552_);
                    v___x_4544_ = v___x_4532_;
                    v_isShared_4545_ = v_isSharedCheck_4551_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_canon_4541_);
                    leanh::lean_inc(v_issues_4540_);
                    leanh::lean_inc(v_extensions_4539_);
                    leanh::lean_inc(v_defEqI_4538_);
                    leanh::lean_inc(v_congrInfo_4537_);
                    leanh::lean_inc(v_getLevel_4536_);
                    leanh::lean_inc(v_inferType_4535_);
                    leanh::lean_inc(v_proofInstInfo_4534_);
                    leanh::lean_inc(v_maxFVar_4533_);
                    leanh::lean_dec(v___x_4532_);
                    v___x_4544_ = leanh::lean_box(0);
                    v_isShared_4545_ = v_isSharedCheck_4551_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4545_ == 0 {
                    leanh::lean_ctor_set(v___x_4544_, 0, v_snd_4531_);
                    v___x_4547_ = v___x_4544_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_snd_4531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_maxFVar_4533_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 2, v_proofInstInfo_4534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 3, v_inferType_4535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 4, v_getLevel_4536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 5, v_congrInfo_4537_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 6, v_defEqI_4538_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 7, v_extensions_4539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 8, v_issues_4540_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 9, v_canon_4541_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        v_debug_4542_,
                    );
                    v___x_4547_ = v_reuseFailAlloc_4550_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4548_ = lean_st_ref_set(v_a_4507_, v___x_4547_);
                v___x_4549_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4549_, 0, v_fst_4530_);
                return v___x_4549_;
            }
            6 => match leanh::lean_obj_tag(v_e_4504_) {
                9 => {
                    v_fst_4530_ = v_e_4504_;
                    v_snd_4531_ = v_snd_4559_;
                    state = 3;
                    continue;
                }
                2 => {
                    v_fst_4530_ = v_e_4504_;
                    v_snd_4531_ = v_snd_4559_;
                    state = 3;
                    continue;
                }
                0 => {
                    v_fst_4530_ = v_e_4504_;
                    v_snd_4531_ = v_snd_4559_;
                    state = 3;
                    continue;
                }
                1 => {
                    v_fst_4530_ = v_e_4504_;
                    v_snd_4531_ = v_snd_4559_;
                    state = 3;
                    continue;
                }
                4 => {
                    v_fst_4530_ = v_e_4504_;
                    v_snd_4531_ = v_snd_4559_;
                    state = 3;
                    continue;
                }
                3 => {
                    v_fst_4530_ = v_e_4504_;
                    v_snd_4531_ = v_snd_4559_;
                    state = 3;
                    continue;
                }
                _ => {
                    v___x_4560_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2);
                    v___x_4561_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_4557_, v_varDeps_4506_, v_xs_4505_, v_e_4504_, v___x_4554_, v___x_4560_, v_debug_4553_, v_snd_4559_);
                    v_fst_4562_ = leanh::lean_ctor_get(v___x_4561_, 0);
                    leanh::lean_inc(v_fst_4562_);
                    v_snd_4563_ = leanh::lean_ctor_get(v___x_4561_, 1);
                    leanh::lean_inc(v_snd_4563_);
                    leanh::lean_dec_ref(v___x_4561_);
                    v_fst_4564_ = leanh::lean_ctor_get(v_fst_4562_, 0);
                    leanh::lean_inc(v_fst_4564_);
                    leanh::lean_dec(v_fst_4562_);
                    v_fst_4530_ = v_fst_4564_;
                    v_snd_4531_ = v_snd_4563_;
                    state = 3;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___boxed(
    mut v_e_4591_: *mut leanh::LeanObject,
    mut v_xs_4592_: *mut leanh::LeanObject,
    mut v_varDeps_4593_: *mut leanh::LeanObject,
    mut v_a_4594_: *mut leanh::LeanObject,
    mut v_a_4595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4596_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(
        v_e_4591_,
        v_xs_4592_,
        v_varDeps_4593_,
        v_a_4594_,
    );
    leanh::lean_dec(v_a_4594_);
    leanh::lean_dec_ref(v_varDeps_4593_);
    leanh::lean_dec_ref(v_xs_4592_);
    return v_res_4596_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(
    mut v_e_4597_: *mut leanh::LeanObject,
    mut v_xs_4598_: *mut leanh::LeanObject,
    mut v_varDeps_4599_: *mut leanh::LeanObject,
    mut v_a_4600_: *mut leanh::LeanObject,
    mut v_a_4601_: *mut leanh::LeanObject,
    mut v_a_4602_: *mut leanh::LeanObject,
    mut v_a_4603_: *mut leanh::LeanObject,
    mut v_a_4604_: *mut leanh::LeanObject,
    mut v_a_4605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4607_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(
        v_e_4597_,
        v_xs_4598_,
        v_varDeps_4599_,
        v_a_4601_,
    );
    return v___x_4607_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(
    mut v_e_4608_: *mut leanh::LeanObject,
    mut v_xs_4609_: *mut leanh::LeanObject,
    mut v_varDeps_4610_: *mut leanh::LeanObject,
    mut v_a_4611_: *mut leanh::LeanObject,
    mut v_a_4612_: *mut leanh::LeanObject,
    mut v_a_4613_: *mut leanh::LeanObject,
    mut v_a_4614_: *mut leanh::LeanObject,
    mut v_a_4615_: *mut leanh::LeanObject,
    mut v_a_4616_: *mut leanh::LeanObject,
    mut v_a_4617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4618_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(
        v_e_4608_,
        v_xs_4609_,
        v_varDeps_4610_,
        v_a_4611_,
        v_a_4612_,
        v_a_4613_,
        v_a_4614_,
        v_a_4615_,
        v_a_4616_,
    );
    leanh::lean_dec(v_a_4616_);
    leanh::lean_dec_ref(v_a_4615_);
    leanh::lean_dec(v_a_4614_);
    leanh::lean_dec_ref(v_a_4613_);
    leanh::lean_dec(v_a_4612_);
    leanh::lean_dec_ref(v_a_4611_);
    leanh::lean_dec_ref(v_varDeps_4610_);
    leanh::lean_dec_ref(v_xs_4609_);
    return v_res_4618_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(
    mut v_00_u03b2_4619_: *mut leanh::LeanObject,
    mut v_m_4620_: *mut leanh::LeanObject,
    mut v_a_4621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4622_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_4620_, v_a_4621_);
    return v___x_4622_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___boxed(
    mut v_00_u03b2_4623_: *mut leanh::LeanObject,
    mut v_m_4624_: *mut leanh::LeanObject,
    mut v_a_4625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(v_00_u03b2_4623_, v_m_4624_, v_a_4625_);
    leanh::lean_dec_ref(v_a_4625_);
    leanh::lean_dec_ref(v_m_4624_);
    return v_res_4626_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(
    mut v_00_u03b2_4627_: *mut leanh::LeanObject,
    mut v_a_4628_: *mut leanh::LeanObject,
    mut v_x_4629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4630_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_4628_, v_x_4629_);
    return v___x_4630_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___boxed(
    mut v_00_u03b2_4631_: *mut leanh::LeanObject,
    mut v_a_4632_: *mut leanh::LeanObject,
    mut v_x_4633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4634_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(v_00_u03b2_4631_, v_a_4632_, v_x_4633_);
    leanh::lean_dec(v_x_4633_);
    leanh::lean_dec_ref(v_a_4632_);
    return v_res_4634_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(
    mut v_name_4635_: *mut leanh::LeanObject,
    mut v_type_4636_: *mut leanh::LeanObject,
    mut v_val_4637_: *mut leanh::LeanObject,
    mut v_k_4638_: *mut leanh::LeanObject,
    mut v_nondep_4639_: u8,
    mut v_kind_4640_: u8,
    mut v___y_4641_: *mut leanh::LeanObject,
    mut v___y_4642_: *mut leanh::LeanObject,
    mut v___y_4643_: *mut leanh::LeanObject,
    mut v___y_4644_: *mut leanh::LeanObject,
    mut v___y_4645_: *mut leanh::LeanObject,
    mut v___y_4646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4653_: u8 = 0;
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_4642_);
                leanh::lean_inc_ref(v___y_4641_);
                v___f_4648_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                leanh::lean_closure_set(v___f_4648_, 0, v_k_4638_);
                leanh::lean_closure_set(v___f_4648_, 1, v___y_4641_);
                leanh::lean_closure_set(v___f_4648_, 2, v___y_4642_);
                v___x_4649_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    leanh::lean_box(0),
                    v_name_4635_,
                    v_type_4636_,
                    v_val_4637_,
                    v___f_4648_,
                    v_nondep_4639_,
                    v_kind_4640_,
                    v___y_4643_,
                    v___y_4644_,
                    v___y_4645_,
                    v___y_4646_,
                );
                if leanh::lean_obj_tag(v___x_4649_) == 0 {
                    return v___x_4649_;
                } else {
                    v_a_4650_ = leanh::lean_ctor_get(v___x_4649_, 0);
                    v_isSharedCheck_4657_ = (!leanh::lean_is_exclusive(v___x_4649_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v___x_4652_ = v___x_4649_;
                        v_isShared_4653_ = v_isSharedCheck_4657_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4650_);
                        leanh::lean_dec(v___x_4649_);
                        v___x_4652_ = leanh::lean_box(0);
                        v_isShared_4653_ = v_isSharedCheck_4657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4653_ == 0 {
                    v___x_4655_ = v___x_4652_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4656_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
                    v___x_4655_ = v_reuseFailAlloc_4656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(
    mut v_name_4658_: *mut leanh::LeanObject,
    mut v_type_4659_: *mut leanh::LeanObject,
    mut v_val_4660_: *mut leanh::LeanObject,
    mut v_k_4661_: *mut leanh::LeanObject,
    mut v_nondep_4662_: *mut leanh::LeanObject,
    mut v_kind_4663_: *mut leanh::LeanObject,
    mut v___y_4664_: *mut leanh::LeanObject,
    mut v___y_4665_: *mut leanh::LeanObject,
    mut v___y_4666_: *mut leanh::LeanObject,
    mut v___y_4667_: *mut leanh::LeanObject,
    mut v___y_4668_: *mut leanh::LeanObject,
    mut v___y_4669_: *mut leanh::LeanObject,
    mut v___y_4670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_4671_: u8 = 0;
    let mut v_kind_boxed_4672_: u8 = 0;
    let mut v_res_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_4671_ = (leanh::lean_unbox(v_nondep_4662_) as u8);
    v_kind_boxed_4672_ = (leanh::lean_unbox(v_kind_4663_) as u8);
    v_res_4673_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_4658_, v_type_4659_, v_val_4660_, v_k_4661_, v_nondep_boxed_4671_, v_kind_boxed_4672_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
    leanh::lean_dec(v___y_4669_);
    leanh::lean_dec_ref(v___y_4668_);
    leanh::lean_dec(v___y_4667_);
    leanh::lean_dec_ref(v___y_4666_);
    leanh::lean_dec(v___y_4665_);
    leanh::lean_dec_ref(v___y_4664_);
    return v_res_4673_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(
    mut v_00_u03b1_4674_: *mut leanh::LeanObject,
    mut v_name_4675_: *mut leanh::LeanObject,
    mut v_type_4676_: *mut leanh::LeanObject,
    mut v_val_4677_: *mut leanh::LeanObject,
    mut v_k_4678_: *mut leanh::LeanObject,
    mut v_nondep_4679_: u8,
    mut v_kind_4680_: u8,
    mut v___y_4681_: *mut leanh::LeanObject,
    mut v___y_4682_: *mut leanh::LeanObject,
    mut v___y_4683_: *mut leanh::LeanObject,
    mut v___y_4684_: *mut leanh::LeanObject,
    mut v___y_4685_: *mut leanh::LeanObject,
    mut v___y_4686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4688_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_4675_, v_type_4676_, v_val_4677_, v_k_4678_, v_nondep_4679_, v_kind_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
    return v___x_4688_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(
    mut v_00_u03b1_4689_: *mut leanh::LeanObject,
    mut v_name_4690_: *mut leanh::LeanObject,
    mut v_type_4691_: *mut leanh::LeanObject,
    mut v_val_4692_: *mut leanh::LeanObject,
    mut v_k_4693_: *mut leanh::LeanObject,
    mut v_nondep_4694_: *mut leanh::LeanObject,
    mut v_kind_4695_: *mut leanh::LeanObject,
    mut v___y_4696_: *mut leanh::LeanObject,
    mut v___y_4697_: *mut leanh::LeanObject,
    mut v___y_4698_: *mut leanh::LeanObject,
    mut v___y_4699_: *mut leanh::LeanObject,
    mut v___y_4700_: *mut leanh::LeanObject,
    mut v___y_4701_: *mut leanh::LeanObject,
    mut v___y_4702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_4703_: u8 = 0;
    let mut v_kind_boxed_4704_: u8 = 0;
    let mut v_res_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_4703_ = (leanh::lean_unbox(v_nondep_4694_) as u8);
    v_kind_boxed_4704_ = (leanh::lean_unbox(v_kind_4695_) as u8);
    v_res_4705_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_4689_, v_name_4690_, v_type_4691_, v_val_4692_, v_k_4693_, v_nondep_boxed_4703_, v_kind_boxed_4704_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
    leanh::lean_dec(v___y_4701_);
    leanh::lean_dec_ref(v___y_4700_);
    leanh::lean_dec(v___y_4699_);
    leanh::lean_dec_ref(v___y_4698_);
    leanh::lean_dec(v___y_4697_);
    leanh::lean_dec_ref(v___y_4696_);
    return v_res_4705_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4706_ = l_Lean_Meta_Sym_instInhabitedSymM(leanh::lean_box(0));
    return v___x_4706_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(
    mut v_msg_4707_: *mut leanh::LeanObject,
    mut v___y_4708_: *mut leanh::LeanObject,
    mut v___y_4709_: *mut leanh::LeanObject,
    mut v___y_4710_: *mut leanh::LeanObject,
    mut v___y_4711_: *mut leanh::LeanObject,
    mut v___y_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402__overap_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4715_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0);
    v___x_2402__overap_4716_ = lean_panic_fn_borrowed(v___x_4715_, v_msg_4707_);
    leanh::lean_inc(v___y_4713_);
    leanh::lean_inc_ref(v___y_4712_);
    leanh::lean_inc(v___y_4711_);
    leanh::lean_inc_ref(v___y_4710_);
    leanh::lean_inc(v___y_4709_);
    leanh::lean_inc_ref(v___y_4708_);
    v___x_4717_ = leanh::lean_apply_7(
        v___x_2402__overap_4716_,
        v___y_4708_,
        v___y_4709_,
        v___y_4710_,
        v___y_4711_,
        v___y_4712_,
        v___y_4713_,
        leanh::lean_box(0),
    );
    return v___x_4717_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___boxed(
    mut v_msg_4718_: *mut leanh::LeanObject,
    mut v___y_4719_: *mut leanh::LeanObject,
    mut v___y_4720_: *mut leanh::LeanObject,
    mut v___y_4721_: *mut leanh::LeanObject,
    mut v___y_4722_: *mut leanh::LeanObject,
    mut v___y_4723_: *mut leanh::LeanObject,
    mut v___y_4724_: *mut leanh::LeanObject,
    mut v___y_4725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4726_ =
        l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(
            v_msg_4718_,
            v___y_4719_,
            v___y_4720_,
            v___y_4721_,
            v___y_4722_,
            v___y_4723_,
            v___y_4724_,
        );
    leanh::lean_dec(v___y_4724_);
    leanh::lean_dec_ref(v___y_4723_);
    leanh::lean_dec(v___y_4722_);
    leanh::lean_dec_ref(v___y_4721_);
    leanh::lean_dec(v___y_4720_);
    leanh::lean_dec_ref(v___y_4719_);
    return v_res_4726_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(
    mut v_xs_4727_: *mut leanh::LeanObject,
    mut v_sz_4728_: usize,
    mut v_i_4729_: usize,
    mut v_bs_4730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4731_: u8 = 0;
    let mut v_v_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: usize = 0;
    let mut v___x_4738_: usize = 0;
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4731_ = lean_usize_dec_lt(v_i_4729_, v_sz_4728_);
                if v___x_4731_ == 0 {
                    return v_bs_4730_;
                } else {
                    v_v_4732_ = lean_array_uget(v_bs_4730_, v_i_4729_);
                    v___x_4733_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4734_ = lean_array_uset(v_bs_4730_, v_i_4729_, v___x_4733_);
                    v___x_4735_ = l_Lean_instInhabitedExpr;
                    v___x_4736_ = lean_array_get_borrowed(v___x_4735_, v_xs_4727_, v_v_4732_);
                    leanh::lean_dec(v_v_4732_);
                    v___x_4737_ = 1usize;
                    v___x_4738_ = lean_usize_add(v_i_4729_, v___x_4737_);
                    leanh::lean_inc(v___x_4736_);
                    v___x_4739_ = lean_array_uset(v_bs_x27_4734_, v_i_4729_, v___x_4736_);
                    v_i_4729_ = v___x_4738_;
                    v_bs_4730_ = v___x_4739_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(
    mut v_xs_4741_: *mut leanh::LeanObject,
    mut v_sz_4742_: *mut leanh::LeanObject,
    mut v_i_4743_: *mut leanh::LeanObject,
    mut v_bs_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4745_: usize = 0;
    let mut v_i_boxed_4746_: usize = 0;
    let mut v_res_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4745_ = leanh::lean_unbox_usize(v_sz_4742_);
    leanh::lean_dec(v_sz_4742_);
    v_i_boxed_4746_ = leanh::lean_unbox_usize(v_i_4743_);
    leanh::lean_dec(v_i_4743_);
    v_res_4747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_4741_, v_sz_boxed_4745_, v_i_boxed_4746_, v_bs_4744_);
    leanh::lean_dec_ref(v_xs_4741_);
    return v_res_4747_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(
    mut v_xs_4748_: *mut leanh::LeanObject,
    mut v_i_4749_: *mut leanh::LeanObject,
    mut v_varDeps_4750_: *mut leanh::LeanObject,
    mut v_args_4751_: *mut leanh::LeanObject,
    mut v_body_4752_: *mut leanh::LeanObject,
    mut v_x_4753_: *mut leanh::LeanObject,
    mut v___y_4754_: *mut leanh::LeanObject,
    mut v___y_4755_: *mut leanh::LeanObject,
    mut v___y_4756_: *mut leanh::LeanObject,
    mut v___y_4757_: *mut leanh::LeanObject,
    mut v___y_4758_: *mut leanh::LeanObject,
    mut v___y_4759_: *mut leanh::LeanObject,
    mut v___y_4760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4761_ =
        l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(
            v_xs_4748_,
            v_i_4749_,
            v_varDeps_4750_,
            v_args_4751_,
            v_body_4752_,
            v_x_4753_,
            v___y_4754_,
            v___y_4755_,
            v___y_4756_,
            v___y_4757_,
            v___y_4758_,
            v___y_4759_,
        );
    leanh::lean_dec(v___y_4759_);
    leanh::lean_dec_ref(v___y_4758_);
    leanh::lean_dec(v___y_4757_);
    leanh::lean_dec_ref(v___y_4756_);
    leanh::lean_dec(v___y_4755_);
    leanh::lean_dec_ref(v___y_4754_);
    leanh::lean_dec(v_i_4749_);
    return v_res_4761_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4763_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2;
    v___x_4764_ = leanh::lean_unsigned_to_nat(30);
    v___x_4765_ = leanh::lean_unsigned_to_nat(254);
    v___x_4766_ =
        l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0;
    v___x_4767_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1;
    v___x_4768_ = l_mkPanicMessageWithDecl(
        v___x_4767_,
        v___x_4766_,
        v___x_4765_,
        v___x_4764_,
        v___x_4763_,
    );
    return v___x_4768_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(
    mut v_varDeps_4769_: *mut leanh::LeanObject,
    mut v_args_4770_: *mut leanh::LeanObject,
    mut v_f_4771_: *mut leanh::LeanObject,
    mut v_xs_4772_: *mut leanh::LeanObject,
    mut v_i_4773_: *mut leanh::LeanObject,
    mut v_a_4774_: *mut leanh::LeanObject,
    mut v_a_4775_: *mut leanh::LeanObject,
    mut v_a_4776_: *mut leanh::LeanObject,
    mut v_a_4777_: *mut leanh::LeanObject,
    mut v_a_4778_: *mut leanh::LeanObject,
    mut v_a_4779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: u8 = 0;
    v___x_4781_ = lean_array_get_size(v_args_4770_);
    v___x_4782_ = lean_nat_dec_lt(v_i_4773_, v___x_4781_);
    if v___x_4782_ == 0 {
        let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4785_: u8 = 0;
        let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_4773_);
        leanh::lean_dec_ref(v_args_4770_);
        v___x_4783_ =
            l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(
                v_f_4771_,
                v_xs_4772_,
                v_varDeps_4769_,
                v_a_4775_,
            );
        leanh::lean_dec_ref(v_varDeps_4769_);
        v_a_4784_ = leanh::lean_ctor_get(v___x_4783_, 0);
        leanh::lean_inc(v_a_4784_);
        leanh::lean_dec_ref(v___x_4783_);
        v___x_4785_ = 1;
        v___x_4786_ = l_Lean_Meta_mkLetFVars(
            v_xs_4772_,
            v_a_4784_,
            v___x_4782_,
            v___x_4782_,
            v___x_4785_,
            v_a_4776_,
            v_a_4777_,
            v_a_4778_,
            v_a_4779_,
        );
        leanh::lean_dec_ref(v_xs_4772_);
        if leanh::lean_obj_tag(v___x_4786_) == 0 {
            let mut v_a_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_4787_ = leanh::lean_ctor_get(v___x_4786_, 0);
            leanh::lean_inc(v_a_4787_);
            leanh::lean_dec_ref_known(v___x_4786_, 1);
            v___x_4788_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_4787_, v_a_4775_);
            return v___x_4788_;
        } else {
            return v___x_4786_;
        }
    } else {
        if leanh::lean_obj_tag(v_f_4771_) == 6 {
            let mut v_binderName_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderType_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_varPos_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_4793_: usize = 0;
            let mut v___x_4794_: usize = 0;
            let mut v_ys_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4797_: u8 = 0;
            let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_binderName_4789_ = leanh::lean_ctor_get(v_f_4771_, 0);
            leanh::lean_inc(v_binderName_4789_);
            v_binderType_4790_ = leanh::lean_ctor_get(v_f_4771_, 1);
            leanh::lean_inc_ref(v_binderType_4790_);
            v_body_4791_ = leanh::lean_ctor_get(v_f_4771_, 2);
            leanh::lean_inc_ref(v_body_4791_);
            leanh::lean_dec_ref_known(v_f_4771_, 3);
            v_varPos_4792_ = lean_array_fget(v_varDeps_4769_, v_i_4773_);
            v_sz_4793_ = lean_array_size(v_varPos_4792_);
            v___x_4794_ = 0usize;
            leanh::lean_inc(v_varPos_4792_);
            v_ys_4795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_4772_, v_sz_4793_, v___x_4794_, v_varPos_4792_);
            v___x_4796_ = lean_array_fget_borrowed(v_args_4770_, v_i_4773_);
            v___x_4797_ = 0;
            leanh::lean_inc(v___x_4796_);
            v___x_4798_ = l_Lean_Expr_betaRev(v___x_4796_, v_ys_4795_, v___x_4797_, v___x_4797_);
            leanh::lean_dec_ref(v_ys_4795_);
            v___x_4799_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_4798_, v_a_4775_);
            if leanh::lean_obj_tag(v___x_4799_) == 0 {
                let mut v_a_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_type_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4804_: u8 = 0;
                let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_4800_ = leanh::lean_ctor_get(v___x_4799_, 0);
                leanh::lean_inc(v_a_4800_);
                leanh::lean_dec_ref_known(v___x_4799_, 1);
                v___f_4801_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 5);
                leanh::lean_closure_set(v___f_4801_, 0, v_xs_4772_);
                leanh::lean_closure_set(v___f_4801_, 1, v_i_4773_);
                leanh::lean_closure_set(v___f_4801_, 2, v_varDeps_4769_);
                leanh::lean_closure_set(v___f_4801_, 3, v_args_4770_);
                leanh::lean_closure_set(v___f_4801_, 4, v_body_4791_);
                v___x_4802_ = lean_array_get_size(v_varPos_4792_);
                leanh::lean_dec(v_varPos_4792_);
                v_type_4803_ =
                    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(
                        v_binderType_4790_,
                        v___x_4802_,
                    );
                v___x_4804_ = 0;
                v___x_4805_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_4789_, v_type_4803_, v_a_4800_, v___f_4801_, v___x_4782_, v___x_4804_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
                return v___x_4805_;
            } else {
                leanh::lean_dec(v_varPos_4792_);
                leanh::lean_dec_ref(v_body_4791_);
                leanh::lean_dec_ref(v_binderType_4790_);
                leanh::lean_dec(v_binderName_4789_);
                leanh::lean_dec(v_i_4773_);
                leanh::lean_dec_ref(v_xs_4772_);
                leanh::lean_dec_ref(v_args_4770_);
                leanh::lean_dec_ref(v_varDeps_4769_);
                return v___x_4799_;
            }
        } else {
            let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_i_4773_);
            leanh::lean_dec_ref(v_xs_4772_);
            leanh::lean_dec_ref(v_f_4771_);
            leanh::lean_dec_ref(v_args_4770_);
            leanh::lean_dec_ref(v_varDeps_4769_);
            v___x_4806_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
            v___x_4807_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_4806_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
            return v___x_4807_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(
    mut v_xs_4808_: *mut leanh::LeanObject,
    mut v_i_4809_: *mut leanh::LeanObject,
    mut v_varDeps_4810_: *mut leanh::LeanObject,
    mut v_args_4811_: *mut leanh::LeanObject,
    mut v_body_4812_: *mut leanh::LeanObject,
    mut v_x_4813_: *mut leanh::LeanObject,
    mut v___y_4814_: *mut leanh::LeanObject,
    mut v___y_4815_: *mut leanh::LeanObject,
    mut v___y_4816_: *mut leanh::LeanObject,
    mut v___y_4817_: *mut leanh::LeanObject,
    mut v___y_4818_: *mut leanh::LeanObject,
    mut v___y_4819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4821_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_x_4813_, v___y_4815_);
    if leanh::lean_obj_tag(v___x_4821_) == 0 {
        let mut v_a_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4822_ = leanh::lean_ctor_get(v___x_4821_, 0);
        leanh::lean_inc(v_a_4822_);
        leanh::lean_dec_ref_known(v___x_4821_, 1);
        v___x_4823_ = lean_array_push(v_xs_4808_, v_a_4822_);
        v___x_4824_ = leanh::lean_unsigned_to_nat(1);
        v___x_4825_ = lean_nat_add(v_i_4809_, v___x_4824_);
        v___x_4826_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(
            v_varDeps_4810_,
            v_args_4811_,
            v_body_4812_,
            v___x_4823_,
            v___x_4825_,
            v___y_4814_,
            v___y_4815_,
            v___y_4816_,
            v___y_4817_,
            v___y_4818_,
            v___y_4819_,
        );
        return v___x_4826_;
    } else {
        leanh::lean_dec_ref(v_body_4812_);
        leanh::lean_dec_ref(v_args_4811_);
        leanh::lean_dec_ref(v_varDeps_4810_);
        leanh::lean_dec_ref(v_xs_4808_);
        return v___x_4821_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(
    mut v_varDeps_4827_: *mut leanh::LeanObject,
    mut v_args_4828_: *mut leanh::LeanObject,
    mut v_f_4829_: *mut leanh::LeanObject,
    mut v_xs_4830_: *mut leanh::LeanObject,
    mut v_i_4831_: *mut leanh::LeanObject,
    mut v_a_4832_: *mut leanh::LeanObject,
    mut v_a_4833_: *mut leanh::LeanObject,
    mut v_a_4834_: *mut leanh::LeanObject,
    mut v_a_4835_: *mut leanh::LeanObject,
    mut v_a_4836_: *mut leanh::LeanObject,
    mut v_a_4837_: *mut leanh::LeanObject,
    mut v_a_4838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4839_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(
        v_varDeps_4827_,
        v_args_4828_,
        v_f_4829_,
        v_xs_4830_,
        v_i_4831_,
        v_a_4832_,
        v_a_4833_,
        v_a_4834_,
        v_a_4835_,
        v_a_4836_,
        v_a_4837_,
    );
    leanh::lean_dec(v_a_4837_);
    leanh::lean_dec_ref(v_a_4836_);
    leanh::lean_dec(v_a_4835_);
    leanh::lean_dec_ref(v_a_4834_);
    leanh::lean_dec(v_a_4833_);
    leanh::lean_dec_ref(v_a_4832_);
    return v_res_4839_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(
    mut v_varDeps_4840_: *mut leanh::LeanObject,
    mut v_args_4841_: *mut leanh::LeanObject,
    mut v___h_4842_: *mut leanh::LeanObject,
    mut v_f_4843_: *mut leanh::LeanObject,
    mut v_xs_4844_: *mut leanh::LeanObject,
    mut v_i_4845_: *mut leanh::LeanObject,
    mut v_a_4846_: *mut leanh::LeanObject,
    mut v_a_4847_: *mut leanh::LeanObject,
    mut v_a_4848_: *mut leanh::LeanObject,
    mut v_a_4849_: *mut leanh::LeanObject,
    mut v_a_4850_: *mut leanh::LeanObject,
    mut v_a_4851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4853_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(
        v_varDeps_4840_,
        v_args_4841_,
        v_f_4843_,
        v_xs_4844_,
        v_i_4845_,
        v_a_4846_,
        v_a_4847_,
        v_a_4848_,
        v_a_4849_,
        v_a_4850_,
        v_a_4851_,
    );
    return v___x_4853_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(
    mut v_varDeps_4854_: *mut leanh::LeanObject,
    mut v_args_4855_: *mut leanh::LeanObject,
    mut v___h_4856_: *mut leanh::LeanObject,
    mut v_f_4857_: *mut leanh::LeanObject,
    mut v_xs_4858_: *mut leanh::LeanObject,
    mut v_i_4859_: *mut leanh::LeanObject,
    mut v_a_4860_: *mut leanh::LeanObject,
    mut v_a_4861_: *mut leanh::LeanObject,
    mut v_a_4862_: *mut leanh::LeanObject,
    mut v_a_4863_: *mut leanh::LeanObject,
    mut v_a_4864_: *mut leanh::LeanObject,
    mut v_a_4865_: *mut leanh::LeanObject,
    mut v_a_4866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4867_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(
        v_varDeps_4854_,
        v_args_4855_,
        v___h_4856_,
        v_f_4857_,
        v_xs_4858_,
        v_i_4859_,
        v_a_4860_,
        v_a_4861_,
        v_a_4862_,
        v_a_4863_,
        v_a_4864_,
        v_a_4865_,
    );
    leanh::lean_dec(v_a_4865_);
    leanh::lean_dec_ref(v_a_4864_);
    leanh::lean_dec(v_a_4863_);
    leanh::lean_dec_ref(v_a_4862_);
    leanh::lean_dec(v_a_4861_);
    leanh::lean_dec_ref(v_a_4860_);
    return v_res_4867_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4869_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2;
    v___x_4870_ = leanh::lean_unsigned_to_nat(40);
    v___x_4871_ = leanh::lean_unsigned_to_nat(251);
    v___x_4872_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0;
    v___x_4873_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1;
    v___x_4874_ = l_mkPanicMessageWithDecl(
        v___x_4873_,
        v___x_4872_,
        v___x_4871_,
        v___x_4870_,
        v___x_4869_,
    );
    return v___x_4874_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(
    mut v_varDeps_4875_: *mut leanh::LeanObject,
    mut v_x_4876_: *mut leanh::LeanObject,
    mut v_x_4877_: *mut leanh::LeanObject,
    mut v_x_4878_: *mut leanh::LeanObject,
    mut v___y_4879_: *mut leanh::LeanObject,
    mut v___y_4880_: *mut leanh::LeanObject,
    mut v___y_4881_: *mut leanh::LeanObject,
    mut v___y_4882_: *mut leanh::LeanObject,
    mut v___y_4883_: *mut leanh::LeanObject,
    mut v___y_4884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4876_) == 5 {
                    v_fn_4886_ = leanh::lean_ctor_get(v_x_4876_, 0);
                    leanh::lean_inc_ref(v_fn_4886_);
                    v_arg_4887_ = leanh::lean_ctor_get(v_x_4876_, 1);
                    leanh::lean_inc_ref(v_arg_4887_);
                    leanh::lean_dec_ref_known(v_x_4876_, 2);
                    v___x_4888_ = lean_array_set(v_x_4877_, v_x_4878_, v_arg_4887_);
                    v___x_4889_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4890_ = lean_nat_sub(v_x_4878_, v___x_4889_);
                    leanh::lean_dec(v_x_4878_);
                    v_x_4876_ = v_fn_4886_;
                    v_x_4877_ = v___x_4888_;
                    v_x_4878_ = v___x_4890_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_4878_);
                    v___x_4892_ = lean_array_get_size(v_x_4877_);
                    v___x_4893_ = lean_array_get_size(v_varDeps_4875_);
                    v___x_4894_ = lean_nat_dec_eq(v___x_4892_, v___x_4893_);
                    if v___x_4894_ == 0 {
                        leanh::lean_dec_ref(v_x_4877_);
                        leanh::lean_dec_ref(v_x_4876_);
                        leanh::lean_dec_ref(v_varDeps_4875_);
                        v___x_4895_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
                        v___x_4896_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_4895_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_);
                        return v___x_4896_;
                    } else {
                        v___x_4897_ = leanh::lean_unsigned_to_nat(0);
                        v___x_4898_ = l_Lean_Meta_Sym_Simp_toBetaApp___closed__0;
                        v___x_4899_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_4875_, v_x_4877_, v_x_4876_, v___x_4898_, v___x_4897_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_);
                        return v___x_4899_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(
    mut v_varDeps_4900_: *mut leanh::LeanObject,
    mut v_x_4901_: *mut leanh::LeanObject,
    mut v_x_4902_: *mut leanh::LeanObject,
    mut v_x_4903_: *mut leanh::LeanObject,
    mut v___y_4904_: *mut leanh::LeanObject,
    mut v___y_4905_: *mut leanh::LeanObject,
    mut v___y_4906_: *mut leanh::LeanObject,
    mut v___y_4907_: *mut leanh::LeanObject,
    mut v___y_4908_: *mut leanh::LeanObject,
    mut v___y_4909_: *mut leanh::LeanObject,
    mut v___y_4910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4911_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_4900_, v_x_4901_, v_x_4902_, v_x_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
    leanh::lean_dec(v___y_4909_);
    leanh::lean_dec_ref(v___y_4908_);
    leanh::lean_dec(v___y_4907_);
    leanh::lean_dec_ref(v___y_4906_);
    leanh::lean_dec(v___y_4905_);
    leanh::lean_dec_ref(v___y_4904_);
    return v_res_4911_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4912_ = leanh::lean_box(0);
    v_dummy_4913_ = l_Lean_Expr_sort___override(v___x_4912_);
    return v_dummy_4913_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(
    mut v_e_4914_: *mut leanh::LeanObject,
    mut v_varDeps_4915_: *mut leanh::LeanObject,
    mut v_a_4916_: *mut leanh::LeanObject,
    mut v_a_4917_: *mut leanh::LeanObject,
    mut v_a_4918_: *mut leanh::LeanObject,
    mut v_a_4919_: *mut leanh::LeanObject,
    mut v_a_4920_: *mut leanh::LeanObject,
    mut v_a_4921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dummy_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dummy_4923_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once
        ),
        _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0,
    );
    v_nargs_4924_ = l_Lean_Expr_getAppNumArgs(v_e_4914_);
    leanh::lean_inc(v_nargs_4924_);
    v___x_4925_ = lean_mk_array(v_nargs_4924_, v_dummy_4923_);
    v___x_4926_ = leanh::lean_unsigned_to_nat(1);
    v___x_4927_ = lean_nat_sub(v_nargs_4924_, v___x_4926_);
    leanh::lean_dec(v_nargs_4924_);
    v___x_4928_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_4915_, v_e_4914_, v___x_4925_, v___x_4927_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_);
    return v___x_4928_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(
    mut v_e_4929_: *mut leanh::LeanObject,
    mut v_varDeps_4930_: *mut leanh::LeanObject,
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
    mut v_a_4933_: *mut leanh::LeanObject,
    mut v_a_4934_: *mut leanh::LeanObject,
    mut v_a_4935_: *mut leanh::LeanObject,
    mut v_a_4936_: *mut leanh::LeanObject,
    mut v_a_4937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4938_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(
        v_e_4929_,
        v_varDeps_4930_,
        v_a_4931_,
        v_a_4932_,
        v_a_4933_,
        v_a_4934_,
        v_a_4935_,
        v_a_4936_,
    );
    leanh::lean_dec(v_a_4936_);
    leanh::lean_dec_ref(v_a_4935_);
    leanh::lean_dec(v_a_4934_);
    leanh::lean_dec_ref(v_a_4933_);
    leanh::lean_dec(v_a_4932_);
    leanh::lean_dec_ref(v_a_4931_);
    return v_res_4938_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(
    mut v_argUnivs_4939_: *mut leanh::LeanObject,
    mut v_a_4940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4946_: u8 = 0;
    let mut v_fst_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4951_: u8 = 0;
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: u8 = 0;
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4975_: u8 = 0;
    let mut v_isSharedCheck_4976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4942_ = leanh::lean_ctor_get(v_a_4940_, 1);
                v_fst_4943_ = leanh::lean_ctor_get(v_a_4940_, 0);
                v_isSharedCheck_4976_ = (!leanh::lean_is_exclusive(v_a_4940_)) as u8;
                if v_isSharedCheck_4976_ == 0 {
                    v___x_4945_ = v_a_4940_;
                    v_isShared_4946_ = v_isSharedCheck_4976_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4942_);
                    leanh::lean_inc(v_fst_4943_);
                    leanh::lean_dec(v_a_4940_);
                    v___x_4945_ = leanh::lean_box(0);
                    v_isShared_4946_ = v_isSharedCheck_4976_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_4947_ = leanh::lean_ctor_get(v_snd_4942_, 0);
                v_snd_4948_ = leanh::lean_ctor_get(v_snd_4942_, 1);
                v_isSharedCheck_4975_ = (!leanh::lean_is_exclusive(v_snd_4942_)) as u8;
                if v_isSharedCheck_4975_ == 0 {
                    v___x_4950_ = v_snd_4942_;
                    v_isShared_4951_ = v_isSharedCheck_4975_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4948_);
                    leanh::lean_inc(v_fst_4947_);
                    leanh::lean_dec(v_snd_4942_);
                    v___x_4950_ = leanh::lean_box(0);
                    v_isShared_4951_ = v_isSharedCheck_4975_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4952_ = leanh::lean_unsigned_to_nat(0);
                v___x_4953_ = lean_nat_dec_lt(v___x_4952_, v_fst_4947_);
                if v___x_4953_ == 0 {
                    if v_isShared_4951_ == 0 {
                        v___x_4955_ = v___x_4950_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4960_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_fst_4947_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4960_, 1, v_snd_4948_);
                        v___x_4955_ = v_reuseFailAlloc_4960_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_4961_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4962_ = lean_nat_sub(v_fst_4947_, v___x_4961_);
                    leanh::lean_dec(v_fst_4947_);
                    v___x_4963_ = leanh::lean_box(0);
                    v___x_4964_ =
                        lean_array_get_borrowed(v___x_4963_, v_argUnivs_4939_, v___x_4962_);
                    leanh::lean_inc(v___x_4964_);
                    v___x_4965_ = l_Lean_mkLevelIMax_x27(v___x_4964_, v_fst_4943_);
                    v___x_4966_ = l_Lean_Level_normalize(v___x_4965_);
                    leanh::lean_dec(v___x_4965_);
                    leanh::lean_inc(v___x_4966_);
                    v___x_4967_ = lean_array_push(v_snd_4948_, v___x_4966_);
                    if v_isShared_4951_ == 0 {
                        leanh::lean_ctor_set(v___x_4950_, 1, v___x_4967_);
                        leanh::lean_ctor_set(v___x_4950_, 0, v___x_4962_);
                        v___x_4969_ = v___x_4950_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4974_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4962_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4974_, 1, v___x_4967_);
                        v___x_4969_ = v_reuseFailAlloc_4974_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4946_ == 0 {
                    leanh::lean_ctor_set(v___x_4945_, 1, v___x_4955_);
                    v___x_4957_ = v___x_4945_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4959_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_fst_4943_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 1, v___x_4955_);
                    v___x_4957_ = v_reuseFailAlloc_4959_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4958_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4958_, 0, v___x_4957_);
                return v___x_4958_;
            }
            5 => {
                if v_isShared_4946_ == 0 {
                    leanh::lean_ctor_set(v___x_4945_, 1, v___x_4969_);
                    leanh::lean_ctor_set(v___x_4945_, 0, v___x_4966_);
                    v___x_4971_ = v___x_4945_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 0, v___x_4966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 1, v___x_4969_);
                    v___x_4971_ = v_reuseFailAlloc_4973_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_4940_ = v___x_4971_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(
    mut v_argUnivs_4977_: *mut leanh::LeanObject,
    mut v_a_4978_: *mut leanh::LeanObject,
    mut v___y_4979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4980_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_4977_, v_a_4978_);
    leanh::lean_dec_ref(v_argUnivs_4977_);
    return v_res_4980_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(
    mut v_type_4983_: *mut leanh::LeanObject,
    mut v_argUnivs_4984_: *mut leanh::LeanObject,
    mut v_a_4985_: *mut leanh::LeanObject,
    mut v_a_4986_: *mut leanh::LeanObject,
    mut v_a_4987_: *mut leanh::LeanObject,
    mut v_a_4988_: *mut leanh::LeanObject,
    mut v_a_4989_: *mut leanh::LeanObject,
    mut v_a_4990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderType_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5001_: u8 = 0;
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5005_: u8 = 0;
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5016_: u8 = 0;
    let mut v_snd_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5021_: u8 = 0;
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5029_: u8 = 0;
    let mut v_unused_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5031_: u8 = 0;
    let mut v_a_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5039_: u8 = 0;
    let mut v_a_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5043_: u8 = 0;
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_type_4983_) == 7 {
                    v_binderType_4992_ = leanh::lean_ctor_get(v_type_4983_, 1);
                    leanh::lean_inc_ref(v_binderType_4992_);
                    v_body_4993_ = leanh::lean_ctor_get(v_type_4983_, 2);
                    leanh::lean_inc_ref(v_body_4993_);
                    leanh::lean_dec_ref_known(v_type_4983_, 3);
                    v___x_4994_ = l_Lean_Meta_Sym_getLevel___redArg(
                        v_binderType_4992_,
                        v_a_4986_,
                        v_a_4987_,
                        v_a_4988_,
                        v_a_4989_,
                        v_a_4990_,
                    );
                    if leanh::lean_obj_tag(v___x_4994_) == 0 {
                        v_a_4995_ = leanh::lean_ctor_get(v___x_4994_, 0);
                        leanh::lean_inc(v_a_4995_);
                        leanh::lean_dec_ref_known(v___x_4994_, 1);
                        v___x_4996_ = lean_array_push(v_argUnivs_4984_, v_a_4995_);
                        v_type_4983_ = v_body_4993_;
                        v_argUnivs_4984_ = v___x_4996_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_body_4993_);
                        leanh::lean_dec_ref(v_argUnivs_4984_);
                        v_a_4998_ = leanh::lean_ctor_get(v___x_4994_, 0);
                        v_isSharedCheck_5005_ =
                            (!leanh::lean_is_exclusive(v___x_4994_)) as u8;
                        if v_isSharedCheck_5005_ == 0 {
                            v___x_5000_ = v___x_4994_;
                            v_isShared_5001_ = v_isSharedCheck_5005_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4998_);
                            leanh::lean_dec(v___x_4994_);
                            v___x_5000_ = leanh::lean_box(0);
                            v_isShared_5001_ = v_isSharedCheck_5005_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_5006_ = l_Lean_Meta_Sym_getLevel___redArg(
                        v_type_4983_,
                        v_a_4986_,
                        v_a_4987_,
                        v_a_4988_,
                        v_a_4989_,
                        v_a_4990_,
                    );
                    if leanh::lean_obj_tag(v___x_5006_) == 0 {
                        v_a_5007_ = leanh::lean_ctor_get(v___x_5006_, 0);
                        leanh::lean_inc(v_a_5007_);
                        leanh::lean_dec_ref_known(v___x_5006_, 1);
                        v___x_5008_ = lean_array_get_size(v_argUnivs_4984_);
                        v___x_5009_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0;
                        v___x_5010_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5010_, 0, v___x_5008_);
                        leanh::lean_ctor_set(v___x_5010_, 1, v___x_5009_);
                        v___x_5011_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5011_, 0, v_a_5007_);
                        leanh::lean_ctor_set(v___x_5011_, 1, v___x_5010_);
                        v___x_5012_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_4984_, v___x_5011_);
                        if leanh::lean_obj_tag(v___x_5012_) == 0 {
                            v_a_5013_ = leanh::lean_ctor_get(v___x_5012_, 0);
                            v_isSharedCheck_5031_ =
                                (!leanh::lean_is_exclusive(v___x_5012_)) as u8;
                            if v_isSharedCheck_5031_ == 0 {
                                v___x_5015_ = v___x_5012_;
                                v_isShared_5016_ = v_isSharedCheck_5031_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5013_);
                                leanh::lean_dec(v___x_5012_);
                                v___x_5015_ = leanh::lean_box(0);
                                v_isShared_5016_ = v_isSharedCheck_5031_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_argUnivs_4984_);
                            v_a_5032_ = leanh::lean_ctor_get(v___x_5012_, 0);
                            v_isSharedCheck_5039_ =
                                (!leanh::lean_is_exclusive(v___x_5012_)) as u8;
                            if v_isSharedCheck_5039_ == 0 {
                                v___x_5034_ = v___x_5012_;
                                v_isShared_5035_ = v_isSharedCheck_5039_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5032_);
                                leanh::lean_dec(v___x_5012_);
                                v___x_5034_ = leanh::lean_box(0);
                                v_isShared_5035_ = v_isSharedCheck_5039_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_argUnivs_4984_);
                        v_a_5040_ = leanh::lean_ctor_get(v___x_5006_, 0);
                        v_isSharedCheck_5047_ =
                            (!leanh::lean_is_exclusive(v___x_5006_)) as u8;
                        if v_isSharedCheck_5047_ == 0 {
                            v___x_5042_ = v___x_5006_;
                            v_isShared_5043_ = v_isSharedCheck_5047_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5040_);
                            leanh::lean_dec(v___x_5006_);
                            v___x_5042_ = leanh::lean_box(0);
                            v_isShared_5043_ = v_isSharedCheck_5047_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5001_ == 0 {
                    v___x_5003_ = v___x_5000_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
                    v___x_5003_ = v_reuseFailAlloc_5004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5003_;
            }
            3 => {
                v_snd_5017_ = leanh::lean_ctor_get(v_a_5013_, 1);
                leanh::lean_inc(v_snd_5017_);
                leanh::lean_dec(v_a_5013_);
                v_snd_5018_ = leanh::lean_ctor_get(v_snd_5017_, 1);
                v_isSharedCheck_5029_ = (!leanh::lean_is_exclusive(v_snd_5017_)) as u8;
                if v_isSharedCheck_5029_ == 0 {
                    v_unused_5030_ = leanh::lean_ctor_get(v_snd_5017_, 0);
                    leanh::lean_dec(v_unused_5030_);
                    v___x_5020_ = v_snd_5017_;
                    v_isShared_5021_ = v_isSharedCheck_5029_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5018_);
                    leanh::lean_dec(v_snd_5017_);
                    v___x_5020_ = leanh::lean_box(0);
                    v_isShared_5021_ = v_isSharedCheck_5029_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5022_ = l_Array_reverse___redArg(v_snd_5018_);
                if v_isShared_5021_ == 0 {
                    leanh::lean_ctor_set(v___x_5020_, 1, v___x_5022_);
                    leanh::lean_ctor_set(v___x_5020_, 0, v_argUnivs_4984_);
                    v___x_5024_ = v___x_5020_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5028_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_argUnivs_4984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5028_, 1, v___x_5022_);
                    v___x_5024_ = v_reuseFailAlloc_5028_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5016_ == 0 {
                    leanh::lean_ctor_set(v___x_5015_, 0, v___x_5024_);
                    v___x_5026_ = v___x_5015_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
                    v___x_5026_ = v_reuseFailAlloc_5027_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5026_;
            }
            7 => {
                if v_isShared_5035_ == 0 {
                    v___x_5037_ = v___x_5034_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5032_);
                    v___x_5037_ = v_reuseFailAlloc_5038_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5037_;
            }
            9 => {
                if v_isShared_5043_ == 0 {
                    v___x_5045_ = v___x_5042_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5046_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_a_5040_);
                    v___x_5045_ = v_reuseFailAlloc_5046_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(
    mut v_type_5048_: *mut leanh::LeanObject,
    mut v_argUnivs_5049_: *mut leanh::LeanObject,
    mut v_a_5050_: *mut leanh::LeanObject,
    mut v_a_5051_: *mut leanh::LeanObject,
    mut v_a_5052_: *mut leanh::LeanObject,
    mut v_a_5053_: *mut leanh::LeanObject,
    mut v_a_5054_: *mut leanh::LeanObject,
    mut v_a_5055_: *mut leanh::LeanObject,
    mut v_a_5056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5057_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(
        v_type_5048_,
        v_argUnivs_5049_,
        v_a_5050_,
        v_a_5051_,
        v_a_5052_,
        v_a_5053_,
        v_a_5054_,
        v_a_5055_,
    );
    leanh::lean_dec(v_a_5055_);
    leanh::lean_dec_ref(v_a_5054_);
    leanh::lean_dec(v_a_5053_);
    leanh::lean_dec_ref(v_a_5052_);
    leanh::lean_dec(v_a_5051_);
    leanh::lean_dec_ref(v_a_5050_);
    return v_res_5057_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(
    mut v_argUnivs_5058_: *mut leanh::LeanObject,
    mut v_inst_5059_: *mut leanh::LeanObject,
    mut v_a_5060_: *mut leanh::LeanObject,
    mut v___y_5061_: *mut leanh::LeanObject,
    mut v___y_5062_: *mut leanh::LeanObject,
    mut v___y_5063_: *mut leanh::LeanObject,
    mut v___y_5064_: *mut leanh::LeanObject,
    mut v___y_5065_: *mut leanh::LeanObject,
    mut v___y_5066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5068_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_5058_, v_a_5060_);
    return v___x_5068_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(
    mut v_argUnivs_5069_: *mut leanh::LeanObject,
    mut v_inst_5070_: *mut leanh::LeanObject,
    mut v_a_5071_: *mut leanh::LeanObject,
    mut v___y_5072_: *mut leanh::LeanObject,
    mut v___y_5073_: *mut leanh::LeanObject,
    mut v___y_5074_: *mut leanh::LeanObject,
    mut v___y_5075_: *mut leanh::LeanObject,
    mut v___y_5076_: *mut leanh::LeanObject,
    mut v___y_5077_: *mut leanh::LeanObject,
    mut v___y_5078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5079_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_5069_, v_inst_5070_, v_a_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_);
    leanh::lean_dec(v___y_5077_);
    leanh::lean_dec_ref(v___y_5076_);
    leanh::lean_dec(v___y_5075_);
    leanh::lean_dec_ref(v___y_5074_);
    leanh::lean_dec(v___y_5073_);
    leanh::lean_dec_ref(v___y_5072_);
    leanh::lean_dec_ref(v_argUnivs_5069_);
    return v_res_5079_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(
    mut v_fType_5080_: *mut leanh::LeanObject,
    mut v_a_5081_: *mut leanh::LeanObject,
    mut v_a_5082_: *mut leanh::LeanObject,
    mut v_a_5083_: *mut leanh::LeanObject,
    mut v_a_5084_: *mut leanh::LeanObject,
    mut v_a_5085_: *mut leanh::LeanObject,
    mut v_a_5086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5088_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0;
    v___x_5089_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(
        v_fType_5080_,
        v___x_5088_,
        v_a_5081_,
        v_a_5082_,
        v_a_5083_,
        v_a_5084_,
        v_a_5085_,
        v_a_5086_,
    );
    return v___x_5089_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(
    mut v_fType_5090_: *mut leanh::LeanObject,
    mut v_a_5091_: *mut leanh::LeanObject,
    mut v_a_5092_: *mut leanh::LeanObject,
    mut v_a_5093_: *mut leanh::LeanObject,
    mut v_a_5094_: *mut leanh::LeanObject,
    mut v_a_5095_: *mut leanh::LeanObject,
    mut v_a_5096_: *mut leanh::LeanObject,
    mut v_a_5097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5098_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(
        v_fType_5090_,
        v_a_5091_,
        v_a_5092_,
        v_a_5093_,
        v_a_5094_,
        v_a_5095_,
        v_a_5096_,
    );
    leanh::lean_dec(v_a_5096_);
    leanh::lean_dec_ref(v_a_5095_);
    leanh::lean_dec(v_a_5094_);
    leanh::lean_dec_ref(v_a_5093_);
    leanh::lean_dec(v_a_5092_);
    leanh::lean_dec_ref(v_a_5091_);
    return v_res_5098_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(
    mut v_fnUnivs_5099_: *mut leanh::LeanObject,
    mut v_argUnivs_5100_: *mut leanh::LeanObject,
    mut v_declName_5101_: *mut leanh::LeanObject,
    mut v_fType_5102_: *mut leanh::LeanObject,
    mut v_i_5103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b1_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b2_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5105_ = leanh::lean_box(0);
    v_00_u03b1_5106_ = l_Lean_Expr_bindingDomain_x21(v_fType_5102_);
    v_00_u03b2_5107_ = l_Lean_Expr_bindingBody_x21(v_fType_5102_);
    v_u_5108_ = lean_array_get_borrowed(v___x_5105_, v_argUnivs_5100_, v_i_5103_);
    v_v_5109_ = lean_array_get_borrowed(v___x_5105_, v_fnUnivs_5099_, v_i_5103_);
    v___x_5110_ = leanh::lean_box(0);
    leanh::lean_inc(v_v_5109_);
    v___x_5111_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5111_, 0, v_v_5109_);
    leanh::lean_ctor_set(v___x_5111_, 1, v___x_5110_);
    leanh::lean_inc(v_u_5108_);
    v___x_5112_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5112_, 0, v_u_5108_);
    leanh::lean_ctor_set(v___x_5112_, 1, v___x_5111_);
    v___x_5113_ = l_Lean_mkConst(v_declName_5101_, v___x_5112_);
    v___x_5114_ = l_Lean_mkAppB(v___x_5113_, v_00_u03b1_5106_, v_00_u03b2_5107_);
    v___x_5115_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5115_, 0, v___x_5114_);
    return v___x_5115_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(
    mut v_fnUnivs_5116_: *mut leanh::LeanObject,
    mut v_argUnivs_5117_: *mut leanh::LeanObject,
    mut v_declName_5118_: *mut leanh::LeanObject,
    mut v_fType_5119_: *mut leanh::LeanObject,
    mut v_i_5120_: *mut leanh::LeanObject,
    mut v_a_5121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5122_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_5116_, v_argUnivs_5117_, v_declName_5118_, v_fType_5119_, v_i_5120_);
    leanh::lean_dec(v_i_5120_);
    leanh::lean_dec_ref(v_fType_5119_);
    leanh::lean_dec_ref(v_argUnivs_5117_);
    leanh::lean_dec_ref(v_fnUnivs_5116_);
    return v_res_5122_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(
    mut v_fnUnivs_5123_: *mut leanh::LeanObject,
    mut v_argUnivs_5124_: *mut leanh::LeanObject,
    mut v_declName_5125_: *mut leanh::LeanObject,
    mut v_fType_5126_: *mut leanh::LeanObject,
    mut v_i_5127_: *mut leanh::LeanObject,
    mut v_a_5128_: *mut leanh::LeanObject,
    mut v_a_5129_: *mut leanh::LeanObject,
    mut v_a_5130_: *mut leanh::LeanObject,
    mut v_a_5131_: *mut leanh::LeanObject,
    mut v_a_5132_: *mut leanh::LeanObject,
    mut v_a_5133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5135_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_5123_, v_argUnivs_5124_, v_declName_5125_, v_fType_5126_, v_i_5127_);
    return v___x_5135_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(
    mut v_fnUnivs_5136_: *mut leanh::LeanObject,
    mut v_argUnivs_5137_: *mut leanh::LeanObject,
    mut v_declName_5138_: *mut leanh::LeanObject,
    mut v_fType_5139_: *mut leanh::LeanObject,
    mut v_i_5140_: *mut leanh::LeanObject,
    mut v_a_5141_: *mut leanh::LeanObject,
    mut v_a_5142_: *mut leanh::LeanObject,
    mut v_a_5143_: *mut leanh::LeanObject,
    mut v_a_5144_: *mut leanh::LeanObject,
    mut v_a_5145_: *mut leanh::LeanObject,
    mut v_a_5146_: *mut leanh::LeanObject,
    mut v_a_5147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5148_ =
        l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(
            v_fnUnivs_5136_,
            v_argUnivs_5137_,
            v_declName_5138_,
            v_fType_5139_,
            v_i_5140_,
            v_a_5141_,
            v_a_5142_,
            v_a_5143_,
            v_a_5144_,
            v_a_5145_,
            v_a_5146_,
        );
    leanh::lean_dec(v_a_5146_);
    leanh::lean_dec_ref(v_a_5145_);
    leanh::lean_dec(v_a_5144_);
    leanh::lean_dec_ref(v_a_5143_);
    leanh::lean_dec(v_a_5142_);
    leanh::lean_dec_ref(v_a_5141_);
    leanh::lean_dec(v_i_5140_);
    leanh::lean_dec_ref(v_fType_5139_);
    leanh::lean_dec_ref(v_argUnivs_5137_);
    leanh::lean_dec_ref(v_fnUnivs_5136_);
    return v_res_5148_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(
    mut v_f_5149_: *mut leanh::LeanObject,
    mut v_a_5150_: *mut leanh::LeanObject,
    mut v___y_5151_: *mut leanh::LeanObject,
    mut v___y_5152_: *mut leanh::LeanObject,
    mut v___y_5153_: *mut leanh::LeanObject,
    mut v___y_5154_: *mut leanh::LeanObject,
    mut v___y_5155_: *mut leanh::LeanObject,
    mut v___y_5156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_5163_: u8 = 0;
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5169_: u8 = 0;
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5173_: u8 = 0;
    let mut v_a_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5177_: u8 = 0;
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5162_ = lean_st_ref_get(v___y_5152_);
                v_debug_5163_ = leanh::lean_ctor_get_uint8(
                    v___x_5162_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                leanh::lean_dec(v___x_5162_);
                if v_debug_5163_ == 0 {
                    v___y_5159_ = v___y_5152_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_f_5149_);
                    v___x_5164_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_5149_,
                        v___y_5151_,
                        v___y_5152_,
                        v___y_5153_,
                        v___y_5154_,
                        v___y_5155_,
                        v___y_5156_,
                    );
                    if leanh::lean_obj_tag(v___x_5164_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5164_, 1);
                        leanh::lean_inc_ref(v_a_5150_);
                        v___x_5165_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_5150_,
                            v___y_5151_,
                            v___y_5152_,
                            v___y_5153_,
                            v___y_5154_,
                            v___y_5155_,
                            v___y_5156_,
                        );
                        if leanh::lean_obj_tag(v___x_5165_) == 0 {
                            leanh::lean_dec_ref_known(v___x_5165_, 1);
                            v___y_5159_ = v___y_5152_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_a_5150_);
                            leanh::lean_dec_ref(v_f_5149_);
                            v_a_5166_ = leanh::lean_ctor_get(v___x_5165_, 0);
                            v_isSharedCheck_5173_ =
                                (!leanh::lean_is_exclusive(v___x_5165_)) as u8;
                            if v_isSharedCheck_5173_ == 0 {
                                v___x_5168_ = v___x_5165_;
                                v_isShared_5169_ = v_isSharedCheck_5173_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5166_);
                                leanh::lean_dec(v___x_5165_);
                                v___x_5168_ = leanh::lean_box(0);
                                v_isShared_5169_ = v_isSharedCheck_5173_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_5150_);
                        leanh::lean_dec_ref(v_f_5149_);
                        v_a_5174_ = leanh::lean_ctor_get(v___x_5164_, 0);
                        v_isSharedCheck_5181_ =
                            (!leanh::lean_is_exclusive(v___x_5164_)) as u8;
                        if v_isSharedCheck_5181_ == 0 {
                            v___x_5176_ = v___x_5164_;
                            v_isShared_5177_ = v_isSharedCheck_5181_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5174_);
                            leanh::lean_dec(v___x_5164_);
                            v___x_5176_ = leanh::lean_box(0);
                            v_isShared_5177_ = v_isSharedCheck_5181_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5160_ = l_Lean_Expr_app___override(v_f_5149_, v_a_5150_);
                v___x_5161_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_5160_, v___y_5159_);
                return v___x_5161_;
            }
            2 => {
                if v_isShared_5169_ == 0 {
                    v___x_5171_ = v___x_5168_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5172_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
                    v___x_5171_ = v_reuseFailAlloc_5172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5171_;
            }
            4 => {
                if v_isShared_5177_ == 0 {
                    v___x_5179_ = v___x_5176_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5180_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5174_);
                    v___x_5179_ = v_reuseFailAlloc_5180_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(
    mut v_f_5182_: *mut leanh::LeanObject,
    mut v_a_5183_: *mut leanh::LeanObject,
    mut v___y_5184_: *mut leanh::LeanObject,
    mut v___y_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
    mut v___y_5187_: *mut leanh::LeanObject,
    mut v___y_5188_: *mut leanh::LeanObject,
    mut v___y_5189_: *mut leanh::LeanObject,
    mut v___y_5190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5191_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_5182_, v_a_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_);
    leanh::lean_dec(v___y_5189_);
    leanh::lean_dec_ref(v___y_5188_);
    leanh::lean_dec(v___y_5187_);
    leanh::lean_dec_ref(v___y_5186_);
    leanh::lean_dec(v___y_5185_);
    leanh::lean_dec_ref(v___y_5184_);
    return v_res_5191_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(
    mut v_f_5192_: *mut leanh::LeanObject,
    mut v_a_5193_: *mut leanh::LeanObject,
    mut v___y_5194_: *mut leanh::LeanObject,
    mut v___y_5195_: *mut leanh::LeanObject,
    mut v___y_5196_: *mut leanh::LeanObject,
    mut v___y_5197_: *mut leanh::LeanObject,
    mut v___y_5198_: *mut leanh::LeanObject,
    mut v___y_5199_: *mut leanh::LeanObject,
    mut v___y_5200_: *mut leanh::LeanObject,
    mut v___y_5201_: *mut leanh::LeanObject,
    mut v___y_5202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5204_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_5192_, v_a_5193_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
    return v___x_5204_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(
    mut v_f_5205_: *mut leanh::LeanObject,
    mut v_a_5206_: *mut leanh::LeanObject,
    mut v___y_5207_: *mut leanh::LeanObject,
    mut v___y_5208_: *mut leanh::LeanObject,
    mut v___y_5209_: *mut leanh::LeanObject,
    mut v___y_5210_: *mut leanh::LeanObject,
    mut v___y_5211_: *mut leanh::LeanObject,
    mut v___y_5212_: *mut leanh::LeanObject,
    mut v___y_5213_: *mut leanh::LeanObject,
    mut v___y_5214_: *mut leanh::LeanObject,
    mut v___y_5215_: *mut leanh::LeanObject,
    mut v___y_5216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5217_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_5205_, v_a_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
    leanh::lean_dec(v___y_5215_);
    leanh::lean_dec_ref(v___y_5214_);
    leanh::lean_dec(v___y_5213_);
    leanh::lean_dec_ref(v___y_5212_);
    leanh::lean_dec(v___y_5211_);
    leanh::lean_dec_ref(v___y_5210_);
    leanh::lean_dec(v___y_5209_);
    leanh::lean_dec_ref(v___y_5208_);
    leanh::lean_dec(v___y_5207_);
    return v_res_5217_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5218_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(leanh::lean_box(0));
    return v___x_5218_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(
    mut v_msg_5219_: *mut leanh::LeanObject,
    mut v___y_5220_: *mut leanh::LeanObject,
    mut v___y_5221_: *mut leanh::LeanObject,
    mut v___y_5222_: *mut leanh::LeanObject,
    mut v___y_5223_: *mut leanh::LeanObject,
    mut v___y_5224_: *mut leanh::LeanObject,
    mut v___y_5225_: *mut leanh::LeanObject,
    mut v___y_5226_: *mut leanh::LeanObject,
    mut v___y_5227_: *mut leanh::LeanObject,
    mut v___y_5228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_15370__overap_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5230_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
    v___x_15370__overap_5231_ = lean_panic_fn_borrowed(v___x_5230_, v_msg_5219_);
    leanh::lean_inc(v___y_5228_);
    leanh::lean_inc_ref(v___y_5227_);
    leanh::lean_inc(v___y_5226_);
    leanh::lean_inc_ref(v___y_5225_);
    leanh::lean_inc(v___y_5224_);
    leanh::lean_inc_ref(v___y_5223_);
    leanh::lean_inc(v___y_5222_);
    leanh::lean_inc_ref(v___y_5221_);
    leanh::lean_inc(v___y_5220_);
    v___x_5232_ = leanh::lean_apply_10(
        v___x_15370__overap_5231_,
        v___y_5220_,
        v___y_5221_,
        v___y_5222_,
        v___y_5223_,
        v___y_5224_,
        v___y_5225_,
        v___y_5226_,
        v___y_5227_,
        v___y_5228_,
        leanh::lean_box(0),
    );
    return v___x_5232_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(
    mut v_msg_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
    mut v___y_5237_: *mut leanh::LeanObject,
    mut v___y_5238_: *mut leanh::LeanObject,
    mut v___y_5239_: *mut leanh::LeanObject,
    mut v___y_5240_: *mut leanh::LeanObject,
    mut v___y_5241_: *mut leanh::LeanObject,
    mut v___y_5242_: *mut leanh::LeanObject,
    mut v___y_5243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5244_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
    leanh::lean_dec(v___y_5242_);
    leanh::lean_dec_ref(v___y_5241_);
    leanh::lean_dec(v___y_5240_);
    leanh::lean_dec_ref(v___y_5239_);
    leanh::lean_dec(v___y_5238_);
    leanh::lean_dec_ref(v___y_5237_);
    leanh::lean_dec(v___y_5236_);
    leanh::lean_dec_ref(v___y_5235_);
    leanh::lean_dec(v___y_5234_);
    return v_res_5244_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5255_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2;
    v___x_5256_ = leanh::lean_unsigned_to_nat(11);
    v___x_5257_ = leanh::lean_unsigned_to_nat(346);
    v___x_5258_ =
        l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6;
    v___x_5259_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1;
    v___x_5260_ = l_mkPanicMessageWithDecl(
        v___x_5259_,
        v___x_5258_,
        v___x_5257_,
        v___x_5256_,
        v___x_5255_,
    );
    return v___x_5260_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(
    mut v_fType_5261_: *mut leanh::LeanObject,
    mut v_fnUnivs_5262_: *mut leanh::LeanObject,
    mut v_argUnivs_5263_: *mut leanh::LeanObject,
    mut v_simpBody_5264_: *mut leanh::LeanObject,
    mut v_e_5265_: *mut leanh::LeanObject,
    mut v_i_5266_: *mut leanh::LeanObject,
    mut v_a_5267_: *mut leanh::LeanObject,
    mut v_a_5268_: *mut leanh::LeanObject,
    mut v_a_5269_: *mut leanh::LeanObject,
    mut v_a_5270_: *mut leanh::LeanObject,
    mut v_a_5271_: *mut leanh::LeanObject,
    mut v_a_5272_: *mut leanh::LeanObject,
    mut v_a_5273_: *mut leanh::LeanObject,
    mut v_a_5274_: *mut leanh::LeanObject,
    mut v_a_5275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5285_: u8 = 0;
    let mut v_fst_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5290_: u8 = 0;
    let mut v_r_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5303_: u8 = 0;
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5305_: u8 = 0;
    let mut v_contextDependent_5306_: u8 = 0;
    let mut v_contextDependent_5307_: u8 = 0;
    let mut v_e_x27_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5310_: u8 = 0;
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5313_: u8 = 0;
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: u8 = 0;
    let mut v___y_5322_: u8 = 0;
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5329_: u8 = 0;
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5333_: u8 = 0;
    let mut v_isSharedCheck_5334_: u8 = 0;
    let mut v_e_x27_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5337_: u8 = 0;
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5340_: u8 = 0;
    let mut v_contextDependent_5341_: u8 = 0;
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: u8 = 0;
    let mut v___y_5350_: u8 = 0;
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5357_: u8 = 0;
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5361_: u8 = 0;
    let mut v_isSharedCheck_5362_: u8 = 0;
    let mut v_e_x27_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5365_: u8 = 0;
    let mut v_e_x27_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5368_: u8 = 0;
    let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5371_: u8 = 0;
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: u8 = 0;
    let mut v___y_5380_: u8 = 0;
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5387_: u8 = 0;
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5391_: u8 = 0;
    let mut v_isSharedCheck_5392_: u8 = 0;
    let mut v_a_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5400_: u8 = 0;
    let mut v_isSharedCheck_5401_: u8 = 0;
    let mut v_isSharedCheck_5402_: u8 = 0;
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5407_: u8 = 0;
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5412_: u8 = 0;
    let mut v_a_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_e_5265_) {
                    5 => {
                        v_fn_5277_ = leanh::lean_ctor_get(v_e_5265_, 0);
                        leanh::lean_inc_ref_n(v_fn_5277_, 2);
                        v_arg_5278_ = leanh::lean_ctor_get(v_e_5265_, 1);
                        leanh::lean_inc_ref(v_arg_5278_);
                        leanh::lean_dec_ref_known(v_e_5265_, 2);
                        v___x_5279_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5280_ = lean_nat_sub(v_i_5266_, v___x_5279_);
                        v___x_5281_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_5261_, v_fnUnivs_5262_, v_argUnivs_5263_, v_simpBody_5264_, v_fn_5277_, v___x_5280_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
                        leanh::lean_dec(v___x_5280_);
                        if leanh::lean_obj_tag(v___x_5281_) == 0 {
                            v_a_5282_ = leanh::lean_ctor_get(v___x_5281_, 0);
                            v_isSharedCheck_5402_ =
                                (!leanh::lean_is_exclusive(v___x_5281_)) as u8;
                            if v_isSharedCheck_5402_ == 0 {
                                v___x_5284_ = v___x_5281_;
                                v_isShared_5285_ = v_isSharedCheck_5402_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5282_);
                                leanh::lean_dec(v___x_5281_);
                                v___x_5284_ = leanh::lean_box(0);
                                v_isShared_5285_ = v_isSharedCheck_5402_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_5278_);
                            leanh::lean_dec_ref(v_fn_5277_);
                            return v___x_5281_;
                        }
                    }
                    6 => {
                        leanh::lean_inc(v_a_5275_);
                        leanh::lean_inc_ref(v_a_5274_);
                        leanh::lean_inc(v_a_5273_);
                        leanh::lean_inc_ref(v_a_5272_);
                        leanh::lean_inc(v_a_5271_);
                        leanh::lean_inc_ref(v_a_5270_);
                        leanh::lean_inc(v_a_5269_);
                        leanh::lean_inc_ref(v_a_5268_);
                        leanh::lean_inc(v_a_5267_);
                        v___x_5403_ = leanh::lean_apply_11(
                            v_simpBody_5264_,
                            v_e_5265_,
                            v_a_5267_,
                            v_a_5268_,
                            v_a_5269_,
                            v_a_5270_,
                            v_a_5271_,
                            v_a_5272_,
                            v_a_5273_,
                            v_a_5274_,
                            v_a_5275_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_5403_) == 0 {
                            v_a_5404_ = leanh::lean_ctor_get(v___x_5403_, 0);
                            v_isSharedCheck_5412_ =
                                (!leanh::lean_is_exclusive(v___x_5403_)) as u8;
                            if v_isSharedCheck_5412_ == 0 {
                                v___x_5406_ = v___x_5403_;
                                v_isShared_5407_ = v_isSharedCheck_5412_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5404_);
                                leanh::lean_dec(v___x_5403_);
                                v___x_5406_ = leanh::lean_box(0);
                                v_isShared_5407_ = v_isSharedCheck_5412_;
                                state = 24;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_fType_5261_);
                            v_a_5413_ = leanh::lean_ctor_get(v___x_5403_, 0);
                            v_isSharedCheck_5420_ =
                                (!leanh::lean_is_exclusive(v___x_5403_)) as u8;
                            if v_isSharedCheck_5420_ == 0 {
                                v___x_5415_ = v___x_5403_;
                                v_isShared_5416_ = v_isSharedCheck_5420_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5413_);
                                leanh::lean_dec(v___x_5403_);
                                v___x_5415_ = leanh::lean_box(0);
                                v_isShared_5416_ = v_isSharedCheck_5420_;
                                state = 26;
                                continue;
                            }
                        }
                    }
                    _ => {
                        leanh::lean_dec_ref(v_e_5265_);
                        leanh::lean_dec_ref(v_simpBody_5264_);
                        leanh::lean_dec_ref(v_fType_5261_);
                        v___x_5421_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once), _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
                        v___x_5422_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_5421_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
                        return v___x_5422_;
                    }
                }
            }
            1 => {
                v_fst_5286_ = leanh::lean_ctor_get(v_a_5282_, 0);
                v_snd_5287_ = leanh::lean_ctor_get(v_a_5282_, 1);
                v_isSharedCheck_5401_ = (!leanh::lean_is_exclusive(v_a_5282_)) as u8;
                if v_isSharedCheck_5401_ == 0 {
                    v___x_5289_ = v_a_5282_;
                    v_isShared_5290_ = v_isSharedCheck_5401_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5287_);
                    leanh::lean_inc(v_fst_5286_);
                    leanh::lean_dec(v_a_5282_);
                    v___x_5289_ = leanh::lean_box(0);
                    v_isShared_5290_ = v_isSharedCheck_5401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_a_5275_);
                leanh::lean_inc_ref(v_a_5274_);
                leanh::lean_inc(v_a_5273_);
                leanh::lean_inc_ref(v_a_5272_);
                leanh::lean_inc(v_a_5271_);
                leanh::lean_inc_ref(v_a_5270_);
                leanh::lean_inc(v_a_5269_);
                leanh::lean_inc_ref(v_a_5268_);
                leanh::lean_inc(v_a_5267_);
                leanh::lean_inc_ref(v_arg_5278_);
                v___x_5300_ = lean_sym_simp(
                    v_arg_5278_,
                    v_a_5267_,
                    v_a_5268_,
                    v_a_5269_,
                    v_a_5270_,
                    v_a_5271_,
                    v_a_5272_,
                    v_a_5273_,
                    v_a_5274_,
                    v_a_5275_,
                );
                if leanh::lean_obj_tag(v___x_5300_) == 0 {
                    v_a_5301_ = leanh::lean_ctor_get(v___x_5300_, 0);
                    leanh::lean_inc(v_a_5301_);
                    leanh::lean_dec_ref_known(v___x_5300_, 1);
                    if leanh::lean_obj_tag(v_fst_5286_) == 0 {
                        if leanh::lean_obj_tag(v_a_5301_) == 0 {
                            leanh::lean_dec_ref(v_arg_5278_);
                            leanh::lean_dec_ref(v_fn_5277_);
                            v_contextDependent_5305_ =
                                leanh::lean_ctor_get_uint8(v_fst_5286_, 1 as u32);
                            leanh::lean_dec_ref_known(v_fst_5286_, 0);
                            if v_contextDependent_5305_ == 0 {
                                v_contextDependent_5306_ =
                                    leanh::lean_ctor_get_uint8(v_a_5301_, 1 as u32);
                                leanh::lean_dec_ref_known(v_a_5301_, 0);
                                v___y_5303_ = v_contextDependent_5306_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_a_5301_, 0);
                                v___y_5303_ = v_contextDependent_5305_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_contextDependent_5307_ =
                                leanh::lean_ctor_get_uint8(v_fst_5286_, 1 as u32);
                            leanh::lean_dec_ref_known(v_fst_5286_, 0);
                            v_e_x27_5308_ = leanh::lean_ctor_get(v_a_5301_, 0);
                            v_proof_5309_ = leanh::lean_ctor_get(v_a_5301_, 1);
                            v_contextDependent_5310_ = leanh::lean_ctor_get_uint8(
                                v_a_5301_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                    as u32,
                            );
                            v_isSharedCheck_5334_ =
                                (!leanh::lean_is_exclusive(v_a_5301_)) as u8;
                            if v_isSharedCheck_5334_ == 0 {
                                v___x_5312_ = v_a_5301_;
                                v_isShared_5313_ = v_isSharedCheck_5334_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_proof_5309_);
                                leanh::lean_inc(v_e_x27_5308_);
                                leanh::lean_dec(v_a_5301_);
                                v___x_5312_ = leanh::lean_box(0);
                                v_isShared_5313_ = v_isSharedCheck_5334_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v_a_5301_) == 0 {
                            v_e_x27_5335_ = leanh::lean_ctor_get(v_fst_5286_, 0);
                            v_proof_5336_ = leanh::lean_ctor_get(v_fst_5286_, 1);
                            v_contextDependent_5337_ = leanh::lean_ctor_get_uint8(
                                v_fst_5286_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                    as u32,
                            );
                            v_isSharedCheck_5362_ =
                                (!leanh::lean_is_exclusive(v_fst_5286_)) as u8;
                            if v_isSharedCheck_5362_ == 0 {
                                v___x_5339_ = v_fst_5286_;
                                v_isShared_5340_ = v_isSharedCheck_5362_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_proof_5336_);
                                leanh::lean_inc(v_e_x27_5335_);
                                leanh::lean_dec(v_fst_5286_);
                                v___x_5339_ = leanh::lean_box(0);
                                v_isShared_5340_ = v_isSharedCheck_5362_;
                                state = 12;
                                continue;
                            }
                        } else {
                            v_e_x27_5363_ = leanh::lean_ctor_get(v_fst_5286_, 0);
                            leanh::lean_inc_ref(v_e_x27_5363_);
                            v_proof_5364_ = leanh::lean_ctor_get(v_fst_5286_, 1);
                            leanh::lean_inc_ref(v_proof_5364_);
                            v_contextDependent_5365_ = leanh::lean_ctor_get_uint8(
                                v_fst_5286_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                    as u32,
                            );
                            leanh::lean_dec_ref_known(v_fst_5286_, 2);
                            v_e_x27_5366_ = leanh::lean_ctor_get(v_a_5301_, 0);
                            v_proof_5367_ = leanh::lean_ctor_get(v_a_5301_, 1);
                            v_contextDependent_5368_ = leanh::lean_ctor_get_uint8(
                                v_a_5301_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                    as u32,
                            );
                            v_isSharedCheck_5392_ =
                                (!leanh::lean_is_exclusive(v_a_5301_)) as u8;
                            if v_isSharedCheck_5392_ == 0 {
                                v___x_5370_ = v_a_5301_;
                                v_isShared_5371_ = v_isSharedCheck_5392_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_proof_5367_);
                                leanh::lean_inc(v_e_x27_5366_);
                                leanh::lean_dec(v_a_5301_);
                                v___x_5370_ = leanh::lean_box(0);
                                v_isShared_5371_ = v_isSharedCheck_5392_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5289_);
                    leanh::lean_dec(v_snd_5287_);
                    leanh::lean_dec(v_fst_5286_);
                    leanh::lean_del_object(v___x_5284_);
                    leanh::lean_dec_ref(v_arg_5278_);
                    leanh::lean_dec_ref(v_fn_5277_);
                    v_a_5393_ = leanh::lean_ctor_get(v___x_5300_, 0);
                    v_isSharedCheck_5400_ = (!leanh::lean_is_exclusive(v___x_5300_)) as u8;
                    if v_isSharedCheck_5400_ == 0 {
                        v___x_5395_ = v___x_5300_;
                        v_isShared_5396_ = v_isSharedCheck_5400_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5393_);
                        leanh::lean_dec(v___x_5300_);
                        v___x_5395_ = leanh::lean_box(0);
                        v_isShared_5396_ = v_isSharedCheck_5400_;
                        state = 22;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5293_ = l_Lean_Expr_bindingBody_x21(v_snd_5287_);
                leanh::lean_dec(v_snd_5287_);
                if v_isShared_5290_ == 0 {
                    leanh::lean_ctor_set(v___x_5289_, 1, v___x_5293_);
                    leanh::lean_ctor_set(v___x_5289_, 0, v_r_5292_);
                    v___x_5295_ = v___x_5289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5299_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_r_5292_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5299_, 1, v___x_5293_);
                    v___x_5295_ = v_reuseFailAlloc_5299_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5285_ == 0 {
                    leanh::lean_ctor_set(v___x_5284_, 0, v___x_5295_);
                    v___x_5297_ = v___x_5284_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5298_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5295_);
                    v___x_5297_ = v_reuseFailAlloc_5298_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5297_;
            }
            6 => {
                v___x_5304_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_5303_);
                v_r_5292_ = v___x_5304_;
                state = 3;
                continue;
            }
            7 => {
                leanh::lean_inc_ref(v_e_x27_5308_);
                leanh::lean_inc_ref(v_fn_5277_);
                v___x_5314_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_5277_, v_e_x27_5308_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
                if leanh::lean_obj_tag(v___x_5314_) == 0 {
                    v_a_5315_ = leanh::lean_ctor_get(v___x_5314_, 0);
                    leanh::lean_inc(v_a_5315_);
                    leanh::lean_dec_ref_known(v___x_5314_, 1);
                    v___x_5316_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1;
                    v___x_5317_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_5262_, v_argUnivs_5263_, v___x_5316_, v_snd_5287_, v_i_5266_);
                    v_a_5318_ = leanh::lean_ctor_get(v___x_5317_, 0);
                    leanh::lean_inc(v_a_5318_);
                    leanh::lean_dec_ref(v___x_5317_);
                    v___x_5319_ = l_Lean_mkApp4(
                        v_a_5318_,
                        v_arg_5278_,
                        v_e_x27_5308_,
                        v_fn_5277_,
                        v_proof_5309_,
                    );
                    v___x_5320_ = 0;
                    if v_contextDependent_5307_ == 0 {
                        v___y_5322_ = v_contextDependent_5310_;
                        state = 8;
                        continue;
                    } else {
                        v___y_5322_ = v_contextDependent_5307_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5312_);
                    leanh::lean_dec_ref(v_proof_5309_);
                    leanh::lean_dec_ref(v_e_x27_5308_);
                    leanh::lean_del_object(v___x_5289_);
                    leanh::lean_dec(v_snd_5287_);
                    leanh::lean_del_object(v___x_5284_);
                    leanh::lean_dec_ref(v_arg_5278_);
                    leanh::lean_dec_ref(v_fn_5277_);
                    v_a_5326_ = leanh::lean_ctor_get(v___x_5314_, 0);
                    v_isSharedCheck_5333_ = (!leanh::lean_is_exclusive(v___x_5314_)) as u8;
                    if v_isSharedCheck_5333_ == 0 {
                        v___x_5328_ = v___x_5314_;
                        v_isShared_5329_ = v_isSharedCheck_5333_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5326_);
                        leanh::lean_dec(v___x_5314_);
                        v___x_5328_ = leanh::lean_box(0);
                        v_isShared_5329_ = v_isSharedCheck_5333_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5313_ == 0 {
                    leanh::lean_ctor_set(v___x_5312_, 1, v___x_5319_);
                    leanh::lean_ctor_set(v___x_5312_, 0, v_a_5315_);
                    v___x_5324_ = v___x_5312_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5325_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 1, v___x_5319_);
                    v___x_5324_ = v_reuseFailAlloc_5325_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5324_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5320_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5324_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_5322_,
                );
                v_r_5292_ = v___x_5324_;
                state = 3;
                continue;
            }
            10 => {
                if v_isShared_5329_ == 0 {
                    v___x_5331_ = v___x_5328_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
                    v___x_5331_ = v_reuseFailAlloc_5332_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5331_;
            }
            12 => {
                v_contextDependent_5341_ = leanh::lean_ctor_get_uint8(v_a_5301_, 1 as u32);
                leanh::lean_dec_ref_known(v_a_5301_, 0);
                leanh::lean_inc_ref(v_arg_5278_);
                leanh::lean_inc_ref(v_e_x27_5335_);
                v___x_5342_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_5335_, v_arg_5278_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
                if leanh::lean_obj_tag(v___x_5342_) == 0 {
                    v_a_5343_ = leanh::lean_ctor_get(v___x_5342_, 0);
                    leanh::lean_inc(v_a_5343_);
                    leanh::lean_dec_ref_known(v___x_5342_, 1);
                    v___x_5344_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3;
                    v___x_5345_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_5262_, v_argUnivs_5263_, v___x_5344_, v_snd_5287_, v_i_5266_);
                    v_a_5346_ = leanh::lean_ctor_get(v___x_5345_, 0);
                    leanh::lean_inc(v_a_5346_);
                    leanh::lean_dec_ref(v___x_5345_);
                    v___x_5347_ = l_Lean_mkApp4(
                        v_a_5346_,
                        v_fn_5277_,
                        v_e_x27_5335_,
                        v_proof_5336_,
                        v_arg_5278_,
                    );
                    v___x_5348_ = 0;
                    if v_contextDependent_5337_ == 0 {
                        v___y_5350_ = v_contextDependent_5341_;
                        state = 13;
                        continue;
                    } else {
                        v___y_5350_ = v_contextDependent_5337_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5339_);
                    leanh::lean_dec_ref(v_proof_5336_);
                    leanh::lean_dec_ref(v_e_x27_5335_);
                    leanh::lean_del_object(v___x_5289_);
                    leanh::lean_dec(v_snd_5287_);
                    leanh::lean_del_object(v___x_5284_);
                    leanh::lean_dec_ref(v_arg_5278_);
                    leanh::lean_dec_ref(v_fn_5277_);
                    v_a_5354_ = leanh::lean_ctor_get(v___x_5342_, 0);
                    v_isSharedCheck_5361_ = (!leanh::lean_is_exclusive(v___x_5342_)) as u8;
                    if v_isSharedCheck_5361_ == 0 {
                        v___x_5356_ = v___x_5342_;
                        v_isShared_5357_ = v_isSharedCheck_5361_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5354_);
                        leanh::lean_dec(v___x_5342_);
                        v___x_5356_ = leanh::lean_box(0);
                        v_isShared_5357_ = v_isSharedCheck_5361_;
                        state = 15;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_5340_ == 0 {
                    leanh::lean_ctor_set(v___x_5339_, 1, v___x_5347_);
                    leanh::lean_ctor_set(v___x_5339_, 0, v_a_5343_);
                    v___x_5352_ = v___x_5339_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5353_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5353_, 1, v___x_5347_);
                    v___x_5352_ = v_reuseFailAlloc_5353_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5352_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5348_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5352_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_5350_,
                );
                v_r_5292_ = v___x_5352_;
                state = 3;
                continue;
            }
            15 => {
                if v_isShared_5357_ == 0 {
                    v___x_5359_ = v___x_5356_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5360_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
                    v___x_5359_ = v_reuseFailAlloc_5360_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5359_;
            }
            17 => {
                leanh::lean_inc_ref(v_e_x27_5366_);
                leanh::lean_inc_ref(v_e_x27_5363_);
                v___x_5372_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_5363_, v_e_x27_5366_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
                if leanh::lean_obj_tag(v___x_5372_) == 0 {
                    v_a_5373_ = leanh::lean_ctor_get(v___x_5372_, 0);
                    leanh::lean_inc(v_a_5373_);
                    leanh::lean_dec_ref_known(v___x_5372_, 1);
                    v___x_5374_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5;
                    v___x_5375_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_5262_, v_argUnivs_5263_, v___x_5374_, v_snd_5287_, v_i_5266_);
                    v_a_5376_ = leanh::lean_ctor_get(v___x_5375_, 0);
                    leanh::lean_inc(v_a_5376_);
                    leanh::lean_dec_ref(v___x_5375_);
                    v___x_5377_ = l_Lean_mkApp6(
                        v_a_5376_,
                        v_fn_5277_,
                        v_e_x27_5363_,
                        v_arg_5278_,
                        v_e_x27_5366_,
                        v_proof_5364_,
                        v_proof_5367_,
                    );
                    v___x_5378_ = 0;
                    if v_contextDependent_5365_ == 0 {
                        v___y_5380_ = v_contextDependent_5368_;
                        state = 18;
                        continue;
                    } else {
                        v___y_5380_ = v_contextDependent_5365_;
                        state = 18;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5370_);
                    leanh::lean_dec_ref(v_proof_5367_);
                    leanh::lean_dec_ref(v_e_x27_5366_);
                    leanh::lean_dec_ref(v_proof_5364_);
                    leanh::lean_dec_ref(v_e_x27_5363_);
                    leanh::lean_del_object(v___x_5289_);
                    leanh::lean_dec(v_snd_5287_);
                    leanh::lean_del_object(v___x_5284_);
                    leanh::lean_dec_ref(v_arg_5278_);
                    leanh::lean_dec_ref(v_fn_5277_);
                    v_a_5384_ = leanh::lean_ctor_get(v___x_5372_, 0);
                    v_isSharedCheck_5391_ = (!leanh::lean_is_exclusive(v___x_5372_)) as u8;
                    if v_isSharedCheck_5391_ == 0 {
                        v___x_5386_ = v___x_5372_;
                        v_isShared_5387_ = v_isSharedCheck_5391_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5384_);
                        leanh::lean_dec(v___x_5372_);
                        v___x_5386_ = leanh::lean_box(0);
                        v_isShared_5387_ = v_isSharedCheck_5391_;
                        state = 20;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_5371_ == 0 {
                    leanh::lean_ctor_set(v___x_5370_, 1, v___x_5377_);
                    leanh::lean_ctor_set(v___x_5370_, 0, v_a_5373_);
                    v___x_5382_ = v___x_5370_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5383_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5383_, 1, v___x_5377_);
                    v___x_5382_ = v_reuseFailAlloc_5383_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5382_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5378_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5382_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_5380_,
                );
                v_r_5292_ = v___x_5382_;
                state = 3;
                continue;
            }
            20 => {
                if v_isShared_5387_ == 0 {
                    v___x_5389_ = v___x_5386_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5390_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_a_5384_);
                    v___x_5389_ = v_reuseFailAlloc_5390_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5389_;
            }
            22 => {
                if v_isShared_5396_ == 0 {
                    v___x_5398_ = v___x_5395_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5399_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
                    v___x_5398_ = v_reuseFailAlloc_5399_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5398_;
            }
            24 => {
                v___x_5408_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5408_, 0, v_a_5404_);
                leanh::lean_ctor_set(v___x_5408_, 1, v_fType_5261_);
                if v_isShared_5407_ == 0 {
                    leanh::lean_ctor_set(v___x_5406_, 0, v___x_5408_);
                    v___x_5410_ = v___x_5406_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5411_, 0, v___x_5408_);
                    v___x_5410_ = v_reuseFailAlloc_5411_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_5410_;
            }
            26 => {
                if v_isShared_5416_ == 0 {
                    v___x_5418_ = v___x_5415_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
                    v___x_5418_ = v_reuseFailAlloc_5419_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_5418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(
    mut v_fType_5423_: *mut leanh::LeanObject,
    mut v_fnUnivs_5424_: *mut leanh::LeanObject,
    mut v_argUnivs_5425_: *mut leanh::LeanObject,
    mut v_simpBody_5426_: *mut leanh::LeanObject,
    mut v_e_5427_: *mut leanh::LeanObject,
    mut v_i_5428_: *mut leanh::LeanObject,
    mut v_a_5429_: *mut leanh::LeanObject,
    mut v_a_5430_: *mut leanh::LeanObject,
    mut v_a_5431_: *mut leanh::LeanObject,
    mut v_a_5432_: *mut leanh::LeanObject,
    mut v_a_5433_: *mut leanh::LeanObject,
    mut v_a_5434_: *mut leanh::LeanObject,
    mut v_a_5435_: *mut leanh::LeanObject,
    mut v_a_5436_: *mut leanh::LeanObject,
    mut v_a_5437_: *mut leanh::LeanObject,
    mut v_a_5438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5439_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(
        v_fType_5423_,
        v_fnUnivs_5424_,
        v_argUnivs_5425_,
        v_simpBody_5426_,
        v_e_5427_,
        v_i_5428_,
        v_a_5429_,
        v_a_5430_,
        v_a_5431_,
        v_a_5432_,
        v_a_5433_,
        v_a_5434_,
        v_a_5435_,
        v_a_5436_,
        v_a_5437_,
    );
    leanh::lean_dec(v_a_5437_);
    leanh::lean_dec_ref(v_a_5436_);
    leanh::lean_dec(v_a_5435_);
    leanh::lean_dec_ref(v_a_5434_);
    leanh::lean_dec(v_a_5433_);
    leanh::lean_dec_ref(v_a_5432_);
    leanh::lean_dec(v_a_5431_);
    leanh::lean_dec_ref(v_a_5430_);
    leanh::lean_dec(v_a_5429_);
    leanh::lean_dec(v_i_5428_);
    leanh::lean_dec_ref(v_argUnivs_5425_);
    leanh::lean_dec_ref(v_fnUnivs_5424_);
    return v_res_5439_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(
    mut v_e_5440_: *mut leanh::LeanObject,
    mut v_fType_5441_: *mut leanh::LeanObject,
    mut v_fnUnivs_5442_: *mut leanh::LeanObject,
    mut v_argUnivs_5443_: *mut leanh::LeanObject,
    mut v_simpBody_5444_: *mut leanh::LeanObject,
    mut v_a_5445_: *mut leanh::LeanObject,
    mut v_a_5446_: *mut leanh::LeanObject,
    mut v_a_5447_: *mut leanh::LeanObject,
    mut v_a_5448_: *mut leanh::LeanObject,
    mut v_a_5449_: *mut leanh::LeanObject,
    mut v_a_5450_: *mut leanh::LeanObject,
    mut v_a_5451_: *mut leanh::LeanObject,
    mut v_a_5452_: *mut leanh::LeanObject,
    mut v_a_5453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numArgs_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5462_: u8 = 0;
    let mut v_fst_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut v_a_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5471_: u8 = 0;
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numArgs_5455_ = lean_array_get_size(v_argUnivs_5443_);
                v___x_5456_ = leanh::lean_unsigned_to_nat(1);
                v___x_5457_ = lean_nat_sub(v_numArgs_5455_, v___x_5456_);
                v___x_5458_ =
                    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(
                        v_fType_5441_,
                        v_fnUnivs_5442_,
                        v_argUnivs_5443_,
                        v_simpBody_5444_,
                        v_e_5440_,
                        v___x_5457_,
                        v_a_5445_,
                        v_a_5446_,
                        v_a_5447_,
                        v_a_5448_,
                        v_a_5449_,
                        v_a_5450_,
                        v_a_5451_,
                        v_a_5452_,
                        v_a_5453_,
                    );
                leanh::lean_dec(v___x_5457_);
                if leanh::lean_obj_tag(v___x_5458_) == 0 {
                    v_a_5459_ = leanh::lean_ctor_get(v___x_5458_, 0);
                    v_isSharedCheck_5467_ = (!leanh::lean_is_exclusive(v___x_5458_)) as u8;
                    if v_isSharedCheck_5467_ == 0 {
                        v___x_5461_ = v___x_5458_;
                        v_isShared_5462_ = v_isSharedCheck_5467_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5459_);
                        leanh::lean_dec(v___x_5458_);
                        v___x_5461_ = leanh::lean_box(0);
                        v_isShared_5462_ = v_isSharedCheck_5467_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5468_ = leanh::lean_ctor_get(v___x_5458_, 0);
                    v_isSharedCheck_5475_ = (!leanh::lean_is_exclusive(v___x_5458_)) as u8;
                    if v_isSharedCheck_5475_ == 0 {
                        v___x_5470_ = v___x_5458_;
                        v_isShared_5471_ = v_isSharedCheck_5475_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5468_);
                        leanh::lean_dec(v___x_5458_);
                        v___x_5470_ = leanh::lean_box(0);
                        v_isShared_5471_ = v_isSharedCheck_5475_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5463_ = leanh::lean_ctor_get(v_a_5459_, 0);
                leanh::lean_inc(v_fst_5463_);
                leanh::lean_dec(v_a_5459_);
                if v_isShared_5462_ == 0 {
                    leanh::lean_ctor_set(v___x_5461_, 0, v_fst_5463_);
                    v___x_5465_ = v___x_5461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_fst_5463_);
                    v___x_5465_ = v_reuseFailAlloc_5466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5465_;
            }
            3 => {
                if v_isShared_5471_ == 0 {
                    v___x_5473_ = v___x_5470_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5474_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5468_);
                    v___x_5473_ = v_reuseFailAlloc_5474_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(
    mut v_e_5476_: *mut leanh::LeanObject,
    mut v_fType_5477_: *mut leanh::LeanObject,
    mut v_fnUnivs_5478_: *mut leanh::LeanObject,
    mut v_argUnivs_5479_: *mut leanh::LeanObject,
    mut v_simpBody_5480_: *mut leanh::LeanObject,
    mut v_a_5481_: *mut leanh::LeanObject,
    mut v_a_5482_: *mut leanh::LeanObject,
    mut v_a_5483_: *mut leanh::LeanObject,
    mut v_a_5484_: *mut leanh::LeanObject,
    mut v_a_5485_: *mut leanh::LeanObject,
    mut v_a_5486_: *mut leanh::LeanObject,
    mut v_a_5487_: *mut leanh::LeanObject,
    mut v_a_5488_: *mut leanh::LeanObject,
    mut v_a_5489_: *mut leanh::LeanObject,
    mut v_a_5490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5491_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(
        v_e_5476_,
        v_fType_5477_,
        v_fnUnivs_5478_,
        v_argUnivs_5479_,
        v_simpBody_5480_,
        v_a_5481_,
        v_a_5482_,
        v_a_5483_,
        v_a_5484_,
        v_a_5485_,
        v_a_5486_,
        v_a_5487_,
        v_a_5488_,
        v_a_5489_,
    );
    leanh::lean_dec(v_a_5489_);
    leanh::lean_dec_ref(v_a_5488_);
    leanh::lean_dec(v_a_5487_);
    leanh::lean_dec_ref(v_a_5486_);
    leanh::lean_dec(v_a_5485_);
    leanh::lean_dec_ref(v_a_5484_);
    leanh::lean_dec(v_a_5483_);
    leanh::lean_dec_ref(v_a_5482_);
    leanh::lean_dec(v_a_5481_);
    leanh::lean_dec_ref(v_argUnivs_5479_);
    leanh::lean_dec_ref(v_fnUnivs_5478_);
    return v_res_5491_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(
    mut v_e_5496_: *mut leanh::LeanObject,
    mut v_simpBody_5497_: *mut leanh::LeanObject,
    mut v_a_5498_: *mut leanh::LeanObject,
    mut v_a_5499_: *mut leanh::LeanObject,
    mut v_a_5500_: *mut leanh::LeanObject,
    mut v_a_5501_: *mut leanh::LeanObject,
    mut v_a_5502_: *mut leanh::LeanObject,
    mut v_a_5503_: *mut leanh::LeanObject,
    mut v_a_5504_: *mut leanh::LeanObject,
    mut v_a_5505_: *mut leanh::LeanObject,
    mut v_a_5506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b1_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varDeps_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fType_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_argUnivs_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnUnivs_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5522_: u8 = 0;
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5527_: u8 = 0;
    let mut v_contextDependent_5528_: u8 = 0;
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5536_: u8 = 0;
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5539_: u8 = 0;
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v___x_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: u8 = 0;
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5567_: u8 = 0;
    let mut v_a_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut v_reuseFailAlloc_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5577_: u8 = 0;
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_a_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5586_: u8 = 0;
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut v_a_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5591_: u8 = 0;
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5595_: u8 = 0;
    let mut v_a_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5599_: u8 = 0;
    let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_5496_);
                v___x_5508_ = l_Lean_Meta_Sym_Simp_toBetaApp(
                    v_e_5496_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_,
                );
                if leanh::lean_obj_tag(v___x_5508_) == 0 {
                    v_a_5509_ = leanh::lean_ctor_get(v___x_5508_, 0);
                    leanh::lean_inc(v_a_5509_);
                    leanh::lean_dec_ref_known(v___x_5508_, 1);
                    v_00_u03b1_5510_ = leanh::lean_ctor_get(v_a_5509_, 0);
                    leanh::lean_inc_ref(v_00_u03b1_5510_);
                    v_u_5511_ = leanh::lean_ctor_get(v_a_5509_, 1);
                    leanh::lean_inc(v_u_5511_);
                    v_e_5512_ = leanh::lean_ctor_get(v_a_5509_, 2);
                    leanh::lean_inc_ref(v_e_5512_);
                    v_h_5513_ = leanh::lean_ctor_get(v_a_5509_, 3);
                    leanh::lean_inc_ref(v_h_5513_);
                    v_varDeps_5514_ = leanh::lean_ctor_get(v_a_5509_, 4);
                    leanh::lean_inc_ref(v_varDeps_5514_);
                    v_fType_5515_ = leanh::lean_ctor_get(v_a_5509_, 5);
                    leanh::lean_inc_ref_n(v_fType_5515_, 2);
                    leanh::lean_dec(v_a_5509_);
                    v___x_5516_ =
                        l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(
                            v_fType_5515_,
                            v_a_5501_,
                            v_a_5502_,
                            v_a_5503_,
                            v_a_5504_,
                            v_a_5505_,
                            v_a_5506_,
                        );
                    if leanh::lean_obj_tag(v___x_5516_) == 0 {
                        v_a_5517_ = leanh::lean_ctor_get(v___x_5516_, 0);
                        leanh::lean_inc(v_a_5517_);
                        leanh::lean_dec_ref_known(v___x_5516_, 1);
                        v_argUnivs_5518_ = leanh::lean_ctor_get(v_a_5517_, 0);
                        v_fnUnivs_5519_ = leanh::lean_ctor_get(v_a_5517_, 1);
                        v_isSharedCheck_5587_ = (!leanh::lean_is_exclusive(v_a_5517_)) as u8;
                        if v_isSharedCheck_5587_ == 0 {
                            v___x_5521_ = v_a_5517_;
                            v_isShared_5522_ = v_isSharedCheck_5587_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_fnUnivs_5519_);
                            leanh::lean_inc(v_argUnivs_5518_);
                            leanh::lean_dec(v_a_5517_);
                            v___x_5521_ = leanh::lean_box(0);
                            v_isShared_5522_ = v_isSharedCheck_5587_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_fType_5515_);
                        leanh::lean_dec_ref(v_varDeps_5514_);
                        leanh::lean_dec_ref(v_h_5513_);
                        leanh::lean_dec_ref(v_e_5512_);
                        leanh::lean_dec(v_u_5511_);
                        leanh::lean_dec_ref(v_00_u03b1_5510_);
                        leanh::lean_dec_ref(v_simpBody_5497_);
                        leanh::lean_dec_ref(v_e_5496_);
                        v_a_5588_ = leanh::lean_ctor_get(v___x_5516_, 0);
                        v_isSharedCheck_5595_ =
                            (!leanh::lean_is_exclusive(v___x_5516_)) as u8;
                        if v_isSharedCheck_5595_ == 0 {
                            v___x_5590_ = v___x_5516_;
                            v_isShared_5591_ = v_isSharedCheck_5595_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5588_);
                            leanh::lean_dec(v___x_5516_);
                            v___x_5590_ = leanh::lean_box(0);
                            v_isShared_5591_ = v_isSharedCheck_5595_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_simpBody_5497_);
                    leanh::lean_dec_ref(v_e_5496_);
                    v_a_5596_ = leanh::lean_ctor_get(v___x_5508_, 0);
                    v_isSharedCheck_5603_ = (!leanh::lean_is_exclusive(v___x_5508_)) as u8;
                    if v_isSharedCheck_5603_ == 0 {
                        v___x_5598_ = v___x_5508_;
                        v_isShared_5599_ = v_isSharedCheck_5603_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5596_);
                        leanh::lean_dec(v___x_5508_);
                        v___x_5598_ = leanh::lean_box(0);
                        v_isShared_5599_ = v_isSharedCheck_5603_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_e_5512_);
                v___x_5523_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(
                    v_e_5512_,
                    v_fType_5515_,
                    v_fnUnivs_5519_,
                    v_argUnivs_5518_,
                    v_simpBody_5497_,
                    v_a_5498_,
                    v_a_5499_,
                    v_a_5500_,
                    v_a_5501_,
                    v_a_5502_,
                    v_a_5503_,
                    v_a_5504_,
                    v_a_5505_,
                    v_a_5506_,
                );
                leanh::lean_dec_ref(v_argUnivs_5518_);
                leanh::lean_dec_ref(v_fnUnivs_5519_);
                if leanh::lean_obj_tag(v___x_5523_) == 0 {
                    v_a_5524_ = leanh::lean_ctor_get(v___x_5523_, 0);
                    v_isSharedCheck_5578_ = (!leanh::lean_is_exclusive(v___x_5523_)) as u8;
                    if v_isSharedCheck_5578_ == 0 {
                        v___x_5526_ = v___x_5523_;
                        v_isShared_5527_ = v_isSharedCheck_5578_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5524_);
                        leanh::lean_dec(v___x_5523_);
                        v___x_5526_ = leanh::lean_box(0);
                        v_isShared_5527_ = v_isSharedCheck_5578_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5521_);
                    leanh::lean_dec_ref(v_varDeps_5514_);
                    leanh::lean_dec_ref(v_h_5513_);
                    leanh::lean_dec_ref(v_e_5512_);
                    leanh::lean_dec(v_u_5511_);
                    leanh::lean_dec_ref(v_00_u03b1_5510_);
                    leanh::lean_dec_ref(v_e_5496_);
                    v_a_5579_ = leanh::lean_ctor_get(v___x_5523_, 0);
                    v_isSharedCheck_5586_ = (!leanh::lean_is_exclusive(v___x_5523_)) as u8;
                    if v_isSharedCheck_5586_ == 0 {
                        v___x_5581_ = v___x_5523_;
                        v_isShared_5582_ = v_isSharedCheck_5586_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5579_);
                        leanh::lean_dec(v___x_5523_);
                        v___x_5581_ = leanh::lean_box(0);
                        v_isShared_5582_ = v_isSharedCheck_5586_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5524_) == 0 {
                    leanh::lean_del_object(v___x_5521_);
                    leanh::lean_dec_ref(v_varDeps_5514_);
                    leanh::lean_dec_ref(v_h_5513_);
                    leanh::lean_dec_ref(v_e_5512_);
                    leanh::lean_dec_ref(v_e_5496_);
                    v_contextDependent_5528_ =
                        leanh::lean_ctor_get_uint8(v_a_5524_, 1 as u32);
                    leanh::lean_dec_ref_known(v_a_5524_, 0);
                    v___x_5529_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_5528_);
                    v___x_5530_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5530_, 0, v___x_5529_);
                    leanh::lean_ctor_set(v___x_5530_, 1, v_00_u03b1_5510_);
                    leanh::lean_ctor_set(v___x_5530_, 2, v_u_5511_);
                    if v_isShared_5527_ == 0 {
                        leanh::lean_ctor_set(v___x_5526_, 0, v___x_5530_);
                        v___x_5532_ = v___x_5526_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5533_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5530_);
                        v___x_5532_ = v_reuseFailAlloc_5533_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5526_);
                    v_e_x27_5534_ = leanh::lean_ctor_get(v_a_5524_, 0);
                    v_proof_5535_ = leanh::lean_ctor_get(v_a_5524_, 1);
                    v_contextDependent_5536_ = leanh::lean_ctor_get_uint8(
                        v_a_5524_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_5577_ = (!leanh::lean_is_exclusive(v_a_5524_)) as u8;
                    if v_isSharedCheck_5577_ == 0 {
                        v___x_5538_ = v_a_5524_;
                        v_isShared_5539_ = v_isSharedCheck_5577_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_proof_5535_);
                        leanh::lean_inc(v_e_x27_5534_);
                        leanh::lean_dec(v_a_5524_);
                        v___x_5538_ = leanh::lean_box(0);
                        v_isShared_5539_ = v_isSharedCheck_5577_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5532_;
            }
            4 => {
                v___x_5540_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1;
                v___x_5541_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_5511_);
                if v_isShared_5522_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5521_, 1);
                    leanh::lean_ctor_set(v___x_5521_, 1, v___x_5541_);
                    leanh::lean_ctor_set(v___x_5521_, 0, v_u_5511_);
                    v___x_5543_ = v___x_5521_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5576_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_u_5511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5576_, 1, v___x_5541_);
                    v___x_5543_ = v_reuseFailAlloc_5576_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___x_5543_);
                v___x_5544_ = l_Lean_mkConst(v___x_5540_, v___x_5543_);
                leanh::lean_inc_ref_n(v_e_x27_5534_, 2);
                leanh::lean_inc_ref(v_e_5496_);
                leanh::lean_inc_ref(v_00_u03b1_5510_);
                leanh::lean_inc_ref(v___x_5544_);
                v___x_5545_ = l_Lean_mkApp6(
                    v___x_5544_,
                    v_00_u03b1_5510_,
                    v_e_5496_,
                    v_e_5512_,
                    v_e_x27_5534_,
                    v_h_5513_,
                    v_proof_5535_,
                );
                v___x_5546_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(
                    v_e_x27_5534_,
                    v_varDeps_5514_,
                    v_a_5501_,
                    v_a_5502_,
                    v_a_5503_,
                    v_a_5504_,
                    v_a_5505_,
                    v_a_5506_,
                );
                if leanh::lean_obj_tag(v___x_5546_) == 0 {
                    v_a_5547_ = leanh::lean_ctor_get(v___x_5546_, 0);
                    v_isSharedCheck_5567_ = (!leanh::lean_is_exclusive(v___x_5546_)) as u8;
                    if v_isSharedCheck_5567_ == 0 {
                        v___x_5549_ = v___x_5546_;
                        v_isShared_5550_ = v_isSharedCheck_5567_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5547_);
                        leanh::lean_dec(v___x_5546_);
                        v___x_5549_ = leanh::lean_box(0);
                        v_isShared_5550_ = v_isSharedCheck_5567_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5545_);
                    leanh::lean_dec_ref(v___x_5544_);
                    leanh::lean_dec_ref(v___x_5543_);
                    leanh::lean_del_object(v___x_5538_);
                    leanh::lean_dec_ref(v_e_x27_5534_);
                    leanh::lean_dec(v_u_5511_);
                    leanh::lean_dec_ref(v_00_u03b1_5510_);
                    leanh::lean_dec_ref(v_e_5496_);
                    v_a_5568_ = leanh::lean_ctor_get(v___x_5546_, 0);
                    v_isSharedCheck_5575_ = (!leanh::lean_is_exclusive(v___x_5546_)) as u8;
                    if v_isSharedCheck_5575_ == 0 {
                        v___x_5570_ = v___x_5546_;
                        v_isShared_5571_ = v_isSharedCheck_5575_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5568_);
                        leanh::lean_dec(v___x_5546_);
                        v___x_5570_ = leanh::lean_box(0);
                        v_isShared_5571_ = v_isSharedCheck_5575_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5551_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1;
                leanh::lean_inc_ref(v___x_5543_);
                v___x_5552_ = l_Lean_mkConst(v___x_5551_, v___x_5543_);
                leanh::lean_inc_n(v_a_5547_, 2);
                leanh::lean_inc_ref_n(v_e_x27_5534_, 2);
                leanh::lean_inc_ref_n(v_00_u03b1_5510_, 3);
                v___x_5553_ =
                    l_Lean_mkApp3(v___x_5552_, v_00_u03b1_5510_, v_e_x27_5534_, v_a_5547_);
                v___x_5554_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3;
                v___x_5555_ = l_Lean_mkConst(v___x_5554_, v___x_5543_);
                v___x_5556_ = l_Lean_mkAppB(v___x_5555_, v_00_u03b1_5510_, v_e_x27_5534_);
                v___x_5557_ = l_Lean_Meta_mkExpectedPropHint(v___x_5556_, v___x_5553_);
                v___x_5558_ = l_Lean_mkApp6(
                    v___x_5544_,
                    v_00_u03b1_5510_,
                    v_e_5496_,
                    v_e_x27_5534_,
                    v_a_5547_,
                    v___x_5545_,
                    v___x_5557_,
                );
                v___x_5559_ = 0;
                if v_isShared_5539_ == 0 {
                    leanh::lean_ctor_set(v___x_5538_, 1, v___x_5558_);
                    leanh::lean_ctor_set(v___x_5538_, 0, v_a_5547_);
                    v___x_5561_ = v___x_5538_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5566_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_a_5547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5566_, 1, v___x_5558_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5566_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_5536_,
                    );
                    v___x_5561_ = v_reuseFailAlloc_5566_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5561_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5559_,
                );
                v___x_5562_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5562_, 0, v___x_5561_);
                leanh::lean_ctor_set(v___x_5562_, 1, v_00_u03b1_5510_);
                leanh::lean_ctor_set(v___x_5562_, 2, v_u_5511_);
                if v_isShared_5550_ == 0 {
                    leanh::lean_ctor_set(v___x_5549_, 0, v___x_5562_);
                    v___x_5564_ = v___x_5549_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5565_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5562_);
                    v___x_5564_ = v_reuseFailAlloc_5565_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5564_;
            }
            9 => {
                if v_isShared_5571_ == 0 {
                    v___x_5573_ = v___x_5570_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5574_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
                    v___x_5573_ = v_reuseFailAlloc_5574_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5573_;
            }
            11 => {
                if v_isShared_5582_ == 0 {
                    v___x_5584_ = v___x_5581_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5579_);
                    v___x_5584_ = v_reuseFailAlloc_5585_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5584_;
            }
            13 => {
                if v_isShared_5591_ == 0 {
                    v___x_5593_ = v___x_5590_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5594_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5588_);
                    v___x_5593_ = v_reuseFailAlloc_5594_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5593_;
            }
            15 => {
                if v_isShared_5599_ == 0 {
                    v___x_5601_ = v___x_5598_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5602_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5596_);
                    v___x_5601_ = v_reuseFailAlloc_5602_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(
    mut v_e_5604_: *mut leanh::LeanObject,
    mut v_simpBody_5605_: *mut leanh::LeanObject,
    mut v_a_5606_: *mut leanh::LeanObject,
    mut v_a_5607_: *mut leanh::LeanObject,
    mut v_a_5608_: *mut leanh::LeanObject,
    mut v_a_5609_: *mut leanh::LeanObject,
    mut v_a_5610_: *mut leanh::LeanObject,
    mut v_a_5611_: *mut leanh::LeanObject,
    mut v_a_5612_: *mut leanh::LeanObject,
    mut v_a_5613_: *mut leanh::LeanObject,
    mut v_a_5614_: *mut leanh::LeanObject,
    mut v_a_5615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5616_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(
        v_e_5604_,
        v_simpBody_5605_,
        v_a_5606_,
        v_a_5607_,
        v_a_5608_,
        v_a_5609_,
        v_a_5610_,
        v_a_5611_,
        v_a_5612_,
        v_a_5613_,
        v_a_5614_,
    );
    leanh::lean_dec(v_a_5614_);
    leanh::lean_dec_ref(v_a_5613_);
    leanh::lean_dec(v_a_5612_);
    leanh::lean_dec_ref(v_a_5611_);
    leanh::lean_dec(v_a_5610_);
    leanh::lean_dec_ref(v_a_5609_);
    leanh::lean_dec(v_a_5608_);
    leanh::lean_dec_ref(v_a_5607_);
    leanh::lean_dec(v_a_5606_);
    return v_res_5616_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpHave(
    mut v_e_5617_: *mut leanh::LeanObject,
    mut v_simpBody_5618_: *mut leanh::LeanObject,
    mut v_a_5619_: *mut leanh::LeanObject,
    mut v_a_5620_: *mut leanh::LeanObject,
    mut v_a_5621_: *mut leanh::LeanObject,
    mut v_a_5622_: *mut leanh::LeanObject,
    mut v_a_5623_: *mut leanh::LeanObject,
    mut v_a_5624_: *mut leanh::LeanObject,
    mut v_a_5625_: *mut leanh::LeanObject,
    mut v_a_5626_: *mut leanh::LeanObject,
    mut v_a_5627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5633_: u8 = 0;
    let mut v_result_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5638_: u8 = 0;
    let mut v_a_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5629_ =
                    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(
                        v_e_5617_,
                        v_simpBody_5618_,
                        v_a_5619_,
                        v_a_5620_,
                        v_a_5621_,
                        v_a_5622_,
                        v_a_5623_,
                        v_a_5624_,
                        v_a_5625_,
                        v_a_5626_,
                        v_a_5627_,
                    );
                if leanh::lean_obj_tag(v___x_5629_) == 0 {
                    v_a_5630_ = leanh::lean_ctor_get(v___x_5629_, 0);
                    v_isSharedCheck_5638_ = (!leanh::lean_is_exclusive(v___x_5629_)) as u8;
                    if v_isSharedCheck_5638_ == 0 {
                        v___x_5632_ = v___x_5629_;
                        v_isShared_5633_ = v_isSharedCheck_5638_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5630_);
                        leanh::lean_dec(v___x_5629_);
                        v___x_5632_ = leanh::lean_box(0);
                        v_isShared_5633_ = v_isSharedCheck_5638_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5639_ = leanh::lean_ctor_get(v___x_5629_, 0);
                    v_isSharedCheck_5646_ = (!leanh::lean_is_exclusive(v___x_5629_)) as u8;
                    if v_isSharedCheck_5646_ == 0 {
                        v___x_5641_ = v___x_5629_;
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5639_);
                        leanh::lean_dec(v___x_5629_);
                        v___x_5641_ = leanh::lean_box(0);
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_result_5634_ = leanh::lean_ctor_get(v_a_5630_, 0);
                leanh::lean_inc_ref(v_result_5634_);
                leanh::lean_dec(v_a_5630_);
                if v_isShared_5633_ == 0 {
                    leanh::lean_ctor_set(v___x_5632_, 0, v_result_5634_);
                    v___x_5636_ = v___x_5632_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5637_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_result_5634_);
                    v___x_5636_ = v_reuseFailAlloc_5637_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5636_;
            }
            3 => {
                if v_isShared_5642_ == 0 {
                    v___x_5644_ = v___x_5641_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
                    v___x_5644_ = v_reuseFailAlloc_5645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpHave___boxed(
    mut v_e_5647_: *mut leanh::LeanObject,
    mut v_simpBody_5648_: *mut leanh::LeanObject,
    mut v_a_5649_: *mut leanh::LeanObject,
    mut v_a_5650_: *mut leanh::LeanObject,
    mut v_a_5651_: *mut leanh::LeanObject,
    mut v_a_5652_: *mut leanh::LeanObject,
    mut v_a_5653_: *mut leanh::LeanObject,
    mut v_a_5654_: *mut leanh::LeanObject,
    mut v_a_5655_: *mut leanh::LeanObject,
    mut v_a_5656_: *mut leanh::LeanObject,
    mut v_a_5657_: *mut leanh::LeanObject,
    mut v_a_5658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5659_ = l_Lean_Meta_Sym_Simp_simpHave(
        v_e_5647_,
        v_simpBody_5648_,
        v_a_5649_,
        v_a_5650_,
        v_a_5651_,
        v_a_5652_,
        v_a_5653_,
        v_a_5654_,
        v_a_5655_,
        v_a_5656_,
        v_a_5657_,
    );
    leanh::lean_dec(v_a_5657_);
    leanh::lean_dec_ref(v_a_5656_);
    leanh::lean_dec(v_a_5655_);
    leanh::lean_dec_ref(v_a_5654_);
    leanh::lean_dec(v_a_5653_);
    leanh::lean_dec_ref(v_a_5652_);
    leanh::lean_dec(v_a_5651_);
    leanh::lean_dec_ref(v_a_5650_);
    leanh::lean_dec(v_a_5649_);
    return v_res_5659_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(
    mut v_e_u2081_5660_: *mut leanh::LeanObject,
    mut v_simpBody_5661_: *mut leanh::LeanObject,
    mut v_a_5662_: *mut leanh::LeanObject,
    mut v_a_5663_: *mut leanh::LeanObject,
    mut v_a_5664_: *mut leanh::LeanObject,
    mut v_a_5665_: *mut leanh::LeanObject,
    mut v_a_5666_: *mut leanh::LeanObject,
    mut v_a_5667_: *mut leanh::LeanObject,
    mut v_a_5668_: *mut leanh::LeanObject,
    mut v_a_5669_: *mut leanh::LeanObject,
    mut v_a_5670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b1_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5677_: u8 = 0;
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5682_: u8 = 0;
    let mut v___x_5683_: u8 = 0;
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5697_: u8 = 0;
    let mut v_a_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5701_: u8 = 0;
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5705_: u8 = 0;
    let mut v_00_u03b1_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5710_: u8 = 0;
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5715_: u8 = 0;
    let mut v___x_5716_: u8 = 0;
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5719_: u8 = 0;
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5734_: u8 = 0;
    let mut v_unused_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5740_: u8 = 0;
    let mut v_a_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5744_: u8 = 0;
    let mut v___x_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5748_: u8 = 0;
    let mut v_a_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5752_: u8 = 0;
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_u2081_5660_);
                v___x_5672_ =
                    l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(
                        v_e_u2081_5660_,
                        v_simpBody_5661_,
                        v_a_5662_,
                        v_a_5663_,
                        v_a_5664_,
                        v_a_5665_,
                        v_a_5666_,
                        v_a_5667_,
                        v_a_5668_,
                        v_a_5669_,
                        v_a_5670_,
                    );
                if leanh::lean_obj_tag(v___x_5672_) == 0 {
                    v_a_5673_ = leanh::lean_ctor_get(v___x_5672_, 0);
                    leanh::lean_inc(v_a_5673_);
                    leanh::lean_dec_ref_known(v___x_5672_, 1);
                    v_result_5674_ = leanh::lean_ctor_get(v_a_5673_, 0);
                    leanh::lean_inc_ref(v_result_5674_);
                    if leanh::lean_obj_tag(v_result_5674_) == 0 {
                        v_00_u03b1_5675_ = leanh::lean_ctor_get(v_a_5673_, 1);
                        leanh::lean_inc_ref(v_00_u03b1_5675_);
                        v_u_5676_ = leanh::lean_ctor_get(v_a_5673_, 2);
                        leanh::lean_inc(v_u_5676_);
                        leanh::lean_dec(v_a_5673_);
                        v_contextDependent_5677_ =
                            leanh::lean_ctor_get_uint8(v_result_5674_, 1 as u32);
                        leanh::lean_dec_ref_known(v_result_5674_, 0);
                        leanh::lean_inc_ref(v_e_u2081_5660_);
                        v___x_5678_ = l_Lean_Meta_zetaUnused(
                            v_e_u2081_5660_,
                            v_a_5667_,
                            v_a_5668_,
                            v_a_5669_,
                            v_a_5670_,
                        );
                        if leanh::lean_obj_tag(v___x_5678_) == 0 {
                            v_a_5679_ = leanh::lean_ctor_get(v___x_5678_, 0);
                            v_isSharedCheck_5697_ =
                                (!leanh::lean_is_exclusive(v___x_5678_)) as u8;
                            if v_isSharedCheck_5697_ == 0 {
                                v___x_5681_ = v___x_5678_;
                                v_isShared_5682_ = v_isSharedCheck_5697_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5679_);
                                leanh::lean_dec(v___x_5678_);
                                v___x_5681_ = leanh::lean_box(0);
                                v_isShared_5682_ = v_isSharedCheck_5697_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_u_5676_);
                            leanh::lean_dec_ref(v_00_u03b1_5675_);
                            leanh::lean_dec_ref(v_e_u2081_5660_);
                            v_a_5698_ = leanh::lean_ctor_get(v___x_5678_, 0);
                            v_isSharedCheck_5705_ =
                                (!leanh::lean_is_exclusive(v___x_5678_)) as u8;
                            if v_isSharedCheck_5705_ == 0 {
                                v___x_5700_ = v___x_5678_;
                                v_isShared_5701_ = v_isSharedCheck_5705_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5698_);
                                leanh::lean_dec(v___x_5678_);
                                v___x_5700_ = leanh::lean_box(0);
                                v_isShared_5701_ = v_isSharedCheck_5705_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_00_u03b1_5706_ = leanh::lean_ctor_get(v_a_5673_, 1);
                        leanh::lean_inc_ref(v_00_u03b1_5706_);
                        v_u_5707_ = leanh::lean_ctor_get(v_a_5673_, 2);
                        leanh::lean_inc(v_u_5707_);
                        leanh::lean_dec(v_a_5673_);
                        v_e_x27_5708_ = leanh::lean_ctor_get(v_result_5674_, 0);
                        v_proof_5709_ = leanh::lean_ctor_get(v_result_5674_, 1);
                        v_contextDependent_5710_ = leanh::lean_ctor_get_uint8(
                            v_result_5674_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        leanh::lean_inc_ref(v_e_x27_5708_);
                        v___x_5711_ = l_Lean_Meta_zetaUnused(
                            v_e_x27_5708_,
                            v_a_5667_,
                            v_a_5668_,
                            v_a_5669_,
                            v_a_5670_,
                        );
                        if leanh::lean_obj_tag(v___x_5711_) == 0 {
                            v_a_5712_ = leanh::lean_ctor_get(v___x_5711_, 0);
                            v_isSharedCheck_5740_ =
                                (!leanh::lean_is_exclusive(v___x_5711_)) as u8;
                            if v_isSharedCheck_5740_ == 0 {
                                v___x_5714_ = v___x_5711_;
                                v_isShared_5715_ = v_isSharedCheck_5740_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5712_);
                                leanh::lean_dec(v___x_5711_);
                                v___x_5714_ = leanh::lean_box(0);
                                v_isShared_5715_ = v_isSharedCheck_5740_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_u_5707_);
                            leanh::lean_dec_ref_known(v_result_5674_, 2);
                            leanh::lean_dec_ref(v_00_u03b1_5706_);
                            leanh::lean_dec_ref(v_e_u2081_5660_);
                            v_a_5741_ = leanh::lean_ctor_get(v___x_5711_, 0);
                            v_isSharedCheck_5748_ =
                                (!leanh::lean_is_exclusive(v___x_5711_)) as u8;
                            if v_isSharedCheck_5748_ == 0 {
                                v___x_5743_ = v___x_5711_;
                                v_isShared_5744_ = v_isSharedCheck_5748_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5741_);
                                leanh::lean_dec(v___x_5711_);
                                v___x_5743_ = leanh::lean_box(0);
                                v_isShared_5744_ = v_isSharedCheck_5748_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_u2081_5660_);
                    v_a_5749_ = leanh::lean_ctor_get(v___x_5672_, 0);
                    v_isSharedCheck_5756_ = (!leanh::lean_is_exclusive(v___x_5672_)) as u8;
                    if v_isSharedCheck_5756_ == 0 {
                        v___x_5751_ = v___x_5672_;
                        v_isShared_5752_ = v_isSharedCheck_5756_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5749_);
                        leanh::lean_dec(v___x_5672_);
                        v___x_5751_ = leanh::lean_box(0);
                        v_isShared_5752_ = v_isSharedCheck_5756_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5683_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_e_u2081_5660_,
                        v_a_5679_,
                    );
                leanh::lean_dec_ref(v_e_u2081_5660_);
                if v___x_5683_ == 0 {
                    v___x_5684_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3;
                    v___x_5685_ = leanh::lean_box(0);
                    v___x_5686_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5686_, 0, v_u_5676_);
                    leanh::lean_ctor_set(v___x_5686_, 1, v___x_5685_);
                    v___x_5687_ = l_Lean_mkConst(v___x_5684_, v___x_5686_);
                    leanh::lean_inc(v_a_5679_);
                    v___x_5688_ = l_Lean_mkAppB(v___x_5687_, v_00_u03b1_5675_, v_a_5679_);
                    v___x_5689_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v___x_5689_, 0, v_a_5679_);
                    leanh::lean_ctor_set(v___x_5689_, 1, v___x_5688_);
                    leanh::lean_ctor_set_uint8(
                        v___x_5689_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_5683_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_5689_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_5677_,
                    );
                    if v_isShared_5682_ == 0 {
                        leanh::lean_ctor_set(v___x_5681_, 0, v___x_5689_);
                        v___x_5691_ = v___x_5681_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5692_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5692_, 0, v___x_5689_);
                        v___x_5691_ = v_reuseFailAlloc_5692_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5679_);
                    leanh::lean_dec(v_u_5676_);
                    leanh::lean_dec_ref(v_00_u03b1_5675_);
                    v___x_5693_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_5677_);
                    if v_isShared_5682_ == 0 {
                        leanh::lean_ctor_set(v___x_5681_, 0, v___x_5693_);
                        v___x_5695_ = v___x_5681_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5696_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5696_, 0, v___x_5693_);
                        v___x_5695_ = v_reuseFailAlloc_5696_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5691_;
            }
            3 => {
                return v___x_5695_;
            }
            4 => {
                if v_isShared_5701_ == 0 {
                    v___x_5703_ = v___x_5700_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5698_);
                    v___x_5703_ = v_reuseFailAlloc_5704_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5703_;
            }
            6 => {
                v___x_5716_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_e_x27_5708_,
                        v_a_5712_,
                    );
                if v___x_5716_ == 0 {
                    leanh::lean_inc_ref(v_proof_5709_);
                    leanh::lean_inc_ref(v_e_x27_5708_);
                    v_isSharedCheck_5734_ =
                        (!leanh::lean_is_exclusive(v_result_5674_)) as u8;
                    if v_isSharedCheck_5734_ == 0 {
                        v_unused_5735_ = leanh::lean_ctor_get(v_result_5674_, 1);
                        leanh::lean_dec(v_unused_5735_);
                        v_unused_5736_ = leanh::lean_ctor_get(v_result_5674_, 0);
                        leanh::lean_dec(v_unused_5736_);
                        v___x_5718_ = v_result_5674_;
                        v_isShared_5719_ = v_isSharedCheck_5734_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v_result_5674_);
                        v___x_5718_ = leanh::lean_box(0);
                        v_isShared_5719_ = v_isSharedCheck_5734_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5712_);
                    leanh::lean_dec(v_u_5707_);
                    leanh::lean_dec_ref(v_00_u03b1_5706_);
                    leanh::lean_dec_ref(v_e_u2081_5660_);
                    if v_isShared_5715_ == 0 {
                        leanh::lean_ctor_set(v___x_5714_, 0, v_result_5674_);
                        v___x_5738_ = v___x_5714_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5739_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_result_5674_);
                        v___x_5738_ = v_reuseFailAlloc_5739_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v___x_5720_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1;
                v___x_5721_ = leanh::lean_box(0);
                v___x_5722_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5722_, 0, v_u_5707_);
                leanh::lean_ctor_set(v___x_5722_, 1, v___x_5721_);
                leanh::lean_inc_ref(v___x_5722_);
                v___x_5723_ = l_Lean_mkConst(v___x_5720_, v___x_5722_);
                v___x_5724_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3;
                v___x_5725_ = l_Lean_mkConst(v___x_5724_, v___x_5722_);
                leanh::lean_inc_n(v_a_5712_, 2);
                leanh::lean_inc_ref(v_00_u03b1_5706_);
                v___x_5726_ = l_Lean_mkAppB(v___x_5725_, v_00_u03b1_5706_, v_a_5712_);
                v___x_5727_ = l_Lean_mkApp6(
                    v___x_5723_,
                    v_00_u03b1_5706_,
                    v_e_u2081_5660_,
                    v_e_x27_5708_,
                    v_a_5712_,
                    v_proof_5709_,
                    v___x_5726_,
                );
                if v_isShared_5719_ == 0 {
                    leanh::lean_ctor_set(v___x_5718_, 1, v___x_5727_);
                    leanh::lean_ctor_set(v___x_5718_, 0, v_a_5712_);
                    v___x_5729_ = v___x_5718_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5733_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5733_, 0, v_a_5712_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5733_, 1, v___x_5727_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5733_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_5710_,
                    );
                    v___x_5729_ = v_reuseFailAlloc_5733_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5729_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5716_,
                );
                if v_isShared_5715_ == 0 {
                    leanh::lean_ctor_set(v___x_5714_, 0, v___x_5729_);
                    v___x_5731_ = v___x_5714_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5732_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 0, v___x_5729_);
                    v___x_5731_ = v_reuseFailAlloc_5732_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5731_;
            }
            10 => {
                return v___x_5738_;
            }
            11 => {
                if v_isShared_5744_ == 0 {
                    v___x_5746_ = v___x_5743_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5747_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5747_, 0, v_a_5741_);
                    v___x_5746_ = v_reuseFailAlloc_5747_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5746_;
            }
            13 => {
                if v_isShared_5752_ == 0 {
                    v___x_5754_ = v___x_5751_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5755_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_a_5749_);
                    v___x_5754_ = v_reuseFailAlloc_5755_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(
    mut v_e_u2081_5757_: *mut leanh::LeanObject,
    mut v_simpBody_5758_: *mut leanh::LeanObject,
    mut v_a_5759_: *mut leanh::LeanObject,
    mut v_a_5760_: *mut leanh::LeanObject,
    mut v_a_5761_: *mut leanh::LeanObject,
    mut v_a_5762_: *mut leanh::LeanObject,
    mut v_a_5763_: *mut leanh::LeanObject,
    mut v_a_5764_: *mut leanh::LeanObject,
    mut v_a_5765_: *mut leanh::LeanObject,
    mut v_a_5766_: *mut leanh::LeanObject,
    mut v_a_5767_: *mut leanh::LeanObject,
    mut v_a_5768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5769_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(
        v_e_u2081_5757_,
        v_simpBody_5758_,
        v_a_5759_,
        v_a_5760_,
        v_a_5761_,
        v_a_5762_,
        v_a_5763_,
        v_a_5764_,
        v_a_5765_,
        v_a_5766_,
        v_a_5767_,
    );
    leanh::lean_dec(v_a_5767_);
    leanh::lean_dec_ref(v_a_5766_);
    leanh::lean_dec(v_a_5765_);
    leanh::lean_dec_ref(v_a_5764_);
    leanh::lean_dec(v_a_5763_);
    leanh::lean_dec_ref(v_a_5762_);
    leanh::lean_dec(v_a_5761_);
    leanh::lean_dec_ref(v_a_5760_);
    leanh::lean_dec(v_a_5759_);
    return v_res_5769_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLet_x27(
    mut v_simpBody_5770_: *mut leanh::LeanObject,
    mut v_e_5771_: *mut leanh::LeanObject,
    mut v_a_5772_: *mut leanh::LeanObject,
    mut v_a_5773_: *mut leanh::LeanObject,
    mut v_a_5774_: *mut leanh::LeanObject,
    mut v_a_5775_: *mut leanh::LeanObject,
    mut v_a_5776_: *mut leanh::LeanObject,
    mut v_a_5777_: *mut leanh::LeanObject,
    mut v_a_5778_: *mut leanh::LeanObject,
    mut v_a_5779_: *mut leanh::LeanObject,
    mut v_a_5780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5782_: u8 = 0;
    v___x_5782_ = l_Lean_Expr_letNondep_x21(v_e_5771_);
    if v___x_5782_ == 0 {
        let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_5771_);
        leanh::lean_dec_ref(v_simpBody_5770_);
        v___x_5783_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
        leanh::lean_ctor_set_uint8(v___x_5783_, 0 as u32, v___x_5782_);
        leanh::lean_ctor_set_uint8(v___x_5783_, 1 as u32, v___x_5782_);
        v___x_5784_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5784_, 0, v___x_5783_);
        return v___x_5784_;
    } else {
        let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5785_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(
            v_e_5771_,
            v_simpBody_5770_,
            v_a_5772_,
            v_a_5773_,
            v_a_5774_,
            v_a_5775_,
            v_a_5776_,
            v_a_5777_,
            v_a_5778_,
            v_a_5779_,
            v_a_5780_,
        );
        return v___x_5785_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(
    mut v_simpBody_5786_: *mut leanh::LeanObject,
    mut v_e_5787_: *mut leanh::LeanObject,
    mut v_a_5788_: *mut leanh::LeanObject,
    mut v_a_5789_: *mut leanh::LeanObject,
    mut v_a_5790_: *mut leanh::LeanObject,
    mut v_a_5791_: *mut leanh::LeanObject,
    mut v_a_5792_: *mut leanh::LeanObject,
    mut v_a_5793_: *mut leanh::LeanObject,
    mut v_a_5794_: *mut leanh::LeanObject,
    mut v_a_5795_: *mut leanh::LeanObject,
    mut v_a_5796_: *mut leanh::LeanObject,
    mut v_a_5797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5798_ = l_Lean_Meta_Sym_Simp_simpLet_x27(
        v_simpBody_5786_,
        v_e_5787_,
        v_a_5788_,
        v_a_5789_,
        v_a_5790_,
        v_a_5791_,
        v_a_5792_,
        v_a_5793_,
        v_a_5794_,
        v_a_5795_,
        v_a_5796_,
    );
    leanh::lean_dec(v_a_5796_);
    leanh::lean_dec_ref(v_a_5795_);
    leanh::lean_dec(v_a_5794_);
    leanh::lean_dec_ref(v_a_5793_);
    leanh::lean_dec(v_a_5792_);
    leanh::lean_dec_ref(v_a_5791_);
    leanh::lean_dec(v_a_5790_);
    leanh::lean_dec_ref(v_a_5789_);
    leanh::lean_dec(v_a_5788_);
    return v_res_5798_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLet(
    mut v_e_5800_: *mut leanh::LeanObject,
    mut v_a_5801_: *mut leanh::LeanObject,
    mut v_a_5802_: *mut leanh::LeanObject,
    mut v_a_5803_: *mut leanh::LeanObject,
    mut v_a_5804_: *mut leanh::LeanObject,
    mut v_a_5805_: *mut leanh::LeanObject,
    mut v_a_5806_: *mut leanh::LeanObject,
    mut v_a_5807_: *mut leanh::LeanObject,
    mut v_a_5808_: *mut leanh::LeanObject,
    mut v_a_5809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5811_ = l_Lean_Meta_Sym_Simp_simpLet___closed__0;
    v___x_5812_ = l_Lean_Meta_Sym_Simp_simpLet_x27(
        v___x_5811_,
        v_e_5800_,
        v_a_5801_,
        v_a_5802_,
        v_a_5803_,
        v_a_5804_,
        v_a_5805_,
        v_a_5806_,
        v_a_5807_,
        v_a_5808_,
        v_a_5809_,
    );
    return v___x_5812_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLet___boxed(
    mut v_e_5813_: *mut leanh::LeanObject,
    mut v_a_5814_: *mut leanh::LeanObject,
    mut v_a_5815_: *mut leanh::LeanObject,
    mut v_a_5816_: *mut leanh::LeanObject,
    mut v_a_5817_: *mut leanh::LeanObject,
    mut v_a_5818_: *mut leanh::LeanObject,
    mut v_a_5819_: *mut leanh::LeanObject,
    mut v_a_5820_: *mut leanh::LeanObject,
    mut v_a_5821_: *mut leanh::LeanObject,
    mut v_a_5822_: *mut leanh::LeanObject,
    mut v_a_5823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5824_ = l_Lean_Meta_Sym_Simp_simpLet(
        v_e_5813_, v_a_5814_, v_a_5815_, v_a_5816_, v_a_5817_, v_a_5818_, v_a_5819_, v_a_5820_,
        v_a_5821_, v_a_5822_,
    );
    leanh::lean_dec(v_a_5822_);
    leanh::lean_dec_ref(v_a_5821_);
    leanh::lean_dec(v_a_5820_);
    leanh::lean_dec_ref(v_a_5819_);
    leanh::lean_dec(v_a_5818_);
    leanh::lean_dec_ref(v_a_5817_);
    leanh::lean_dec(v_a_5816_);
    leanh::lean_dec_ref(v_a_5815_);
    leanh::lean_dec(v_a_5814_);
    return v_res_5824_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Have(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HaveTelescope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default =
        _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default);
    l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult =
        _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Have(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Have(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AbstractS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_HaveTelescope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Have(builtin);
}