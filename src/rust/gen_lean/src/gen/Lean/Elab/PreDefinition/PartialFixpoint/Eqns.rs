// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Eqns
// Imports: Lean.Elab.PreDefinition.FixedParams Init.Internal.Order.Basic Lean.Meta.Tactic.Delta Lean.Meta.Tactic.Refl
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_infer_type,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_ptr_addr, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Internal::Order::Basic::{
    initialize_Init_Internal_Order_Basic, runtime_initialize_Init_Internal_Order_Basic,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isRuntime, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_hasValue;
use crate::r#gen::Lean::Elab::DefView::l_Lean_Elab_DefKind_isTheorem;
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::{
    initialize_Lean_Elab_PreDefinition_FixedParams,
    l_Lean_Elab_instInhabitedFixedParamPerms_default,
    runtime_initialize_Lean_Elab_PreDefinition_FixedParams,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_hasUnsafe,
    l_Lean_Environment_setExporting, l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_bvar___override, l_Lean_Expr_const___override,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isProj,
    l_Lean_Expr_mvarId_x21, l_Lean_Expr_proj___override, l_Lean_Expr_projExpr_x21,
    l_Lean_Expr_sort___override, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkLambda,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAppM, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqTrans,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_realizeConst,
};
use crate::r#gen::Lean::Meta::Eqns::{
    l_Lean_Meta_ensureEqnReservedNamesAvailable, l_Lean_Meta_mkEqLikeNameFor,
    l_Lean_Meta_registerGetUnfoldEqnFn, l_Lean_Meta_unfoldThmSuffix,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::LetToHave::l_Lean_Meta_letToHave;
use crate::r#gen::Lean::Meta::Tactic::Delta::{
    initialize_Lean_Meta_Tactic_Delta, l_Lean_Meta_deltaExpand,
    runtime_initialize_Lean_Meta_Tactic_Delta,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_tactic_hygienic;
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, l_Lean_MVarId_refl, runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::l_Lean_MVarId_replaceTargetDefEq;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType_x27, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
    l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::Meta::TransparencyMode::l_Lean_Meta_TransparencyMode_lt;
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_smartUnfolding;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value:
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
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1_value:
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
            l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3_value:
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
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 113, 110, 73, 110, 102, 111, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14538583185260052093 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,60575703006878408 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_PartialFixpoint_eqnInfoExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 101, 108, 116, 97, 76, 72, 83, 85, 110, 116, 105, 108, 70, 105, 120, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value) as *mut leanh::LeanObject,11109162375831805875 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 113, 117, 97, 108, 105, 116, 121, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 114, 100, 101, 114, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 105, 120, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value) as *mut leanh::LeanObject,1180902349914728466 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [108, 102, 112, 95, 109, 111, 110, 111, 116, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value) as *mut leanh::LeanObject,2249643242235982818 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [114, 119, 70, 105, 120, 85, 110, 100, 101, 114, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [112, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value) as *mut leanh::LeanObject,9720699510028671266 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value) as *mut leanh::LeanObject,2642306550782628284 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12: usize = 0;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [76, 101, 97, 110, 46, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14_value: leanh::LeanStringObject<47> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 48, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 80, 114, 111, 106, 33, 73, 109, 112, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 111, 106, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 103, 114, 70, 117, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value) as *mut leanh::LeanObject,10988039791356833343 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 102, 112, 95, 109, 111, 110, 111, 116, 111, 110, 101, 95, 102, 105, 120, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value) as *mut leanh::LeanObject,5842129990421541298 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 105, 120, 95, 101, 113, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value) as *mut leanh::LeanObject,1315671465214526803 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0_value: leanh::LeanStringObject<45> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 46, 69, 113, 110, 115, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1_value: leanh::LeanStringObject<90> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 90, m_capacity: 90, m_length: 89, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 46, 69, 113, 110, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 46, 114, 119, 70, 105, 120, 69, 113, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [109, 107, 85, 110, 102, 111, 108, 100, 69, 113, 32, 114, 102, 108, 32, 115, 117, 99, 99, 101, 101, 100, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [109, 107, 85, 110, 102, 111, 108, 100, 69, 113, 32, 97, 102, 116, 101, 114, 32, 114, 119, 70, 105, 120, 69, 113, 58, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [109, 107, 85, 110, 102, 111, 108, 100, 69, 113, 32, 97, 102, 116, 101, 114, 32, 100, 101, 108, 116, 97, 76, 72, 83, 58, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 117, 110, 102, 111, 108, 100, 32, 116, 104, 101, 111, 114, 101, 109, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [96, 58, 10, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [112, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12843180897352504333 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value) as *mut leanh::LeanObject,6897119537390546559 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_value) as *mut leanh::LeanObject,3297018234817926677 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [109, 107, 85, 110, 102, 111, 108, 100, 69, 113, 32, 115, 116, 97, 114, 116, 58, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = leanh::lean_box(0);
    v___x_2173_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1;
    v___x_2174_ = l_Lean_Expr_const___override(v___x_2173_, v___x_2172_);
    return v___x_2174_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
    v___x_2178_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3;
    v___x_2179_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2_once
        ),
        _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2,
    );
    v___x_2180_ = leanh::lean_box(0);
    v___x_2181_ = leanh::lean_box(0);
    v___x_2182_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_2182_, 0, v___x_2181_);
    leanh::lean_ctor_set(v___x_2182_, 1, v___x_2180_);
    leanh::lean_ctor_set(v___x_2182_, 2, v___x_2179_);
    leanh::lean_ctor_set(v___x_2182_, 3, v___x_2179_);
    leanh::lean_ctor_set(v___x_2182_, 4, v___x_2178_);
    leanh::lean_ctor_set(v___x_2182_, 5, v___x_2181_);
    leanh::lean_ctor_set(v___x_2182_, 6, v___x_2177_);
    leanh::lean_ctor_set(v___x_2182_, 7, v___x_2178_);
    return v___x_2182_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4_once
        ),
        _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4,
    );
    return v___x_2183_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo()
-> *mut leanh::LeanObject {
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2184_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
    return v___x_2184_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_(
    mut v_env_2185_: *mut leanh::LeanObject,
    mut v_n_2186_: *mut leanh::LeanObject,
    mut v_x_2187_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2188_: u8 = 0;
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ = 1;
    v___x_2189_ = l_Lean_Environment_setExporting(v_env_2185_, v___x_2188_);
    v___x_2190_ = 0;
    v___x_2191_ = l_Lean_Environment_find_x3f(v___x_2189_, v_n_2186_, v___x_2190_);
    if leanh::lean_obj_tag(v___x_2191_) == 0 {
        return v___x_2190_;
    } else {
        let mut v_val_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: u8 = 0;
        v_val_2192_ = leanh::lean_ctor_get(v___x_2191_, 0);
        leanh::lean_inc(v_val_2192_);
        leanh::lean_dec_ref_known(v___x_2191_, 1);
        v___x_2193_ = l_Lean_ConstantInfo_hasValue(v_val_2192_, v___x_2190_);
        leanh::lean_dec(v_val_2192_);
        return v___x_2193_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2____boxed(
    mut v_env_2194_: *mut leanh::LeanObject,
    mut v_n_2195_: *mut leanh::LeanObject,
    mut v_x_2196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2197_: u8 = 0;
    let mut v_r_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2197_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_(v_env_2194_, v_n_2195_, v_x_2196_);
    leanh::lean_dec_ref(v_x_2196_);
    v_r_2198_ = leanh::lean_box((v_res_2197_) as usize);
    return v_r_2198_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_2199_: *mut leanh::LeanObject,
    mut v_x_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2200_) == 0 {
                    v_k_2201_ = leanh::lean_ctor_get(v_x_2200_, 1);
                    v_v_2202_ = leanh::lean_ctor_get(v_x_2200_, 2);
                    v_l_2203_ = leanh::lean_ctor_get(v_x_2200_, 3);
                    v_r_2204_ = leanh::lean_ctor_get(v_x_2200_, 4);
                    v___x_2205_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_2199_, v_l_2203_);
                    leanh::lean_inc(v_v_2202_);
                    leanh::lean_inc(v_k_2201_);
                    v___x_2206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2206_, 0, v_k_2201_);
                    leanh::lean_ctor_set(v___x_2206_, 1, v_v_2202_);
                    v___x_2207_ = lean_array_push(v___x_2205_, v___x_2206_);
                    v_init_2199_ = v___x_2207_;
                    v_x_2200_ = v_r_2204_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2199_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_2209_: *mut leanh::LeanObject,
    mut v_x_2210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2211_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_2209_, v_x_2210_);
    leanh::lean_dec(v_x_2210_);
    return v_res_2211_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_(
    mut v_env_2214_: *mut leanh::LeanObject,
    mut v_s_2215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2216_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___f_2216_, 0, v_env_2214_);
    v___x_2217_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_;
    v_all_2218_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_2217_, v_s_2215_);
    v___x_2219_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
        v___f_2216_,
        v_s_2215_,
    );
    v_exported_2220_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_2217_, v___x_2219_);
    leanh::lean_dec(v___x_2219_);
    leanh::lean_inc_ref(v_exported_2220_);
    v___x_2221_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2221_, 0, v_exported_2220_);
    leanh::lean_ctor_set(v___x_2221_, 1, v_exported_2220_);
    leanh::lean_ctor_set(v___x_2221_, 2, v_all_2218_);
    return v___x_2221_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2235_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_;
    v___x_2236_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_;
    v___x_2237_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_;
    v___x_2238_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_2236_, v___x_2237_, v___f_2235_);
    return v___x_2238_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2____boxed(
    mut v_a_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_();
    return v_res_2240_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0(
    mut v_init_2241_: *mut leanh::LeanObject,
    mut v_t_2242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_2241_, v_t_2242_);
    return v___x_2243_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_2244_: *mut leanh::LeanObject,
    mut v_t_2245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2246_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0(v_init_2244_, v_t_2245_);
    leanh::lean_dec(v_t_2245_);
    return v_res_2246_;
}
pub unsafe fn l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(
    mut v___x_2247_: u8,
    mut v___x_2248_: u8,
    mut v_____do__lift_2249_: u8,
    mut v___y_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
    mut v___y_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_2249_ == 0 {
        let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2255_ = leanh::lean_box((v___x_2247_) as usize);
        v___x_2256_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2256_, 0, v___x_2255_);
        return v___x_2256_;
    } else {
        let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2257_ = leanh::lean_box((v___x_2248_) as usize);
        v___x_2258_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2258_, 0, v___x_2257_);
        return v___x_2258_;
    }
}
pub unsafe fn l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(
    mut v___x_2259_: *mut leanh::LeanObject,
    mut v___x_2260_: *mut leanh::LeanObject,
    mut v_____do__lift_2261_: *mut leanh::LeanObject,
    mut v___y_2262_: *mut leanh::LeanObject,
    mut v___y_2263_: *mut leanh::LeanObject,
    mut v___y_2264_: *mut leanh::LeanObject,
    mut v___y_2265_: *mut leanh::LeanObject,
    mut v___y_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4040__boxed_2267_: u8 = 0;
    let mut v___x_4041__boxed_2268_: u8 = 0;
    let mut v_____do__lift_4042__boxed_2269_: u8 = 0;
    let mut v_res_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4040__boxed_2267_ = (leanh::lean_unbox(v___x_2259_) as u8);
    v___x_4041__boxed_2268_ = (leanh::lean_unbox(v___x_2260_) as u8);
    v_____do__lift_4042__boxed_2269_ = (leanh::lean_unbox(v_____do__lift_2261_) as u8);
    v_res_2270_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(
        v___x_4040__boxed_2267_,
        v___x_4041__boxed_2268_,
        v_____do__lift_4042__boxed_2269_,
        v___y_2262_,
        v___y_2263_,
        v___y_2264_,
        v___y_2265_,
    );
    leanh::lean_dec(v___y_2265_);
    leanh::lean_dec_ref(v___y_2264_);
    leanh::lean_dec(v___y_2263_);
    leanh::lean_dec_ref(v___y_2262_);
    return v_res_2270_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(
    mut v_as_2271_: *mut leanh::LeanObject,
    mut v_i_2272_: usize,
    mut v_stop_2273_: usize,
) -> u8 {
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2276_: u8 = 0;
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: usize = 0;
    let mut v___x_2280_: usize = 0;
    let mut v___x_2282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2274_ = lean_usize_dec_eq(v_i_2272_, v_stop_2273_);
                if v___x_2274_ == 0 {
                    v___x_2275_ = lean_array_uget_borrowed(v_as_2271_, v_i_2272_);
                    v_kind_2276_ = leanh::lean_ctor_get_uint8(
                        v___x_2275_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 9) as u32,
                    );
                    v___x_2277_ = 1;
                    v___x_2278_ = l_Lean_Elab_DefKind_isTheorem(v_kind_2276_);
                    if v___x_2278_ == 0 {
                        return v___x_2277_;
                    } else {
                        if v___x_2274_ == 0 {
                            v___x_2279_ = 1usize;
                            v___x_2280_ = lean_usize_add(v_i_2272_, v___x_2279_);
                            v_i_2272_ = v___x_2280_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2277_;
                        }
                    }
                } else {
                    v___x_2282_ = 0;
                    return v___x_2282_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(
    mut v_as_2283_: *mut leanh::LeanObject,
    mut v_i_2284_: *mut leanh::LeanObject,
    mut v_stop_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2286_: usize = 0;
    let mut v_stop_boxed_2287_: usize = 0;
    let mut v_res_2288_: u8 = 0;
    let mut v_r_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2286_ = leanh::lean_unbox_usize(v_i_2284_);
    leanh::lean_dec(v_i_2284_);
    v_stop_boxed_2287_ = leanh::lean_unbox_usize(v_stop_2285_);
    leanh::lean_dec(v_stop_2285_);
    v_res_2288_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_2283_, v_i_boxed_2286_, v_stop_boxed_2287_);
    leanh::lean_dec_ref(v_as_2283_);
    v_r_2289_ = leanh::lean_box((v_res_2288_) as usize);
    return v_r_2289_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(
    mut v___x_2290_: *mut leanh::LeanObject,
    mut v_declNameNonRec_2291_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_2292_: *mut leanh::LeanObject,
    mut v_fixpointType_2293_: *mut leanh::LeanObject,
    mut v_as_2294_: *mut leanh::LeanObject,
    mut v_i_2295_: usize,
    mut v_stop_2296_: usize,
    mut v_b_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: usize = 0;
    let mut v___x_2308_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2298_ = lean_usize_dec_eq(v_i_2295_, v_stop_2296_);
                if v___x_2298_ == 0 {
                    v___x_2299_ = lean_array_uget_borrowed(v_as_2294_, v_i_2295_);
                    v_levelParams_2300_ = leanh::lean_ctor_get(v___x_2299_, 1);
                    v_declName_2301_ = leanh::lean_ctor_get(v___x_2299_, 3);
                    v_type_2302_ = leanh::lean_ctor_get(v___x_2299_, 6);
                    v_value_2303_ = leanh::lean_ctor_get(v___x_2299_, 7);
                    v___x_2304_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
                    leanh::lean_inc_ref(v_fixpointType_2293_);
                    leanh::lean_inc_ref(v_fixedParamPerms_2292_);
                    leanh::lean_inc(v_declNameNonRec_2291_);
                    leanh::lean_inc_ref(v___x_2290_);
                    leanh::lean_inc_ref(v_value_2303_);
                    leanh::lean_inc_ref(v_type_2302_);
                    leanh::lean_inc(v_levelParams_2300_);
                    leanh::lean_inc_n(v_declName_2301_, 2);
                    v___x_2305_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v___x_2305_, 0, v_declName_2301_);
                    leanh::lean_ctor_set(v___x_2305_, 1, v_levelParams_2300_);
                    leanh::lean_ctor_set(v___x_2305_, 2, v_type_2302_);
                    leanh::lean_ctor_set(v___x_2305_, 3, v_value_2303_);
                    leanh::lean_ctor_set(v___x_2305_, 4, v___x_2290_);
                    leanh::lean_ctor_set(v___x_2305_, 5, v_declNameNonRec_2291_);
                    leanh::lean_ctor_set(v___x_2305_, 6, v_fixedParamPerms_2292_);
                    leanh::lean_ctor_set(v___x_2305_, 7, v_fixpointType_2293_);
                    v___x_2306_ = l_Lean_MapDeclarationExtension_insert___redArg(
                        v___x_2304_,
                        v_b_2297_,
                        v_declName_2301_,
                        v___x_2305_,
                    );
                    v___x_2307_ = 1usize;
                    v___x_2308_ = lean_usize_add(v_i_2295_, v___x_2307_);
                    v_i_2295_ = v___x_2308_;
                    v_b_2297_ = v___x_2306_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_fixpointType_2293_);
                    leanh::lean_dec_ref(v_fixedParamPerms_2292_);
                    leanh::lean_dec(v_declNameNonRec_2291_);
                    leanh::lean_dec_ref(v___x_2290_);
                    return v_b_2297_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(
    mut v___x_2310_: *mut leanh::LeanObject,
    mut v_declNameNonRec_2311_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_2312_: *mut leanh::LeanObject,
    mut v_fixpointType_2313_: *mut leanh::LeanObject,
    mut v_as_2314_: *mut leanh::LeanObject,
    mut v_i_2315_: *mut leanh::LeanObject,
    mut v_stop_2316_: *mut leanh::LeanObject,
    mut v_b_2317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2318_: usize = 0;
    let mut v_stop_boxed_2319_: usize = 0;
    let mut v_res_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2318_ = leanh::lean_unbox_usize(v_i_2315_);
    leanh::lean_dec(v_i_2315_);
    v_stop_boxed_2319_ = leanh::lean_unbox_usize(v_stop_2316_);
    leanh::lean_dec(v_stop_2316_);
    v_res_2320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_2310_, v_declNameNonRec_2311_, v_fixedParamPerms_2312_, v_fixpointType_2313_, v_as_2314_, v_i_boxed_2318_, v_stop_boxed_2319_, v_b_2317_);
    leanh::lean_dec_ref(v_as_2314_);
    return v_res_2320_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(
    mut v_sz_2321_: usize,
    mut v_i_2322_: usize,
    mut v_bs_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2324_: u8 = 0;
    let mut v_v_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2324_ = lean_usize_dec_lt(v_i_2322_, v_sz_2321_);
                if v___x_2324_ == 0 {
                    return v_bs_2323_;
                } else {
                    v_v_2325_ = lean_array_uget_borrowed(v_bs_2323_, v_i_2322_);
                    v_declName_2326_ = leanh::lean_ctor_get(v_v_2325_, 3);
                    leanh::lean_inc(v_declName_2326_);
                    v___x_2327_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2328_ = lean_array_uset(v_bs_2323_, v_i_2322_, v___x_2327_);
                    v___x_2329_ = 1usize;
                    v___x_2330_ = lean_usize_add(v_i_2322_, v___x_2329_);
                    v___x_2331_ = lean_array_uset(v_bs_x27_2328_, v_i_2322_, v_declName_2326_);
                    v_i_2322_ = v___x_2330_;
                    v_bs_2323_ = v___x_2331_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(
    mut v_sz_2333_: *mut leanh::LeanObject,
    mut v_i_2334_: *mut leanh::LeanObject,
    mut v_bs_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2336_: usize = 0;
    let mut v_i_boxed_2337_: usize = 0;
    let mut v_res_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2336_ = leanh::lean_unbox_usize(v_sz_2333_);
    leanh::lean_dec(v_sz_2333_);
    v_i_boxed_2337_ = leanh::lean_unbox_usize(v_i_2334_);
    leanh::lean_dec(v_i_2334_);
    v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_2336_, v_i_boxed_2337_, v_bs_2335_);
    return v_res_2338_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(
    mut v_as_2339_: *mut leanh::LeanObject,
    mut v_i_2340_: usize,
    mut v_stop_2341_: usize,
    mut v_b_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: usize = 0;
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2346_ = lean_usize_dec_eq(v_i_2340_, v_stop_2341_);
                if v___x_2346_ == 0 {
                    v___x_2347_ = lean_array_uget_borrowed(v_as_2339_, v_i_2340_);
                    v_declName_2348_ = leanh::lean_ctor_get(v___x_2347_, 3);
                    leanh::lean_inc(v_declName_2348_);
                    v___x_2349_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(
                        v_declName_2348_,
                        v___y_2343_,
                        v___y_2344_,
                    );
                    if leanh::lean_obj_tag(v___x_2349_) == 0 {
                        v_a_2350_ = leanh::lean_ctor_get(v___x_2349_, 0);
                        leanh::lean_inc(v_a_2350_);
                        leanh::lean_dec_ref_known(v___x_2349_, 1);
                        v___x_2351_ = 1usize;
                        v___x_2352_ = lean_usize_add(v_i_2340_, v___x_2351_);
                        v_i_2340_ = v___x_2352_;
                        v_b_2342_ = v_a_2350_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2349_;
                    }
                } else {
                    v___x_2354_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2354_, 0, v_b_2342_);
                    return v___x_2354_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(
    mut v_as_2355_: *mut leanh::LeanObject,
    mut v_i_2356_: *mut leanh::LeanObject,
    mut v_stop_2357_: *mut leanh::LeanObject,
    mut v_b_2358_: *mut leanh::LeanObject,
    mut v___y_2359_: *mut leanh::LeanObject,
    mut v___y_2360_: *mut leanh::LeanObject,
    mut v___y_2361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2362_: usize = 0;
    let mut v_stop_boxed_2363_: usize = 0;
    let mut v_res_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2362_ = leanh::lean_unbox_usize(v_i_2356_);
    leanh::lean_dec(v_i_2356_);
    v_stop_boxed_2363_ = leanh::lean_unbox_usize(v_stop_2357_);
    leanh::lean_dec(v_stop_2357_);
    v_res_2364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_2355_, v_i_boxed_2362_, v_stop_boxed_2363_, v_b_2358_, v___y_2359_, v___y_2360_);
    leanh::lean_dec(v___y_2360_);
    leanh::lean_dec_ref(v___y_2359_);
    leanh::lean_dec_ref(v_as_2355_);
    return v_res_2364_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(
    mut v___x_2365_: u8,
    mut v_as_2366_: *mut leanh::LeanObject,
    mut v_i_2367_: usize,
    mut v_stop_2368_: usize,
    mut v___y_2369_: *mut leanh::LeanObject,
    mut v___y_2370_: *mut leanh::LeanObject,
    mut v___y_2371_: *mut leanh::LeanObject,
    mut v___y_2372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2375_: usize = 0;
    let mut v___x_2376_: usize = 0;
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: u8 = 0;
    let mut v_a_2383_: u8 = 0;
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    let mut v_a_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2378_ = lean_usize_dec_eq(v_i_2367_, v_stop_2368_);
                if v___x_2378_ == 0 {
                    v___x_2379_ = lean_array_uget_borrowed(v_as_2366_, v_i_2367_);
                    v_type_2380_ = leanh::lean_ctor_get(v___x_2379_, 6);
                    v___x_2381_ = 1;
                    leanh::lean_inc_ref(v_type_2380_);
                    v___x_2386_ = l_Lean_Meta_isProp(
                        v_type_2380_,
                        v___y_2369_,
                        v___y_2370_,
                        v___y_2371_,
                        v___y_2372_,
                    );
                    if leanh::lean_obj_tag(v___x_2386_) == 0 {
                        v_a_2387_ = leanh::lean_ctor_get(v___x_2386_, 0);
                        leanh::lean_inc(v_a_2387_);
                        leanh::lean_dec_ref_known(v___x_2386_, 1);
                        v___x_2388_ = (leanh::lean_unbox(v_a_2387_) as u8);
                        leanh::lean_dec(v_a_2387_);
                        if v___x_2388_ == 0 {
                            v_a_2383_ = v___x_2365_;
                            state = 2;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_2386_) == 0 {
                            v_a_2389_ = leanh::lean_ctor_get(v___x_2386_, 0);
                            leanh::lean_inc(v_a_2389_);
                            leanh::lean_dec_ref_known(v___x_2386_, 1);
                            v___x_2390_ = (leanh::lean_unbox(v_a_2389_) as u8);
                            leanh::lean_dec(v_a_2389_);
                            v_a_2383_ = v___x_2390_;
                            state = 2;
                            continue;
                        } else {
                            return v___x_2386_;
                        }
                    }
                } else {
                    v___x_2391_ = 0;
                    v___x_2392_ = leanh::lean_box((v___x_2391_) as usize);
                    v___x_2393_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
                    return v___x_2393_;
                }
            }
            1 => {
                v___x_2375_ = 1usize;
                v___x_2376_ = lean_usize_add(v_i_2367_, v___x_2375_);
                v_i_2367_ = v___x_2376_;
                state = 0;
                continue;
            }
            2 => {
                if v_a_2383_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_2384_ = leanh::lean_box((v___x_2381_) as usize);
                    v___x_2385_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2385_, 0, v___x_2384_);
                    return v___x_2385_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(
    mut v___x_2394_: *mut leanh::LeanObject,
    mut v_as_2395_: *mut leanh::LeanObject,
    mut v_i_2396_: *mut leanh::LeanObject,
    mut v_stop_2397_: *mut leanh::LeanObject,
    mut v___y_2398_: *mut leanh::LeanObject,
    mut v___y_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
    mut v___y_2402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4145__boxed_2403_: u8 = 0;
    let mut v_i_boxed_2404_: usize = 0;
    let mut v_stop_boxed_2405_: usize = 0;
    let mut v_res_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4145__boxed_2403_ = (leanh::lean_unbox(v___x_2394_) as u8);
    v_i_boxed_2404_ = leanh::lean_unbox_usize(v_i_2396_);
    leanh::lean_dec(v_i_2396_);
    v_stop_boxed_2405_ = leanh::lean_unbox_usize(v_stop_2397_);
    leanh::lean_dec(v_stop_2397_);
    v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_4145__boxed_2403_, v_as_2395_, v_i_boxed_2404_, v_stop_boxed_2405_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
    leanh::lean_dec(v___y_2401_);
    leanh::lean_dec_ref(v___y_2400_);
    leanh::lean_dec(v___y_2399_);
    leanh::lean_dec_ref(v___y_2398_);
    leanh::lean_dec_ref(v_as_2395_);
    return v_res_2406_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2407_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2407_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2408_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once),
        _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0,
    );
    v___x_2409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2409_, 0, v___x_2408_);
    return v___x_2409_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2410_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once),
        _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1,
    );
    v___x_2411_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2411_, 0, v___x_2410_);
    leanh::lean_ctor_set(v___x_2411_, 1, v___x_2410_);
    return v___x_2411_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2412_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once),
        _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1,
    );
    v___x_2413_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2413_, 0, v___x_2412_);
    leanh::lean_ctor_set(v___x_2413_, 1, v___x_2412_);
    leanh::lean_ctor_set(v___x_2413_, 2, v___x_2412_);
    leanh::lean_ctor_set(v___x_2413_, 3, v___x_2412_);
    leanh::lean_ctor_set(v___x_2413_, 4, v___x_2412_);
    leanh::lean_ctor_set(v___x_2413_, 5, v___x_2412_);
    return v___x_2413_;
}
pub unsafe fn l_Lean_Elab_PartialFixpoint_registerEqnsInfo(
    mut v_preDefs_2414_: *mut leanh::LeanObject,
    mut v_declNameNonRec_2415_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_2416_: *mut leanh::LeanObject,
    mut v_fixpointType_2417_: *mut leanh::LeanObject,
    mut v_a_2418_: *mut leanh::LeanObject,
    mut v_a_2419_: *mut leanh::LeanObject,
    mut v_a_2420_: *mut leanh::LeanObject,
    mut v_a_2421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2445_: u8 = 0;
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2453_: u8 = 0;
    let mut v_unused_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: u8 = 0;
    let mut v_sz_2474_: usize = 0;
    let mut v___x_2475_: usize = 0;
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: u8 = 0;
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: usize = 0;
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2489_: u8 = 0;
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: usize = 0;
    let mut v___x_2493_: usize = 0;
    let mut v___x_2494_: u8 = 0;
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: u8 = 0;
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: u8 = 0;
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: usize = 0;
    let mut v___x_2507_: usize = 0;
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: usize = 0;
    let mut v___x_2510_: usize = 0;
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2458_ = leanh::lean_unsigned_to_nat(0);
                v___x_2459_ = lean_array_get_size(v_preDefs_2414_);
                v___x_2503_ = lean_nat_dec_lt(v___x_2458_, v___x_2459_);
                if v___x_2503_ == 0 {
                    state = 9;
                    continue;
                } else {
                    v___x_2504_ = leanh::lean_box(0);
                    v___x_2505_ = lean_nat_dec_le(v___x_2459_, v___x_2459_);
                    if v___x_2505_ == 0 {
                        if v___x_2503_ == 0 {
                            state = 9;
                            continue;
                        } else {
                            v___x_2506_ = 0usize;
                            v___x_2507_ = lean_usize_of_nat(v___x_2459_);
                            v___x_2508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_2414_, v___x_2506_, v___x_2507_, v___x_2504_, v_a_2420_, v_a_2421_);
                            v___y_2502_ = v___x_2508_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___x_2509_ = 0usize;
                        v___x_2510_ = lean_usize_of_nat(v___x_2459_);
                        v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_preDefs_2414_, v___x_2509_, v___x_2510_, v___x_2504_, v_a_2420_, v_a_2421_);
                        v___y_2502_ = v___x_2511_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2424_ = leanh::lean_box(0);
                v___x_2425_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
                return v___x_2425_;
            }
            2 => {
                v___x_2435_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once
                    ),
                    _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2,
                );
                v___x_2436_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                leanh::lean_ctor_set(v___x_2436_, 0, v___y_2434_);
                leanh::lean_ctor_set(v___x_2436_, 1, v_nextMacroScope_2427_);
                leanh::lean_ctor_set(v___x_2436_, 2, v_ngen_2428_);
                leanh::lean_ctor_set(v___x_2436_, 3, v_auxDeclNGen_2429_);
                leanh::lean_ctor_set(v___x_2436_, 4, v_traceState_2430_);
                leanh::lean_ctor_set(v___x_2436_, 5, v___x_2435_);
                leanh::lean_ctor_set(v___x_2436_, 6, v_messages_2431_);
                leanh::lean_ctor_set(v___x_2436_, 7, v_infoState_2432_);
                leanh::lean_ctor_set(v___x_2436_, 8, v_snapshotTasks_2433_);
                v___x_2437_ = lean_st_ref_set(v_a_2421_, v___x_2436_);
                v___x_2438_ = lean_st_ref_take(v_a_2419_);
                v_mctx_2439_ = leanh::lean_ctor_get(v___x_2438_, 0);
                v_zetaDeltaFVarIds_2440_ = leanh::lean_ctor_get(v___x_2438_, 2);
                v_postponed_2441_ = leanh::lean_ctor_get(v___x_2438_, 3);
                v_diag_2442_ = leanh::lean_ctor_get(v___x_2438_, 4);
                v_isSharedCheck_2453_ = (!leanh::lean_is_exclusive(v___x_2438_)) as u8;
                if v_isSharedCheck_2453_ == 0 {
                    v_unused_2454_ = leanh::lean_ctor_get(v___x_2438_, 1);
                    leanh::lean_dec(v_unused_2454_);
                    v___x_2444_ = v___x_2438_;
                    v_isShared_2445_ = v_isSharedCheck_2453_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2442_);
                    leanh::lean_inc(v_postponed_2441_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2440_);
                    leanh::lean_inc(v_mctx_2439_);
                    leanh::lean_dec(v___x_2438_);
                    v___x_2444_ = leanh::lean_box(0);
                    v_isShared_2445_ = v_isSharedCheck_2453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2446_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once
                    ),
                    _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3,
                );
                if v_isShared_2445_ == 0 {
                    leanh::lean_ctor_set(v___x_2444_, 1, v___x_2446_);
                    v___x_2448_ = v___x_2444_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2452_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_mctx_2439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2446_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2452_,
                        2,
                        v_zetaDeltaFVarIds_2440_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_postponed_2441_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_diag_2442_);
                    v___x_2448_ = v_reuseFailAlloc_2452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2449_ = lean_st_ref_set(v_a_2419_, v___x_2448_);
                v___x_2450_ = leanh::lean_box(0);
                v___x_2451_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2451_, 0, v___x_2450_);
                return v___x_2451_;
            }
            5 => {
                v___x_2456_ = leanh::lean_box(0);
                v___x_2457_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2457_, 0, v___x_2456_);
                return v___x_2457_;
            }
            6 => {
                if leanh::lean_obj_tag(v___y_2461_) == 0 {
                    v_a_2462_ = leanh::lean_ctor_get(v___y_2461_, 0);
                    leanh::lean_inc(v_a_2462_);
                    leanh::lean_dec_ref_known(v___y_2461_, 1);
                    v___x_2463_ = (leanh::lean_unbox(v_a_2462_) as u8);
                    leanh::lean_dec(v_a_2462_);
                    if v___x_2463_ == 0 {
                        v___x_2464_ = lean_st_ref_take(v_a_2421_);
                        v_env_2465_ = leanh::lean_ctor_get(v___x_2464_, 0);
                        leanh::lean_inc_ref(v_env_2465_);
                        v_nextMacroScope_2466_ = leanh::lean_ctor_get(v___x_2464_, 1);
                        leanh::lean_inc(v_nextMacroScope_2466_);
                        v_ngen_2467_ = leanh::lean_ctor_get(v___x_2464_, 2);
                        leanh::lean_inc_ref(v_ngen_2467_);
                        v_auxDeclNGen_2468_ = leanh::lean_ctor_get(v___x_2464_, 3);
                        leanh::lean_inc_ref(v_auxDeclNGen_2468_);
                        v_traceState_2469_ = leanh::lean_ctor_get(v___x_2464_, 4);
                        leanh::lean_inc_ref(v_traceState_2469_);
                        v_messages_2470_ = leanh::lean_ctor_get(v___x_2464_, 6);
                        leanh::lean_inc_ref(v_messages_2470_);
                        v_infoState_2471_ = leanh::lean_ctor_get(v___x_2464_, 7);
                        leanh::lean_inc_ref(v_infoState_2471_);
                        v_snapshotTasks_2472_ = leanh::lean_ctor_get(v___x_2464_, 8);
                        leanh::lean_inc_ref(v_snapshotTasks_2472_);
                        leanh::lean_dec(v___x_2464_);
                        v___x_2473_ = lean_nat_dec_lt(v___x_2458_, v___x_2459_);
                        if v___x_2473_ == 0 {
                            leanh::lean_dec_ref(v_fixpointType_2417_);
                            leanh::lean_dec_ref(v_fixedParamPerms_2416_);
                            leanh::lean_dec(v_declNameNonRec_2415_);
                            leanh::lean_dec_ref(v_preDefs_2414_);
                            v_nextMacroScope_2427_ = v_nextMacroScope_2466_;
                            v_ngen_2428_ = v_ngen_2467_;
                            v_auxDeclNGen_2429_ = v_auxDeclNGen_2468_;
                            v_traceState_2430_ = v_traceState_2469_;
                            v_messages_2431_ = v_messages_2470_;
                            v_infoState_2432_ = v_infoState_2471_;
                            v_snapshotTasks_2433_ = v_snapshotTasks_2472_;
                            v___y_2434_ = v_env_2465_;
                            state = 2;
                            continue;
                        } else {
                            v_sz_2474_ = lean_array_size(v_preDefs_2414_);
                            v___x_2475_ = 0usize;
                            leanh::lean_inc_ref(v_preDefs_2414_);
                            v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_2474_, v___x_2475_, v_preDefs_2414_);
                            v___x_2477_ = lean_nat_dec_le(v___x_2459_, v___x_2459_);
                            if v___x_2477_ == 0 {
                                if v___x_2473_ == 0 {
                                    leanh::lean_dec_ref(v___x_2476_);
                                    leanh::lean_dec_ref(v_fixpointType_2417_);
                                    leanh::lean_dec_ref(v_fixedParamPerms_2416_);
                                    leanh::lean_dec(v_declNameNonRec_2415_);
                                    leanh::lean_dec_ref(v_preDefs_2414_);
                                    v_nextMacroScope_2427_ = v_nextMacroScope_2466_;
                                    v_ngen_2428_ = v_ngen_2467_;
                                    v_auxDeclNGen_2429_ = v_auxDeclNGen_2468_;
                                    v_traceState_2430_ = v_traceState_2469_;
                                    v_messages_2431_ = v_messages_2470_;
                                    v_infoState_2432_ = v_infoState_2471_;
                                    v_snapshotTasks_2433_ = v_snapshotTasks_2472_;
                                    v___y_2434_ = v_env_2465_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2478_ = lean_usize_of_nat(v___x_2459_);
                                    v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_2476_, v_declNameNonRec_2415_, v_fixedParamPerms_2416_, v_fixpointType_2417_, v_preDefs_2414_, v___x_2475_, v___x_2478_, v_env_2465_);
                                    leanh::lean_dec_ref(v_preDefs_2414_);
                                    v_nextMacroScope_2427_ = v_nextMacroScope_2466_;
                                    v_ngen_2428_ = v_ngen_2467_;
                                    v_auxDeclNGen_2429_ = v_auxDeclNGen_2468_;
                                    v_traceState_2430_ = v_traceState_2469_;
                                    v_messages_2431_ = v_messages_2470_;
                                    v_infoState_2432_ = v_infoState_2471_;
                                    v_snapshotTasks_2433_ = v_snapshotTasks_2472_;
                                    v___y_2434_ = v___x_2479_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_2480_ = lean_usize_of_nat(v___x_2459_);
                                v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_2476_, v_declNameNonRec_2415_, v_fixedParamPerms_2416_, v_fixpointType_2417_, v_preDefs_2414_, v___x_2475_, v___x_2480_, v_env_2465_);
                                leanh::lean_dec_ref(v_preDefs_2414_);
                                v_nextMacroScope_2427_ = v_nextMacroScope_2466_;
                                v_ngen_2428_ = v_ngen_2467_;
                                v_auxDeclNGen_2429_ = v_auxDeclNGen_2468_;
                                v_traceState_2430_ = v_traceState_2469_;
                                v_messages_2431_ = v_messages_2470_;
                                v_infoState_2432_ = v_infoState_2471_;
                                v_snapshotTasks_2433_ = v_snapshotTasks_2472_;
                                v___y_2434_ = v___x_2481_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_fixpointType_2417_);
                        leanh::lean_dec_ref(v_fixedParamPerms_2416_);
                        leanh::lean_dec(v_declNameNonRec_2415_);
                        leanh::lean_dec_ref(v_preDefs_2414_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_fixpointType_2417_);
                    leanh::lean_dec_ref(v_fixedParamPerms_2416_);
                    leanh::lean_dec(v_declNameNonRec_2415_);
                    leanh::lean_dec_ref(v_preDefs_2414_);
                    v_a_2482_ = leanh::lean_ctor_get(v___y_2461_, 0);
                    v_isSharedCheck_2489_ = (!leanh::lean_is_exclusive(v___y_2461_)) as u8;
                    if v_isSharedCheck_2489_ == 0 {
                        v___x_2484_ = v___y_2461_;
                        v_isShared_2485_ = v_isSharedCheck_2489_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2482_);
                        leanh::lean_dec(v___y_2461_);
                        v___x_2484_ = leanh::lean_box(0);
                        v_isShared_2485_ = v_isSharedCheck_2489_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2485_ == 0 {
                    v___x_2487_ = v___x_2484_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2488_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
                    v___x_2487_ = v_reuseFailAlloc_2488_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2487_;
            }
            9 => {
                v___x_2491_ = lean_nat_dec_lt(v___x_2458_, v___x_2459_);
                if v___x_2491_ == 0 {
                    leanh::lean_dec_ref(v_fixpointType_2417_);
                    leanh::lean_dec_ref(v_fixedParamPerms_2416_);
                    leanh::lean_dec(v_declNameNonRec_2415_);
                    leanh::lean_dec_ref(v_preDefs_2414_);
                    state = 5;
                    continue;
                } else {
                    if v___x_2491_ == 0 {
                        leanh::lean_dec_ref(v_fixpointType_2417_);
                        leanh::lean_dec_ref(v_fixedParamPerms_2416_);
                        leanh::lean_dec(v_declNameNonRec_2415_);
                        leanh::lean_dec_ref(v_preDefs_2414_);
                        state = 5;
                        continue;
                    } else {
                        v___x_2492_ = 0usize;
                        v___x_2493_ = lean_usize_of_nat(v___x_2459_);
                        v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_2414_, v___x_2492_, v___x_2493_);
                        if v___x_2494_ == 0 {
                            leanh::lean_dec_ref(v_fixpointType_2417_);
                            leanh::lean_dec_ref(v_fixedParamPerms_2416_);
                            leanh::lean_dec(v_declNameNonRec_2415_);
                            leanh::lean_dec_ref(v_preDefs_2414_);
                            state = 5;
                            continue;
                        } else {
                            v___x_2495_ = 0;
                            if v___x_2491_ == 0 {
                                v___x_2496_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(
                                    v___x_2494_,
                                    v___x_2495_,
                                    v___x_2495_,
                                    v_a_2418_,
                                    v_a_2419_,
                                    v_a_2420_,
                                    v_a_2421_,
                                );
                                v___y_2461_ = v___x_2496_;
                                state = 6;
                                continue;
                            } else {
                                if v___x_2491_ == 0 {
                                    leanh::lean_dec_ref(v_fixpointType_2417_);
                                    leanh::lean_dec_ref(v_fixedParamPerms_2416_);
                                    leanh::lean_dec(v_declNameNonRec_2415_);
                                    leanh::lean_dec_ref(v_preDefs_2414_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_2494_, v_preDefs_2414_, v___x_2492_, v___x_2493_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
                                    if leanh::lean_obj_tag(v___x_2497_) == 0 {
                                        v_a_2498_ = leanh::lean_ctor_get(v___x_2497_, 0);
                                        leanh::lean_inc(v_a_2498_);
                                        leanh::lean_dec_ref_known(v___x_2497_, 1);
                                        v___x_2499_ = (leanh::lean_unbox(v_a_2498_) as u8);
                                        leanh::lean_dec(v_a_2498_);
                                        v___x_2500_ =
                                            l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(
                                                v___x_2494_,
                                                v___x_2495_,
                                                v___x_2499_,
                                                v_a_2418_,
                                                v_a_2419_,
                                                v_a_2420_,
                                                v_a_2421_,
                                            );
                                        v___y_2461_ = v___x_2500_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v___y_2461_ = v___x_2497_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            10 => {
                if leanh::lean_obj_tag(v___y_2502_) == 0 {
                    leanh::lean_dec_ref_known(v___y_2502_, 1);
                    state = 9;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_fixpointType_2417_);
                    leanh::lean_dec_ref(v_fixedParamPerms_2416_);
                    leanh::lean_dec(v_declNameNonRec_2415_);
                    leanh::lean_dec_ref(v_preDefs_2414_);
                    return v___y_2502_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(
    mut v_preDefs_2512_: *mut leanh::LeanObject,
    mut v_declNameNonRec_2513_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_2514_: *mut leanh::LeanObject,
    mut v_fixpointType_2515_: *mut leanh::LeanObject,
    mut v_a_2516_: *mut leanh::LeanObject,
    mut v_a_2517_: *mut leanh::LeanObject,
    mut v_a_2518_: *mut leanh::LeanObject,
    mut v_a_2519_: *mut leanh::LeanObject,
    mut v_a_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(
        v_preDefs_2512_,
        v_declNameNonRec_2513_,
        v_fixedParamPerms_2514_,
        v_fixpointType_2515_,
        v_a_2516_,
        v_a_2517_,
        v_a_2518_,
        v_a_2519_,
    );
    leanh::lean_dec(v_a_2519_);
    leanh::lean_dec_ref(v_a_2518_);
    leanh::lean_dec(v_a_2517_);
    leanh::lean_dec_ref(v_a_2516_);
    return v_res_2521_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(
    mut v_as_2522_: *mut leanh::LeanObject,
    mut v_i_2523_: usize,
    mut v_stop_2524_: usize,
    mut v_b_2525_: *mut leanh::LeanObject,
    mut v___y_2526_: *mut leanh::LeanObject,
    mut v___y_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_2522_, v_i_2523_, v_stop_2524_, v_b_2525_, v___y_2528_, v___y_2529_);
    return v___x_2531_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(
    mut v_as_2532_: *mut leanh::LeanObject,
    mut v_i_2533_: *mut leanh::LeanObject,
    mut v_stop_2534_: *mut leanh::LeanObject,
    mut v_b_2535_: *mut leanh::LeanObject,
    mut v___y_2536_: *mut leanh::LeanObject,
    mut v___y_2537_: *mut leanh::LeanObject,
    mut v___y_2538_: *mut leanh::LeanObject,
    mut v___y_2539_: *mut leanh::LeanObject,
    mut v___y_2540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2541_: usize = 0;
    let mut v_stop_boxed_2542_: usize = 0;
    let mut v_res_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2541_ = leanh::lean_unbox_usize(v_i_2533_);
    leanh::lean_dec(v_i_2533_);
    v_stop_boxed_2542_ = leanh::lean_unbox_usize(v_stop_2534_);
    leanh::lean_dec(v_stop_2534_);
    v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_2532_, v_i_boxed_2541_, v_stop_boxed_2542_, v_b_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
    leanh::lean_dec(v___y_2539_);
    leanh::lean_dec_ref(v___y_2538_);
    leanh::lean_dec(v___y_2537_);
    leanh::lean_dec_ref(v___y_2536_);
    leanh::lean_dec_ref(v_as_2532_);
    return v_res_2543_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(
    mut v_mvarId_2544_: *mut leanh::LeanObject,
    mut v_x_2545_: *mut leanh::LeanObject,
    mut v___y_2546_: *mut leanh::LeanObject,
    mut v___y_2547_: *mut leanh::LeanObject,
    mut v___y_2548_: *mut leanh::LeanObject,
    mut v___y_2549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_a_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2563_: u8 = 0;
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2551_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_2544_,
                    v_x_2545_,
                    v___y_2546_,
                    v___y_2547_,
                    v___y_2548_,
                    v___y_2549_,
                );
                if leanh::lean_obj_tag(v___x_2551_) == 0 {
                    v_a_2552_ = leanh::lean_ctor_get(v___x_2551_, 0);
                    v_isSharedCheck_2559_ = (!leanh::lean_is_exclusive(v___x_2551_)) as u8;
                    if v_isSharedCheck_2559_ == 0 {
                        v___x_2554_ = v___x_2551_;
                        v_isShared_2555_ = v_isSharedCheck_2559_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2552_);
                        leanh::lean_dec(v___x_2551_);
                        v___x_2554_ = leanh::lean_box(0);
                        v_isShared_2555_ = v_isSharedCheck_2559_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2560_ = leanh::lean_ctor_get(v___x_2551_, 0);
                    v_isSharedCheck_2567_ = (!leanh::lean_is_exclusive(v___x_2551_)) as u8;
                    if v_isSharedCheck_2567_ == 0 {
                        v___x_2562_ = v___x_2551_;
                        v_isShared_2563_ = v_isSharedCheck_2567_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2560_);
                        leanh::lean_dec(v___x_2551_);
                        v___x_2562_ = leanh::lean_box(0);
                        v_isShared_2563_ = v_isSharedCheck_2567_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2555_ == 0 {
                    v___x_2557_ = v___x_2554_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
                    v___x_2557_ = v_reuseFailAlloc_2558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2557_;
            }
            3 => {
                if v_isShared_2563_ == 0 {
                    v___x_2565_ = v___x_2562_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2566_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
                    v___x_2565_ = v_reuseFailAlloc_2566_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2565_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg___boxed(
    mut v_mvarId_2568_: *mut leanh::LeanObject,
    mut v_x_2569_: *mut leanh::LeanObject,
    mut v___y_2570_: *mut leanh::LeanObject,
    mut v___y_2571_: *mut leanh::LeanObject,
    mut v___y_2572_: *mut leanh::LeanObject,
    mut v___y_2573_: *mut leanh::LeanObject,
    mut v___y_2574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2575_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2568_, v_x_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
    leanh::lean_dec(v___y_2573_);
    leanh::lean_dec_ref(v___y_2572_);
    leanh::lean_dec(v___y_2571_);
    leanh::lean_dec_ref(v___y_2570_);
    return v_res_2575_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(
    mut v_00_u03b1_2576_: *mut leanh::LeanObject,
    mut v_mvarId_2577_: *mut leanh::LeanObject,
    mut v_x_2578_: *mut leanh::LeanObject,
    mut v___y_2579_: *mut leanh::LeanObject,
    mut v___y_2580_: *mut leanh::LeanObject,
    mut v___y_2581_: *mut leanh::LeanObject,
    mut v___y_2582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2577_, v_x_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
    return v___x_2584_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(
    mut v_00_u03b1_2585_: *mut leanh::LeanObject,
    mut v_mvarId_2586_: *mut leanh::LeanObject,
    mut v_x_2587_: *mut leanh::LeanObject,
    mut v___y_2588_: *mut leanh::LeanObject,
    mut v___y_2589_: *mut leanh::LeanObject,
    mut v___y_2590_: *mut leanh::LeanObject,
    mut v___y_2591_: *mut leanh::LeanObject,
    mut v___y_2592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2593_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_2585_, v_mvarId_2586_, v_x_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
    leanh::lean_dec(v___y_2591_);
    leanh::lean_dec_ref(v___y_2590_);
    leanh::lean_dec(v___y_2589_);
    leanh::lean_dec_ref(v___y_2588_);
    return v_res_2593_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(
    mut v_declName_2594_: *mut leanh::LeanObject,
    mut v_declNameNonRec_2595_: *mut leanh::LeanObject,
    mut v_n_2596_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2597_: u8 = 0;
    v___x_2597_ = lean_name_eq(v_n_2596_, v_declName_2594_);
    if v___x_2597_ == 0 {
        let mut v___x_2598_: u8 = 0;
        v___x_2598_ = lean_name_eq(v_n_2596_, v_declNameNonRec_2595_);
        return v___x_2598_;
    } else {
        return v___x_2597_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(
    mut v_declName_2599_: *mut leanh::LeanObject,
    mut v_declNameNonRec_2600_: *mut leanh::LeanObject,
    mut v_n_2601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2602_: u8 = 0;
    let mut v_r_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2602_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_2599_, v_declNameNonRec_2600_, v_n_2601_);
    leanh::lean_dec(v_n_2601_);
    leanh::lean_dec(v_declNameNonRec_2600_);
    leanh::lean_dec(v_declName_2599_);
    v_r_2603_ = leanh::lean_box((v_res_2602_) as usize);
    return v_r_2603_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5;
    v___x_2614_ = l_Lean_MessageData_ofFormat(v___x_2613_);
    return v___x_2614_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2615_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
    v___x_2616_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2616_, 0, v___x_2615_);
    return v___x_2616_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(
    mut v_mvarId_2617_: *mut leanh::LeanObject,
    mut v___f_2618_: *mut leanh::LeanObject,
    mut v___y_2619_: *mut leanh::LeanObject,
    mut v___y_2620_: *mut leanh::LeanObject,
    mut v___y_2621_: *mut leanh::LeanObject,
    mut v___y_2622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: u8 = 0;
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2644_: u8 = 0;
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_a_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut v_a_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2660_: u8 = 0;
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_2617_);
                v___x_2624_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_2617_,
                    v___y_2619_,
                    v___y_2620_,
                    v___y_2621_,
                    v___y_2622_,
                );
                if leanh::lean_obj_tag(v___x_2624_) == 0 {
                    v_a_2625_ = leanh::lean_ctor_get(v___x_2624_, 0);
                    leanh::lean_inc(v_a_2625_);
                    leanh::lean_dec_ref_known(v___x_2624_, 1);
                    v___x_2626_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1;
                    v___x_2627_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2628_ = l_Lean_Expr_isAppOfArity(v_a_2625_, v___x_2626_, v___x_2627_);
                    if v___x_2628_ == 0 {
                        leanh::lean_dec(v_a_2625_);
                        leanh::lean_dec_ref(v___f_2618_);
                        v___x_2629_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3;
                        v___x_2630_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
                        v___x_2631_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_2629_,
                            v_mvarId_2617_,
                            v___x_2630_,
                            v___y_2619_,
                            v___y_2620_,
                            v___y_2621_,
                            v___y_2622_,
                        );
                        return v___x_2631_;
                    } else {
                        v___x_2632_ = l_Lean_Expr_appFn_x21(v_a_2625_);
                        v___x_2633_ = l_Lean_Expr_appArg_x21(v___x_2632_);
                        leanh::lean_dec_ref(v___x_2632_);
                        v___x_2634_ = 0;
                        v___x_2635_ = l_Lean_Meta_deltaExpand(
                            v___x_2633_,
                            v___f_2618_,
                            v___x_2634_,
                            v___y_2621_,
                            v___y_2622_,
                        );
                        if leanh::lean_obj_tag(v___x_2635_) == 0 {
                            v_a_2636_ = leanh::lean_ctor_get(v___x_2635_, 0);
                            leanh::lean_inc(v_a_2636_);
                            leanh::lean_dec_ref_known(v___x_2635_, 1);
                            v___x_2637_ = l_Lean_Expr_appArg_x21(v_a_2625_);
                            leanh::lean_dec(v_a_2625_);
                            v___x_2638_ = l_Lean_Meta_mkEq(
                                v_a_2636_,
                                v___x_2637_,
                                v___y_2619_,
                                v___y_2620_,
                                v___y_2621_,
                                v___y_2622_,
                            );
                            if leanh::lean_obj_tag(v___x_2638_) == 0 {
                                v_a_2639_ = leanh::lean_ctor_get(v___x_2638_, 0);
                                leanh::lean_inc(v_a_2639_);
                                leanh::lean_dec_ref_known(v___x_2638_, 1);
                                v___x_2640_ = l_Lean_MVarId_replaceTargetDefEq(
                                    v_mvarId_2617_,
                                    v_a_2639_,
                                    v___y_2619_,
                                    v___y_2620_,
                                    v___y_2621_,
                                    v___y_2622_,
                                );
                                return v___x_2640_;
                            } else {
                                leanh::lean_dec(v_mvarId_2617_);
                                v_a_2641_ = leanh::lean_ctor_get(v___x_2638_, 0);
                                v_isSharedCheck_2648_ =
                                    (!leanh::lean_is_exclusive(v___x_2638_)) as u8;
                                if v_isSharedCheck_2648_ == 0 {
                                    v___x_2643_ = v___x_2638_;
                                    v_isShared_2644_ = v_isSharedCheck_2648_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2641_);
                                    leanh::lean_dec(v___x_2638_);
                                    v___x_2643_ = leanh::lean_box(0);
                                    v_isShared_2644_ = v_isSharedCheck_2648_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2625_);
                            leanh::lean_dec(v_mvarId_2617_);
                            v_a_2649_ = leanh::lean_ctor_get(v___x_2635_, 0);
                            v_isSharedCheck_2656_ =
                                (!leanh::lean_is_exclusive(v___x_2635_)) as u8;
                            if v_isSharedCheck_2656_ == 0 {
                                v___x_2651_ = v___x_2635_;
                                v_isShared_2652_ = v_isSharedCheck_2656_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2649_);
                                leanh::lean_dec(v___x_2635_);
                                v___x_2651_ = leanh::lean_box(0);
                                v_isShared_2652_ = v_isSharedCheck_2656_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___f_2618_);
                    leanh::lean_dec(v_mvarId_2617_);
                    v_a_2657_ = leanh::lean_ctor_get(v___x_2624_, 0);
                    v_isSharedCheck_2664_ = (!leanh::lean_is_exclusive(v___x_2624_)) as u8;
                    if v_isSharedCheck_2664_ == 0 {
                        v___x_2659_ = v___x_2624_;
                        v_isShared_2660_ = v_isSharedCheck_2664_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2657_);
                        leanh::lean_dec(v___x_2624_);
                        v___x_2659_ = leanh::lean_box(0);
                        v_isShared_2660_ = v_isSharedCheck_2664_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2644_ == 0 {
                    v___x_2646_ = v___x_2643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2647_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
                    v___x_2646_ = v_reuseFailAlloc_2647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2646_;
            }
            3 => {
                if v_isShared_2652_ == 0 {
                    v___x_2654_ = v___x_2651_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
                    v___x_2654_ = v_reuseFailAlloc_2655_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2654_;
            }
            5 => {
                if v_isShared_2660_ == 0 {
                    v___x_2662_ = v___x_2659_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2663_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
                    v___x_2662_ = v_reuseFailAlloc_2663_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed(
    mut v_mvarId_2665_: *mut leanh::LeanObject,
    mut v___f_2666_: *mut leanh::LeanObject,
    mut v___y_2667_: *mut leanh::LeanObject,
    mut v___y_2668_: *mut leanh::LeanObject,
    mut v___y_2669_: *mut leanh::LeanObject,
    mut v___y_2670_: *mut leanh::LeanObject,
    mut v___y_2671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_2665_, v___f_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
    leanh::lean_dec(v___y_2670_);
    leanh::lean_dec_ref(v___y_2669_);
    leanh::lean_dec(v___y_2668_);
    leanh::lean_dec_ref(v___y_2667_);
    return v_res_2672_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(
    mut v_declName_2673_: *mut leanh::LeanObject,
    mut v_declNameNonRec_2674_: *mut leanh::LeanObject,
    mut v_mvarId_2675_: *mut leanh::LeanObject,
    mut v_a_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
    mut v_a_2678_: *mut leanh::LeanObject,
    mut v_a_2679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2681_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_2681_, 0, v_declName_2673_);
    leanh::lean_closure_set(v___f_2681_, 1, v_declNameNonRec_2674_);
    leanh::lean_inc(v_mvarId_2675_);
    v___f_2682_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed as *mut core::ffi::c_void, 7, 2);
    leanh::lean_closure_set(v___f_2682_, 0, v_mvarId_2675_);
    leanh::lean_closure_set(v___f_2682_, 1, v___f_2681_);
    v___x_2683_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2675_, v___f_2682_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
    return v___x_2683_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(
    mut v_declName_2684_: *mut leanh::LeanObject,
    mut v_declNameNonRec_2685_: *mut leanh::LeanObject,
    mut v_mvarId_2686_: *mut leanh::LeanObject,
    mut v_a_2687_: *mut leanh::LeanObject,
    mut v_a_2688_: *mut leanh::LeanObject,
    mut v_a_2689_: *mut leanh::LeanObject,
    mut v_a_2690_: *mut leanh::LeanObject,
    mut v_a_2691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2692_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2684_, v_declNameNonRec_2685_, v_mvarId_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
    leanh::lean_dec(v_a_2690_);
    leanh::lean_dec_ref(v_a_2689_);
    leanh::lean_dec(v_a_2688_);
    leanh::lean_dec_ref(v_a_2687_);
    return v_res_2692_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(
    mut v_msg_2693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2694_ = l_Lean_instInhabitedExpr;
    v___x_2695_ = lean_panic_fn_borrowed(v___x_2694_, v_msg_2693_);
    return v___x_2695_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(
    mut v_msgData_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
    mut v___y_2698_: *mut leanh::LeanObject,
    mut v___y_2699_: *mut leanh::LeanObject,
    mut v___y_2700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ = lean_st_ref_get(v___y_2700_);
    v_env_2703_ = leanh::lean_ctor_get(v___x_2702_, 0);
    leanh::lean_inc_ref(v_env_2703_);
    leanh::lean_dec(v___x_2702_);
    v___x_2704_ = lean_st_ref_get(v___y_2698_);
    v_mctx_2705_ = leanh::lean_ctor_get(v___x_2704_, 0);
    leanh::lean_inc_ref(v_mctx_2705_);
    leanh::lean_dec(v___x_2704_);
    v_lctx_2706_ = leanh::lean_ctor_get(v___y_2697_, 2);
    v_options_2707_ = leanh::lean_ctor_get(v___y_2699_, 2);
    leanh::lean_inc_ref(v_options_2707_);
    leanh::lean_inc_ref(v_lctx_2706_);
    v___x_2708_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2708_, 0, v_env_2703_);
    leanh::lean_ctor_set(v___x_2708_, 1, v_mctx_2705_);
    leanh::lean_ctor_set(v___x_2708_, 2, v_lctx_2706_);
    leanh::lean_ctor_set(v___x_2708_, 3, v_options_2707_);
    v___x_2709_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2709_, 0, v___x_2708_);
    leanh::lean_ctor_set(v___x_2709_, 1, v_msgData_2696_);
    v___x_2710_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2710_, 0, v___x_2709_);
    return v___x_2710_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0___boxed(
    mut v_msgData_2711_: *mut leanh::LeanObject,
    mut v___y_2712_: *mut leanh::LeanObject,
    mut v___y_2713_: *mut leanh::LeanObject,
    mut v___y_2714_: *mut leanh::LeanObject,
    mut v___y_2715_: *mut leanh::LeanObject,
    mut v___y_2716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2717_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msgData_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
    leanh::lean_dec(v___y_2715_);
    leanh::lean_dec_ref(v___y_2714_);
    leanh::lean_dec(v___y_2713_);
    leanh::lean_dec_ref(v___y_2712_);
    return v_res_2717_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(
    mut v_msg_2718_: *mut leanh::LeanObject,
    mut v___y_2719_: *mut leanh::LeanObject,
    mut v___y_2720_: *mut leanh::LeanObject,
    mut v___y_2721_: *mut leanh::LeanObject,
    mut v___y_2722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2729_: u8 = 0;
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2724_ = leanh::lean_ctor_get(v___y_2721_, 5);
                v___x_2725_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
                v_a_2726_ = leanh::lean_ctor_get(v___x_2725_, 0);
                v_isSharedCheck_2734_ = (!leanh::lean_is_exclusive(v___x_2725_)) as u8;
                if v_isSharedCheck_2734_ == 0 {
                    v___x_2728_ = v___x_2725_;
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2726_);
                    leanh::lean_dec(v___x_2725_);
                    v___x_2728_ = leanh::lean_box(0);
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2724_);
                v___x_2730_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2730_, 0, v_ref_2724_);
                leanh::lean_ctor_set(v___x_2730_, 1, v_a_2726_);
                if v_isShared_2729_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2728_, 1);
                    leanh::lean_ctor_set(v___x_2728_, 0, v___x_2730_);
                    v___x_2732_ = v___x_2728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2730_);
                    v___x_2732_ = v_reuseFailAlloc_2733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg___boxed(
    mut v_msg_2735_: *mut leanh::LeanObject,
    mut v___y_2736_: *mut leanh::LeanObject,
    mut v___y_2737_: *mut leanh::LeanObject,
    mut v___y_2738_: *mut leanh::LeanObject,
    mut v___y_2739_: *mut leanh::LeanObject,
    mut v___y_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2741_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
    leanh::lean_dec(v___y_2739_);
    leanh::lean_dec_ref(v___y_2738_);
    leanh::lean_dec(v___y_2737_);
    leanh::lean_dec_ref(v___y_2736_);
    return v_res_2741_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5;
    v___x_2755_ = l_Lean_stringToMessageData(v___x_2754_);
    return v___x_2755_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2762_ = leanh::lean_unsigned_to_nat(0);
    v___x_2763_ = l_Lean_Expr_bvar___override(v___x_2762_);
    return v___x_2763_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12()
-> usize {
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: usize = 0;
    v___x_2764_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
    v___x_2765_ = lean_ptr_addr(v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2769_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
    v___x_2770_ = leanh::lean_unsigned_to_nat(18);
    v___x_2771_ = leanh::lean_unsigned_to_nat(1888);
    v___x_2772_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
    v___x_2773_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
    v___x_2774_ = l_mkPanicMessageWithDecl(
        v___x_2773_,
        v___x_2772_,
        v___x_2771_,
        v___x_2770_,
        v___x_2769_,
    );
    return v___x_2774_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2783_ = leanh::lean_box(0);
    v_dummy_2784_ = l_Lean_Expr_sort___override(v___x_2783_);
    return v_dummy_2784_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(
    mut v_lhs_2790_: *mut leanh::LeanObject,
    mut v_a_2791_: *mut leanh::LeanObject,
    mut v_a_2792_: *mut leanh::LeanObject,
    mut v_a_2793_: *mut leanh::LeanObject,
    mut v_a_2794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: u8 = 0;
    let mut v___x_2802_: u8 = 0;
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: u8 = 0;
    let mut v___y_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: usize = 0;
    let mut v___x_2828_: usize = 0;
    let mut v___x_2829_: u8 = 0;
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2796_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
                v___x_2797_ = leanh::lean_unsigned_to_nat(4);
                v___x_2798_ = l_Lean_Expr_isAppOfArity(v_lhs_2790_, v___x_2796_, v___x_2797_);
                if v___x_2798_ == 0 {
                    v___x_2799_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
                    v___x_2800_ = l_Lean_Expr_isAppOfArity(v_lhs_2790_, v___x_2799_, v___x_2797_);
                    if v___x_2800_ == 0 {
                        v___x_2801_ = l_Lean_Expr_isApp(v_lhs_2790_);
                        if v___x_2801_ == 0 {
                            v___x_2802_ = l_Lean_Expr_isProj(v_lhs_2790_);
                            if v___x_2802_ == 0 {
                                v___x_2803_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
                                v___x_2804_ = l_Lean_MessageData_ofExpr(v_lhs_2790_);
                                v___x_2805_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2805_, 0, v___x_2803_);
                                leanh::lean_ctor_set(v___x_2805_, 1, v___x_2804_);
                                v___x_2806_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_2805_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
                                return v___x_2806_;
                            } else {
                                v___x_2807_ = l_Lean_Expr_projExpr_x21(v_lhs_2790_);
                                leanh::lean_inc(v_a_2794_);
                                leanh::lean_inc_ref(v_a_2793_);
                                leanh::lean_inc(v_a_2792_);
                                leanh::lean_inc_ref(v_a_2791_);
                                leanh::lean_inc_ref(v___x_2807_);
                                v___x_2808_ = lean_infer_type(
                                    v___x_2807_,
                                    v_a_2791_,
                                    v_a_2792_,
                                    v_a_2793_,
                                    v_a_2794_,
                                );
                                if leanh::lean_obj_tag(v___x_2808_) == 0 {
                                    v_a_2809_ = leanh::lean_ctor_get(v___x_2808_, 0);
                                    leanh::lean_inc(v_a_2809_);
                                    leanh::lean_dec_ref_known(v___x_2808_, 1);
                                    v___x_2810_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_2807_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
                                    if leanh::lean_obj_tag(v___x_2810_) == 0 {
                                        v_a_2811_ = leanh::lean_ctor_get(v___x_2810_, 0);
                                        leanh::lean_inc(v_a_2811_);
                                        leanh::lean_dec_ref_known(v___x_2810_, 1);
                                        v___x_2812_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
                                        v___x_2813_ = 0;
                                        if leanh::lean_obj_tag(v_lhs_2790_) == 11 {
                                            v_typeName_2823_ =
                                                leanh::lean_ctor_get(v_lhs_2790_, 0);
                                            v_idx_2824_ =
                                                leanh::lean_ctor_get(v_lhs_2790_, 1);
                                            v_struct_2825_ =
                                                leanh::lean_ctor_get(v_lhs_2790_, 2);
                                            v___x_2826_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
                                            v___x_2827_ = lean_ptr_addr(v_struct_2825_);
                                            v___x_2828_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12);
                                            v___x_2829_ =
                                                lean_usize_dec_eq(v___x_2827_, v___x_2828_);
                                            if v___x_2829_ == 0 {
                                                leanh::lean_inc(v_idx_2824_);
                                                leanh::lean_inc(v_typeName_2823_);
                                                leanh::lean_dec_ref_known(v_lhs_2790_, 3);
                                                v___x_2830_ = l_Lean_Expr_proj___override(
                                                    v_typeName_2823_,
                                                    v_idx_2824_,
                                                    v___x_2826_,
                                                );
                                                v___y_2815_ = v___x_2830_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___y_2815_ = v_lhs_2790_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_lhs_2790_);
                                            v___x_2831_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16);
                                            v___x_2832_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(v___x_2831_);
                                            v___y_2815_ = v___x_2832_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_2809_);
                                        leanh::lean_dec_ref(v_lhs_2790_);
                                        return v___x_2810_;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_2807_);
                                    leanh::lean_dec_ref(v_lhs_2790_);
                                    return v___x_2808_;
                                }
                            }
                        } else {
                            v___x_2833_ = l_Lean_Expr_appFn_x21(v_lhs_2790_);
                            v___x_2834_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_2833_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
                            if leanh::lean_obj_tag(v___x_2834_) == 0 {
                                v_a_2835_ = leanh::lean_ctor_get(v___x_2834_, 0);
                                leanh::lean_inc(v_a_2835_);
                                leanh::lean_dec_ref_known(v___x_2834_, 1);
                                v___x_2836_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
                                v___x_2837_ = l_Lean_Expr_appArg_x21(v_lhs_2790_);
                                leanh::lean_dec_ref(v_lhs_2790_);
                                v___x_2838_ = leanh::lean_unsigned_to_nat(2);
                                v___x_2839_ = lean_mk_empty_array_with_capacity(v___x_2838_);
                                v___x_2840_ = lean_array_push(v___x_2839_, v_a_2835_);
                                v___x_2841_ = lean_array_push(v___x_2840_, v___x_2837_);
                                v___x_2842_ = l_Lean_Meta_mkAppM(
                                    v___x_2836_,
                                    v___x_2841_,
                                    v_a_2791_,
                                    v_a_2792_,
                                    v_a_2793_,
                                    v_a_2794_,
                                );
                                return v___x_2842_;
                            } else {
                                leanh::lean_dec_ref(v_lhs_2790_);
                                return v___x_2834_;
                            }
                        }
                    } else {
                        v___x_2843_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
                        v___x_2844_ = l_Lean_Expr_getAppFn(v_lhs_2790_);
                        v___x_2845_ = l_Lean_Expr_constLevels_x21(v___x_2844_);
                        leanh::lean_dec_ref(v___x_2844_);
                        v___x_2846_ = l_Lean_mkConst(v___x_2843_, v___x_2845_);
                        v_dummy_2847_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
                        v_nargs_2848_ = l_Lean_Expr_getAppNumArgs(v_lhs_2790_);
                        leanh::lean_inc(v_nargs_2848_);
                        v___x_2849_ = lean_mk_array(v_nargs_2848_, v_dummy_2847_);
                        v___x_2850_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2851_ = lean_nat_sub(v_nargs_2848_, v___x_2850_);
                        leanh::lean_dec(v_nargs_2848_);
                        v___x_2852_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v_lhs_2790_,
                            v___x_2849_,
                            v___x_2851_,
                        );
                        v___x_2853_ = l_Lean_mkAppN(v___x_2846_, v___x_2852_);
                        leanh::lean_dec_ref(v___x_2852_);
                        v___x_2854_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2854_, 0, v___x_2853_);
                        return v___x_2854_;
                    }
                } else {
                    v___x_2855_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23;
                    v___x_2856_ = l_Lean_Expr_getAppFn(v_lhs_2790_);
                    v___x_2857_ = l_Lean_Expr_constLevels_x21(v___x_2856_);
                    leanh::lean_dec_ref(v___x_2856_);
                    v___x_2858_ = l_Lean_mkConst(v___x_2855_, v___x_2857_);
                    v_dummy_2859_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
                    v_nargs_2860_ = l_Lean_Expr_getAppNumArgs(v_lhs_2790_);
                    leanh::lean_inc(v_nargs_2860_);
                    v___x_2861_ = lean_mk_array(v_nargs_2860_, v_dummy_2859_);
                    v___x_2862_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2863_ = lean_nat_sub(v_nargs_2860_, v___x_2862_);
                    leanh::lean_dec(v_nargs_2860_);
                    v___x_2864_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_lhs_2790_,
                        v___x_2861_,
                        v___x_2863_,
                    );
                    v___x_2865_ = l_Lean_mkAppN(v___x_2858_, v___x_2864_);
                    leanh::lean_dec_ref(v___x_2864_);
                    v___x_2866_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2866_, 0, v___x_2865_);
                    return v___x_2866_;
                }
            }
            1 => {
                v___x_2816_ = l_Lean_mkLambda(v___x_2812_, v___x_2813_, v_a_2809_, v___y_2815_);
                v___x_2817_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
                v___x_2818_ = leanh::lean_unsigned_to_nat(2);
                v___x_2819_ = lean_mk_empty_array_with_capacity(v___x_2818_);
                v___x_2820_ = lean_array_push(v___x_2819_, v___x_2816_);
                v___x_2821_ = lean_array_push(v___x_2820_, v_a_2811_);
                v___x_2822_ = l_Lean_Meta_mkAppM(
                    v___x_2817_,
                    v___x_2821_,
                    v_a_2791_,
                    v_a_2792_,
                    v_a_2793_,
                    v_a_2794_,
                );
                return v___x_2822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___boxed(
    mut v_lhs_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_a_2869_: *mut leanh::LeanObject,
    mut v_a_2870_: *mut leanh::LeanObject,
    mut v_a_2871_: *mut leanh::LeanObject,
    mut v_a_2872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2873_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
    leanh::lean_dec(v_a_2871_);
    leanh::lean_dec_ref(v_a_2870_);
    leanh::lean_dec(v_a_2869_);
    leanh::lean_dec_ref(v_a_2868_);
    return v_res_2873_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(
    mut v_00_u03b1_2874_: *mut leanh::LeanObject,
    mut v_msg_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
    mut v___y_2877_: *mut leanh::LeanObject,
    mut v___y_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2881_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
    return v___x_2881_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___boxed(
    mut v_00_u03b1_2882_: *mut leanh::LeanObject,
    mut v_msg_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
    mut v___y_2888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v_00_u03b1_2882_, v_msg_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    leanh::lean_dec(v___y_2887_);
    leanh::lean_dec_ref(v___y_2886_);
    leanh::lean_dec(v___y_2885_);
    leanh::lean_dec_ref(v___y_2884_);
    return v_res_2889_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(
    mut v_msg_2891_: *mut leanh::LeanObject,
    mut v___y_2892_: *mut leanh::LeanObject,
    mut v___y_2893_: *mut leanh::LeanObject,
    mut v___y_2894_: *mut leanh::LeanObject,
    mut v___y_2895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534__overap_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2897_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0;
    v___x_1534__overap_2898_ = lean_panic_fn_borrowed(v___f_2897_, v_msg_2891_);
    leanh::lean_inc(v___y_2895_);
    leanh::lean_inc_ref(v___y_2894_);
    leanh::lean_inc(v___y_2893_);
    leanh::lean_inc_ref(v___y_2892_);
    v___x_2899_ = leanh::lean_apply_5(
        v___x_1534__overap_2898_,
        v___y_2892_,
        v___y_2893_,
        v___y_2894_,
        v___y_2895_,
        leanh::lean_box(0),
    );
    return v___x_2899_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(
    mut v_msg_2900_: *mut leanh::LeanObject,
    mut v___y_2901_: *mut leanh::LeanObject,
    mut v___y_2902_: *mut leanh::LeanObject,
    mut v___y_2903_: *mut leanh::LeanObject,
    mut v___y_2904_: *mut leanh::LeanObject,
    mut v___y_2905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2906_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
    leanh::lean_dec(v___y_2904_);
    leanh::lean_dec_ref(v___y_2903_);
    leanh::lean_dec(v___y_2902_);
    leanh::lean_dec_ref(v___y_2901_);
    return v_res_2906_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_2907_: *mut leanh::LeanObject,
    mut v_x_2908_: *mut leanh::LeanObject,
    mut v_x_2909_: *mut leanh::LeanObject,
    mut v_x_2910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2911_ = leanh::lean_ctor_get(v_x_2907_, 0);
                v_vs_2912_ = leanh::lean_ctor_get(v_x_2907_, 1);
                v_isSharedCheck_2936_ = (!leanh::lean_is_exclusive(v_x_2907_)) as u8;
                if v_isSharedCheck_2936_ == 0 {
                    v___x_2914_ = v_x_2907_;
                    v_isShared_2915_ = v_isSharedCheck_2936_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2912_);
                    leanh::lean_inc(v_ks_2911_);
                    leanh::lean_dec(v_x_2907_);
                    v___x_2914_ = leanh::lean_box(0);
                    v_isShared_2915_ = v_isSharedCheck_2936_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2916_ = lean_array_get_size(v_ks_2911_);
                v___x_2917_ = lean_nat_dec_lt(v_x_2908_, v___x_2916_);
                if v___x_2917_ == 0 {
                    leanh::lean_dec(v_x_2908_);
                    v___x_2918_ = lean_array_push(v_ks_2911_, v_x_2909_);
                    v___x_2919_ = lean_array_push(v_vs_2912_, v_x_2910_);
                    if v_isShared_2915_ == 0 {
                        leanh::lean_ctor_set(v___x_2914_, 1, v___x_2919_);
                        leanh::lean_ctor_set(v___x_2914_, 0, v___x_2918_);
                        v___x_2921_ = v___x_2914_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2922_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2918_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2922_, 1, v___x_2919_);
                        v___x_2921_ = v_reuseFailAlloc_2922_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2923_ = lean_array_fget_borrowed(v_ks_2911_, v_x_2908_);
                    v___x_2924_ = l_Lean_instBEqMVarId_beq(v_x_2909_, v_k_x27_2923_);
                    if v___x_2924_ == 0 {
                        if v_isShared_2915_ == 0 {
                            v___x_2926_ = v___x_2914_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2930_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_ks_2911_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_vs_2912_);
                            v___x_2926_ = v_reuseFailAlloc_2930_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2931_ = lean_array_fset(v_ks_2911_, v_x_2908_, v_x_2909_);
                        v___x_2932_ = lean_array_fset(v_vs_2912_, v_x_2908_, v_x_2910_);
                        leanh::lean_dec(v_x_2908_);
                        if v_isShared_2915_ == 0 {
                            leanh::lean_ctor_set(v___x_2914_, 1, v___x_2932_);
                            leanh::lean_ctor_set(v___x_2914_, 0, v___x_2931_);
                            v___x_2934_ = v___x_2914_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2935_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2931_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2935_, 1, v___x_2932_);
                            v___x_2934_ = v_reuseFailAlloc_2935_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2921_;
            }
            3 => {
                v___x_2927_ = leanh::lean_unsigned_to_nat(1);
                v___x_2928_ = lean_nat_add(v_x_2908_, v___x_2927_);
                leanh::lean_dec(v_x_2908_);
                v_x_2907_ = v___x_2926_;
                v_x_2908_ = v___x_2928_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_n_2937_: *mut leanh::LeanObject,
    mut v_k_2938_: *mut leanh::LeanObject,
    mut v_v_2939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = leanh::lean_unsigned_to_nat(0);
    v___x_2941_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_2937_, v___x_2940_, v_k_2938_, v_v_2939_);
    return v___x_2941_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_2942_: usize = 0;
    let mut v___x_2943_: usize = 0;
    let mut v___x_2944_: usize = 0;
    v___x_2942_ = 5usize;
    v___x_2943_ = 1usize;
    v___x_2944_ = lean_usize_shift_left(v___x_2943_, v___x_2942_);
    return v___x_2944_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_2945_: usize = 0;
    let mut v___x_2946_: usize = 0;
    let mut v___x_2947_: usize = 0;
    v___x_2945_ = 1usize;
    v___x_2946_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
    v___x_2947_ = lean_usize_sub(v___x_2946_, v___x_2945_);
    return v___x_2947_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2948_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2948_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(
    mut v_x_2949_: *mut leanh::LeanObject,
    mut v_x_2950_: usize,
    mut v_x_2951_: usize,
    mut v_x_2952_: *mut leanh::LeanObject,
    mut v_x_2953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: usize = 0;
    let mut v___x_2956_: usize = 0;
    let mut v___x_2957_: usize = 0;
    let mut v___x_2958_: usize = 0;
    let mut v_j_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: u8 = 0;
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v_v_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2979_: u8 = 0;
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_node_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2989_: u8 = 0;
    let mut v___x_2990_: usize = 0;
    let mut v___x_2991_: usize = 0;
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2998_: u8 = 0;
    let mut v_unused_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3004_: u8 = 0;
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3009_: u8 = 0;
    let mut v_ks_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: usize = 0;
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v_reuseFailAlloc_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2949_) == 0 {
                    v_es_2954_ = leanh::lean_ctor_get(v_x_2949_, 0);
                    v___x_2955_ = 5usize;
                    v___x_2956_ = 1usize;
                    v___x_2957_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1);
                    v___x_2958_ = lean_usize_land(v_x_2950_, v___x_2957_);
                    v_j_2959_ = lean_usize_to_nat(v___x_2958_);
                    v___x_2960_ = lean_array_get_size(v_es_2954_);
                    v___x_2961_ = lean_nat_dec_lt(v_j_2959_, v___x_2960_);
                    if v___x_2961_ == 0 {
                        leanh::lean_dec(v_j_2959_);
                        leanh::lean_dec(v_x_2953_);
                        leanh::lean_dec(v_x_2952_);
                        return v_x_2949_;
                    } else {
                        leanh::lean_inc_ref(v_es_2954_);
                        v_isSharedCheck_2998_ = (!leanh::lean_is_exclusive(v_x_2949_)) as u8;
                        if v_isSharedCheck_2998_ == 0 {
                            v_unused_2999_ = leanh::lean_ctor_get(v_x_2949_, 0);
                            leanh::lean_dec(v_unused_2999_);
                            v___x_2963_ = v_x_2949_;
                            v_isShared_2964_ = v_isSharedCheck_2998_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2949_);
                            v___x_2963_ = leanh::lean_box(0);
                            v_isShared_2964_ = v_isSharedCheck_2998_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3000_ = leanh::lean_ctor_get(v_x_2949_, 0);
                    v_vs_3001_ = leanh::lean_ctor_get(v_x_2949_, 1);
                    v_isSharedCheck_3021_ = (!leanh::lean_is_exclusive(v_x_2949_)) as u8;
                    if v_isSharedCheck_3021_ == 0 {
                        v___x_3003_ = v_x_2949_;
                        v_isShared_3004_ = v_isSharedCheck_3021_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3001_);
                        leanh::lean_inc(v_ks_3000_);
                        leanh::lean_dec(v_x_2949_);
                        v___x_3003_ = leanh::lean_box(0);
                        v_isShared_3004_ = v_isSharedCheck_3021_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2965_ = lean_array_fget(v_es_2954_, v_j_2959_);
                v___x_2966_ = leanh::lean_box(0);
                v_xs_x27_2967_ = lean_array_fset(v_es_2954_, v_j_2959_, v___x_2966_);
                match leanh::lean_obj_tag(v_v_2965_) {
                    0 => {
                        v_key_2974_ = leanh::lean_ctor_get(v_v_2965_, 0);
                        v_val_2975_ = leanh::lean_ctor_get(v_v_2965_, 1);
                        v_isSharedCheck_2985_ = (!leanh::lean_is_exclusive(v_v_2965_)) as u8;
                        if v_isSharedCheck_2985_ == 0 {
                            v___x_2977_ = v_v_2965_;
                            v_isShared_2978_ = v_isSharedCheck_2985_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2975_);
                            leanh::lean_inc(v_key_2974_);
                            leanh::lean_dec(v_v_2965_);
                            v___x_2977_ = leanh::lean_box(0);
                            v_isShared_2978_ = v_isSharedCheck_2985_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2986_ = leanh::lean_ctor_get(v_v_2965_, 0);
                        v_isSharedCheck_2996_ = (!leanh::lean_is_exclusive(v_v_2965_)) as u8;
                        if v_isSharedCheck_2996_ == 0 {
                            v___x_2988_ = v_v_2965_;
                            v_isShared_2989_ = v_isSharedCheck_2996_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2986_);
                            leanh::lean_dec(v_v_2965_);
                            v___x_2988_ = leanh::lean_box(0);
                            v_isShared_2989_ = v_isSharedCheck_2996_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2997_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2997_, 0, v_x_2952_);
                        leanh::lean_ctor_set(v___x_2997_, 1, v_x_2953_);
                        v___y_2969_ = v___x_2997_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2970_ = lean_array_fset(v_xs_x27_2967_, v_j_2959_, v___y_2969_);
                leanh::lean_dec(v_j_2959_);
                if v_isShared_2964_ == 0 {
                    leanh::lean_ctor_set(v___x_2963_, 0, v___x_2970_);
                    v___x_2972_ = v___x_2963_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
                    v___x_2972_ = v_reuseFailAlloc_2973_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2972_;
            }
            4 => {
                v___x_2979_ = l_Lean_instBEqMVarId_beq(v_x_2952_, v_key_2974_);
                if v___x_2979_ == 0 {
                    leanh::lean_del_object(v___x_2977_);
                    v___x_2980_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2974_,
                        v_val_2975_,
                        v_x_2952_,
                        v_x_2953_,
                    );
                    v___x_2981_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2981_, 0, v___x_2980_);
                    v___y_2969_ = v___x_2981_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2975_);
                    leanh::lean_dec(v_key_2974_);
                    if v_isShared_2978_ == 0 {
                        leanh::lean_ctor_set(v___x_2977_, 1, v_x_2953_);
                        leanh::lean_ctor_set(v___x_2977_, 0, v_x_2952_);
                        v___x_2983_ = v___x_2977_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_x_2952_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_x_2953_);
                        v___x_2983_ = v_reuseFailAlloc_2984_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2969_ = v___x_2983_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2990_ = lean_usize_shift_right(v_x_2950_, v___x_2955_);
                v___x_2991_ = lean_usize_add(v_x_2951_, v___x_2956_);
                v___x_2992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_node_2986_, v___x_2990_, v___x_2991_, v_x_2952_, v_x_2953_);
                if v_isShared_2989_ == 0 {
                    leanh::lean_ctor_set(v___x_2988_, 0, v___x_2992_);
                    v___x_2994_ = v___x_2988_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2995_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
                    v___x_2994_ = v_reuseFailAlloc_2995_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2969_ = v___x_2994_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3004_ == 0 {
                    v___x_3006_ = v___x_3003_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3020_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_ks_3000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_vs_3001_);
                    v___x_3006_ = v_reuseFailAlloc_3020_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3007_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v___x_3006_, v_x_2952_, v_x_2953_);
                v___x_3015_ = 7usize;
                v___x_3016_ = lean_usize_dec_le(v___x_3015_, v_x_2951_);
                if v___x_3016_ == 0 {
                    v___x_3017_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3007_);
                    v___x_3018_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3019_ = lean_nat_dec_lt(v___x_3017_, v___x_3018_);
                    leanh::lean_dec(v___x_3017_);
                    v___y_3009_ = v___x_3019_;
                    state = 10;
                    continue;
                } else {
                    v___y_3009_ = v___x_3016_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3009_ == 0 {
                    v_ks_3010_ = leanh::lean_ctor_get(v_newNode_3007_, 0);
                    leanh::lean_inc_ref(v_ks_3010_);
                    v_vs_3011_ = leanh::lean_ctor_get(v_newNode_3007_, 1);
                    leanh::lean_inc_ref(v_vs_3011_);
                    leanh::lean_dec_ref(v_newNode_3007_);
                    v___x_3012_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3013_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2);
                    v___x_3014_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_2951_, v_ks_3010_, v_vs_3011_, v___x_3012_, v___x_3013_);
                    leanh::lean_dec_ref(v_vs_3011_);
                    leanh::lean_dec_ref(v_ks_3010_);
                    return v___x_3014_;
                } else {
                    return v_newNode_3007_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_depth_3022_: usize,
    mut v_keys_3023_: *mut leanh::LeanObject,
    mut v_vals_3024_: *mut leanh::LeanObject,
    mut v_i_3025_: *mut leanh::LeanObject,
    mut v_entries_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v_k_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: u64 = 0;
    let mut v_h_3032_: usize = 0;
    let mut v___x_3033_: usize = 0;
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: usize = 0;
    let mut v___x_3036_: usize = 0;
    let mut v___x_3037_: usize = 0;
    let mut v_h_3038_: usize = 0;
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3027_ = lean_array_get_size(v_keys_3023_);
                v___x_3028_ = lean_nat_dec_lt(v_i_3025_, v___x_3027_);
                if v___x_3028_ == 0 {
                    leanh::lean_dec(v_i_3025_);
                    return v_entries_3026_;
                } else {
                    v_k_3029_ = lean_array_fget_borrowed(v_keys_3023_, v_i_3025_);
                    v_v_3030_ = lean_array_fget_borrowed(v_vals_3024_, v_i_3025_);
                    v___x_3031_ = l_Lean_instHashableMVarId_hash(v_k_3029_);
                    v_h_3032_ = lean_uint64_to_usize(v___x_3031_);
                    v___x_3033_ = 5usize;
                    v___x_3034_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3035_ = 1usize;
                    v___x_3036_ = lean_usize_sub(v_depth_3022_, v___x_3035_);
                    v___x_3037_ = lean_usize_mul(v___x_3033_, v___x_3036_);
                    v_h_3038_ = lean_usize_shift_right(v_h_3032_, v___x_3037_);
                    v___x_3039_ = lean_nat_add(v_i_3025_, v___x_3034_);
                    leanh::lean_dec(v_i_3025_);
                    leanh::lean_inc(v_v_3030_);
                    leanh::lean_inc(v_k_3029_);
                    v___x_3040_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_entries_3026_, v_h_3038_, v_depth_3022_, v_k_3029_, v_v_3030_);
                    v_i_3025_ = v___x_3039_;
                    v_entries_3026_ = v___x_3040_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_depth_3042_: *mut leanh::LeanObject,
    mut v_keys_3043_: *mut leanh::LeanObject,
    mut v_vals_3044_: *mut leanh::LeanObject,
    mut v_i_3045_: *mut leanh::LeanObject,
    mut v_entries_3046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3047_: usize = 0;
    let mut v_res_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3047_ = leanh::lean_unbox_usize(v_depth_3042_);
    leanh::lean_dec(v_depth_3042_);
    v_res_3048_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_3047_, v_keys_3043_, v_vals_3044_, v_i_3045_, v_entries_3046_);
    leanh::lean_dec_ref(v_vals_3044_);
    leanh::lean_dec_ref(v_keys_3043_);
    return v_res_3048_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_x_3049_: *mut leanh::LeanObject,
    mut v_x_3050_: *mut leanh::LeanObject,
    mut v_x_3051_: *mut leanh::LeanObject,
    mut v_x_3052_: *mut leanh::LeanObject,
    mut v_x_3053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2123__boxed_3054_: usize = 0;
    let mut v_x_2124__boxed_3055_: usize = 0;
    let mut v_res_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2123__boxed_3054_ = leanh::lean_unbox_usize(v_x_3050_);
    leanh::lean_dec(v_x_3050_);
    v_x_2124__boxed_3055_ = leanh::lean_unbox_usize(v_x_3051_);
    leanh::lean_dec(v_x_3051_);
    v_res_3056_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_3049_, v_x_2123__boxed_3054_, v_x_2124__boxed_3055_, v_x_3052_, v_x_3053_);
    return v_res_3056_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(
    mut v_x_3057_: *mut leanh::LeanObject,
    mut v_x_3058_: *mut leanh::LeanObject,
    mut v_x_3059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3060_: u64 = 0;
    let mut v___x_3061_: usize = 0;
    let mut v___x_3062_: usize = 0;
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3060_ = l_Lean_instHashableMVarId_hash(v_x_3058_);
    v___x_3061_ = lean_uint64_to_usize(v___x_3060_);
    v___x_3062_ = 1usize;
    v___x_3063_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_3057_, v___x_3061_, v___x_3062_, v_x_3058_, v_x_3059_);
    return v___x_3063_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(
    mut v_mvarId_3064_: *mut leanh::LeanObject,
    mut v_val_3065_: *mut leanh::LeanObject,
    mut v___y_3066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v_depth_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3100_: u8 = 0;
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3068_ = lean_st_ref_take(v___y_3066_);
                v_mctx_3069_ = leanh::lean_ctor_get(v___x_3068_, 0);
                v_cache_3070_ = leanh::lean_ctor_get(v___x_3068_, 1);
                v_zetaDeltaFVarIds_3071_ = leanh::lean_ctor_get(v___x_3068_, 2);
                v_postponed_3072_ = leanh::lean_ctor_get(v___x_3068_, 3);
                v_diag_3073_ = leanh::lean_ctor_get(v___x_3068_, 4);
                v_isSharedCheck_3101_ = (!leanh::lean_is_exclusive(v___x_3068_)) as u8;
                if v_isSharedCheck_3101_ == 0 {
                    v___x_3075_ = v___x_3068_;
                    v_isShared_3076_ = v_isSharedCheck_3101_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3073_);
                    leanh::lean_inc(v_postponed_3072_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3071_);
                    leanh::lean_inc(v_cache_3070_);
                    leanh::lean_inc(v_mctx_3069_);
                    leanh::lean_dec(v___x_3068_);
                    v___x_3075_ = leanh::lean_box(0);
                    v_isShared_3076_ = v_isSharedCheck_3101_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3077_ = leanh::lean_ctor_get(v_mctx_3069_, 0);
                v_levelAssignDepth_3078_ = leanh::lean_ctor_get(v_mctx_3069_, 1);
                v_lmvarCounter_3079_ = leanh::lean_ctor_get(v_mctx_3069_, 2);
                v_mvarCounter_3080_ = leanh::lean_ctor_get(v_mctx_3069_, 3);
                v_lDecls_3081_ = leanh::lean_ctor_get(v_mctx_3069_, 4);
                v_decls_3082_ = leanh::lean_ctor_get(v_mctx_3069_, 5);
                v_userNames_3083_ = leanh::lean_ctor_get(v_mctx_3069_, 6);
                v_lAssignment_3084_ = leanh::lean_ctor_get(v_mctx_3069_, 7);
                v_eAssignment_3085_ = leanh::lean_ctor_get(v_mctx_3069_, 8);
                v_dAssignment_3086_ = leanh::lean_ctor_get(v_mctx_3069_, 9);
                v_isSharedCheck_3100_ = (!leanh::lean_is_exclusive(v_mctx_3069_)) as u8;
                if v_isSharedCheck_3100_ == 0 {
                    v___x_3088_ = v_mctx_3069_;
                    v_isShared_3089_ = v_isSharedCheck_3100_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_3086_);
                    leanh::lean_inc(v_eAssignment_3085_);
                    leanh::lean_inc(v_lAssignment_3084_);
                    leanh::lean_inc(v_userNames_3083_);
                    leanh::lean_inc(v_decls_3082_);
                    leanh::lean_inc(v_lDecls_3081_);
                    leanh::lean_inc(v_mvarCounter_3080_);
                    leanh::lean_inc(v_lmvarCounter_3079_);
                    leanh::lean_inc(v_levelAssignDepth_3078_);
                    leanh::lean_inc(v_depth_3077_);
                    leanh::lean_dec(v_mctx_3069_);
                    v___x_3088_ = leanh::lean_box(0);
                    v_isShared_3089_ = v_isSharedCheck_3100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3090_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_3085_, v_mvarId_3064_, v_val_3065_);
                if v_isShared_3089_ == 0 {
                    leanh::lean_ctor_set(v___x_3088_, 8, v___x_3090_);
                    v___x_3092_ = v___x_3088_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3099_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_depth_3077_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3099_,
                        1,
                        v_levelAssignDepth_3078_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_lmvarCounter_3079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 3, v_mvarCounter_3080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 4, v_lDecls_3081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 5, v_decls_3082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 6, v_userNames_3083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 7, v_lAssignment_3084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 8, v___x_3090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 9, v_dAssignment_3086_);
                    v___x_3092_ = v_reuseFailAlloc_3099_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3076_ == 0 {
                    leanh::lean_ctor_set(v___x_3075_, 0, v___x_3092_);
                    v___x_3094_ = v___x_3075_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_cache_3070_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3098_,
                        2,
                        v_zetaDeltaFVarIds_3071_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_postponed_3072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_diag_3073_);
                    v___x_3094_ = v_reuseFailAlloc_3098_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3095_ = lean_st_ref_set(v___y_3066_, v___x_3094_);
                v___x_3096_ = leanh::lean_box(0);
                v___x_3097_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3097_, 0, v___x_3096_);
                return v___x_3097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(
    mut v_mvarId_3102_: *mut leanh::LeanObject,
    mut v_val_3103_: *mut leanh::LeanObject,
    mut v___y_3104_: *mut leanh::LeanObject,
    mut v___y_3105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3106_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_3102_, v_val_3103_, v___y_3104_);
    leanh::lean_dec(v___y_3104_);
    return v_res_3106_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3110_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2;
    v___x_3111_ = leanh::lean_unsigned_to_nat(41);
    v___x_3112_ = leanh::lean_unsigned_to_nat(70);
    v___x_3113_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1;
    v___x_3114_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0;
    v___x_3115_ = l_mkPanicMessageWithDecl(
        v___x_3114_,
        v___x_3113_,
        v___x_3112_,
        v___x_3111_,
        v___x_3110_,
    );
    return v___x_3115_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3116_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2;
    v___x_3117_ = leanh::lean_unsigned_to_nat(51);
    v___x_3118_ = leanh::lean_unsigned_to_nat(72);
    v___x_3119_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1;
    v___x_3120_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0;
    v___x_3121_ = l_mkPanicMessageWithDecl(
        v___x_3120_,
        v___x_3119_,
        v___x_3118_,
        v___x_3117_,
        v___x_3116_,
    );
    return v___x_3121_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(
    mut v_mvarId_3122_: *mut leanh::LeanObject,
    mut v___y_3123_: *mut leanh::LeanObject,
    mut v___y_3124_: *mut leanh::LeanObject,
    mut v___y_3125_: *mut leanh::LeanObject,
    mut v___y_3126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: u8 = 0;
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut v_unused_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3170_: u8 = 0;
    let mut v_a_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3178_: u8 = 0;
    let mut v_a_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3182_: u8 = 0;
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_a_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v_a_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_a_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_3122_);
                v___x_3128_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_3122_,
                    v___y_3123_,
                    v___y_3124_,
                    v___y_3125_,
                    v___y_3126_,
                );
                if leanh::lean_obj_tag(v___x_3128_) == 0 {
                    v_a_3129_ = leanh::lean_ctor_get(v___x_3128_, 0);
                    leanh::lean_inc(v_a_3129_);
                    leanh::lean_dec_ref_known(v___x_3128_, 1);
                    v___x_3130_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1;
                    v___x_3131_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3132_ = l_Lean_Expr_isAppOfArity(v_a_3129_, v___x_3130_, v___x_3131_);
                    if v___x_3132_ == 0 {
                        leanh::lean_dec(v_a_3129_);
                        leanh::lean_dec(v_mvarId_3122_);
                        v___x_3133_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
                        v___x_3134_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_3133_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
                        leanh::lean_dec(v___y_3126_);
                        leanh::lean_dec_ref(v___y_3125_);
                        leanh::lean_dec(v___y_3124_);
                        leanh::lean_dec_ref(v___y_3123_);
                        return v___x_3134_;
                    } else {
                        v___x_3135_ = l_Lean_Expr_appFn_x21(v_a_3129_);
                        v___x_3136_ = l_Lean_Expr_appArg_x21(v___x_3135_);
                        leanh::lean_dec_ref(v___x_3135_);
                        v___x_3137_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_3136_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
                        if leanh::lean_obj_tag(v___x_3137_) == 0 {
                            v_a_3138_ = leanh::lean_ctor_get(v___x_3137_, 0);
                            leanh::lean_inc_n(v_a_3138_, 2);
                            leanh::lean_dec_ref_known(v___x_3137_, 1);
                            leanh::lean_inc(v___y_3126_);
                            leanh::lean_inc_ref(v___y_3125_);
                            leanh::lean_inc(v___y_3124_);
                            leanh::lean_inc_ref(v___y_3123_);
                            v___x_3139_ = lean_infer_type(
                                v_a_3138_,
                                v___y_3123_,
                                v___y_3124_,
                                v___y_3125_,
                                v___y_3126_,
                            );
                            if leanh::lean_obj_tag(v___x_3139_) == 0 {
                                v_a_3140_ = leanh::lean_ctor_get(v___x_3139_, 0);
                                leanh::lean_inc(v_a_3140_);
                                leanh::lean_dec_ref_known(v___x_3139_, 1);
                                v___x_3141_ =
                                    l_Lean_Expr_isAppOfArity(v_a_3140_, v___x_3130_, v___x_3131_);
                                if v___x_3141_ == 0 {
                                    leanh::lean_dec(v_a_3140_);
                                    leanh::lean_dec(v_a_3138_);
                                    leanh::lean_dec(v_a_3129_);
                                    leanh::lean_dec(v_mvarId_3122_);
                                    v___x_3142_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4);
                                    v___x_3143_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_3142_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
                                    leanh::lean_dec(v___y_3126_);
                                    leanh::lean_dec_ref(v___y_3125_);
                                    leanh::lean_dec(v___y_3124_);
                                    leanh::lean_dec_ref(v___y_3123_);
                                    return v___x_3143_;
                                } else {
                                    v___x_3144_ = l_Lean_Expr_appArg_x21(v_a_3129_);
                                    leanh::lean_dec(v_a_3129_);
                                    v___x_3145_ = l_Lean_Expr_appArg_x21(v_a_3140_);
                                    leanh::lean_dec(v_a_3140_);
                                    v___x_3146_ = l_Lean_Meta_mkEq(
                                        v___x_3145_,
                                        v___x_3144_,
                                        v___y_3123_,
                                        v___y_3124_,
                                        v___y_3125_,
                                        v___y_3126_,
                                    );
                                    if leanh::lean_obj_tag(v___x_3146_) == 0 {
                                        v_a_3147_ = leanh::lean_ctor_get(v___x_3146_, 0);
                                        leanh::lean_inc(v_a_3147_);
                                        leanh::lean_dec_ref_known(v___x_3146_, 1);
                                        v___x_3148_ = leanh::lean_box(0);
                                        v___x_3149_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                            v_a_3147_,
                                            v___x_3148_,
                                            v___y_3123_,
                                            v___y_3124_,
                                            v___y_3125_,
                                            v___y_3126_,
                                        );
                                        if leanh::lean_obj_tag(v___x_3149_) == 0 {
                                            v_a_3150_ = leanh::lean_ctor_get(v___x_3149_, 0);
                                            leanh::lean_inc_n(v_a_3150_, 2);
                                            leanh::lean_dec_ref_known(v___x_3149_, 1);
                                            v___x_3151_ = l_Lean_Meta_mkEqTrans(
                                                v_a_3138_,
                                                v_a_3150_,
                                                v___y_3123_,
                                                v___y_3124_,
                                                v___y_3125_,
                                                v___y_3126_,
                                            );
                                            leanh::lean_dec(v___y_3126_);
                                            leanh::lean_dec_ref(v___y_3125_);
                                            leanh::lean_dec_ref(v___y_3123_);
                                            if leanh::lean_obj_tag(v___x_3151_) == 0 {
                                                v_a_3152_ =
                                                    leanh::lean_ctor_get(v___x_3151_, 0);
                                                leanh::lean_inc(v_a_3152_);
                                                leanh::lean_dec_ref_known(v___x_3151_, 1);
                                                v___x_3153_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_3122_, v_a_3152_, v___y_3124_);
                                                leanh::lean_dec(v___y_3124_);
                                                v_isSharedCheck_3161_ =
                                                    (!leanh::lean_is_exclusive(v___x_3153_))
                                                        as u8;
                                                if v_isSharedCheck_3161_ == 0 {
                                                    v_unused_3162_ =
                                                        leanh::lean_ctor_get(v___x_3153_, 0);
                                                    leanh::lean_dec(v_unused_3162_);
                                                    v___x_3155_ = v___x_3153_;
                                                    v_isShared_3156_ = v_isSharedCheck_3161_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    leanh::lean_dec(v___x_3153_);
                                                    v___x_3155_ = leanh::lean_box(0);
                                                    v_isShared_3156_ = v_isSharedCheck_3161_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_3150_);
                                                leanh::lean_dec(v___y_3124_);
                                                leanh::lean_dec(v_mvarId_3122_);
                                                v_a_3163_ =
                                                    leanh::lean_ctor_get(v___x_3151_, 0);
                                                v_isSharedCheck_3170_ =
                                                    (!leanh::lean_is_exclusive(v___x_3151_))
                                                        as u8;
                                                if v_isSharedCheck_3170_ == 0 {
                                                    v___x_3165_ = v___x_3151_;
                                                    v_isShared_3166_ = v_isSharedCheck_3170_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_3163_);
                                                    leanh::lean_dec(v___x_3151_);
                                                    v___x_3165_ = leanh::lean_box(0);
                                                    v_isShared_3166_ = v_isSharedCheck_3170_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_3138_);
                                            leanh::lean_dec(v___y_3126_);
                                            leanh::lean_dec_ref(v___y_3125_);
                                            leanh::lean_dec(v___y_3124_);
                                            leanh::lean_dec_ref(v___y_3123_);
                                            leanh::lean_dec(v_mvarId_3122_);
                                            v_a_3171_ = leanh::lean_ctor_get(v___x_3149_, 0);
                                            v_isSharedCheck_3178_ =
                                                (!leanh::lean_is_exclusive(v___x_3149_))
                                                    as u8;
                                            if v_isSharedCheck_3178_ == 0 {
                                                v___x_3173_ = v___x_3149_;
                                                v_isShared_3174_ = v_isSharedCheck_3178_;
                                                state = 5;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3171_);
                                                leanh::lean_dec(v___x_3149_);
                                                v___x_3173_ = leanh::lean_box(0);
                                                v_isShared_3174_ = v_isSharedCheck_3178_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_3138_);
                                        leanh::lean_dec(v___y_3126_);
                                        leanh::lean_dec_ref(v___y_3125_);
                                        leanh::lean_dec(v___y_3124_);
                                        leanh::lean_dec_ref(v___y_3123_);
                                        leanh::lean_dec(v_mvarId_3122_);
                                        v_a_3179_ = leanh::lean_ctor_get(v___x_3146_, 0);
                                        v_isSharedCheck_3186_ =
                                            (!leanh::lean_is_exclusive(v___x_3146_)) as u8;
                                        if v_isSharedCheck_3186_ == 0 {
                                            v___x_3181_ = v___x_3146_;
                                            v_isShared_3182_ = v_isSharedCheck_3186_;
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3179_);
                                            leanh::lean_dec(v___x_3146_);
                                            v___x_3181_ = leanh::lean_box(0);
                                            v_isShared_3182_ = v_isSharedCheck_3186_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_3138_);
                                leanh::lean_dec(v_a_3129_);
                                leanh::lean_dec(v___y_3126_);
                                leanh::lean_dec_ref(v___y_3125_);
                                leanh::lean_dec(v___y_3124_);
                                leanh::lean_dec_ref(v___y_3123_);
                                leanh::lean_dec(v_mvarId_3122_);
                                v_a_3187_ = leanh::lean_ctor_get(v___x_3139_, 0);
                                v_isSharedCheck_3194_ =
                                    (!leanh::lean_is_exclusive(v___x_3139_)) as u8;
                                if v_isSharedCheck_3194_ == 0 {
                                    v___x_3189_ = v___x_3139_;
                                    v_isShared_3190_ = v_isSharedCheck_3194_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3187_);
                                    leanh::lean_dec(v___x_3139_);
                                    v___x_3189_ = leanh::lean_box(0);
                                    v_isShared_3190_ = v_isSharedCheck_3194_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_3129_);
                            leanh::lean_dec(v___y_3126_);
                            leanh::lean_dec_ref(v___y_3125_);
                            leanh::lean_dec(v___y_3124_);
                            leanh::lean_dec_ref(v___y_3123_);
                            leanh::lean_dec(v_mvarId_3122_);
                            v_a_3195_ = leanh::lean_ctor_get(v___x_3137_, 0);
                            v_isSharedCheck_3202_ =
                                (!leanh::lean_is_exclusive(v___x_3137_)) as u8;
                            if v_isSharedCheck_3202_ == 0 {
                                v___x_3197_ = v___x_3137_;
                                v_isShared_3198_ = v_isSharedCheck_3202_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3195_);
                                leanh::lean_dec(v___x_3137_);
                                v___x_3197_ = leanh::lean_box(0);
                                v_isShared_3198_ = v_isSharedCheck_3202_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_3126_);
                    leanh::lean_dec_ref(v___y_3125_);
                    leanh::lean_dec(v___y_3124_);
                    leanh::lean_dec_ref(v___y_3123_);
                    leanh::lean_dec(v_mvarId_3122_);
                    v_a_3203_ = leanh::lean_ctor_get(v___x_3128_, 0);
                    v_isSharedCheck_3210_ = (!leanh::lean_is_exclusive(v___x_3128_)) as u8;
                    if v_isSharedCheck_3210_ == 0 {
                        v___x_3205_ = v___x_3128_;
                        v_isShared_3206_ = v_isSharedCheck_3210_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3203_);
                        leanh::lean_dec(v___x_3128_);
                        v___x_3205_ = leanh::lean_box(0);
                        v_isShared_3206_ = v_isSharedCheck_3210_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3157_ = l_Lean_Expr_mvarId_x21(v_a_3150_);
                leanh::lean_dec(v_a_3150_);
                if v_isShared_3156_ == 0 {
                    leanh::lean_ctor_set(v___x_3155_, 0, v___x_3157_);
                    v___x_3159_ = v___x_3155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
                    v___x_3159_ = v_reuseFailAlloc_3160_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3159_;
            }
            3 => {
                if v_isShared_3166_ == 0 {
                    v___x_3168_ = v___x_3165_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3169_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
                    v___x_3168_ = v_reuseFailAlloc_3169_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3168_;
            }
            5 => {
                if v_isShared_3174_ == 0 {
                    v___x_3176_ = v___x_3173_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3177_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
                    v___x_3176_ = v_reuseFailAlloc_3177_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3176_;
            }
            7 => {
                if v_isShared_3182_ == 0 {
                    v___x_3184_ = v___x_3181_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3185_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
                    v___x_3184_ = v_reuseFailAlloc_3185_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3184_;
            }
            9 => {
                if v_isShared_3190_ == 0 {
                    v___x_3192_ = v___x_3189_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
                    v___x_3192_ = v_reuseFailAlloc_3193_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3192_;
            }
            11 => {
                if v_isShared_3198_ == 0 {
                    v___x_3200_ = v___x_3197_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
                    v___x_3200_ = v_reuseFailAlloc_3201_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3200_;
            }
            13 => {
                if v_isShared_3206_ == 0 {
                    v___x_3208_ = v___x_3205_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
                    v___x_3208_ = v_reuseFailAlloc_3209_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed(
    mut v_mvarId_3211_: *mut leanh::LeanObject,
    mut v___y_3212_: *mut leanh::LeanObject,
    mut v___y_3213_: *mut leanh::LeanObject,
    mut v___y_3214_: *mut leanh::LeanObject,
    mut v___y_3215_: *mut leanh::LeanObject,
    mut v___y_3216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3217_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
    return v_res_3217_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(
    mut v_mvarId_3218_: *mut leanh::LeanObject,
    mut v_a_3219_: *mut leanh::LeanObject,
    mut v_a_3220_: *mut leanh::LeanObject,
    mut v_a_3221_: *mut leanh::LeanObject,
    mut v_a_3222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_3218_);
    v___f_3224_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed as *mut core::ffi::c_void, 6, 1);
    leanh::lean_closure_set(v___f_3224_, 0, v_mvarId_3218_);
    v___x_3225_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_3218_, v___f_3224_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
    return v___x_3225_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(
    mut v_mvarId_3226_: *mut leanh::LeanObject,
    mut v_a_3227_: *mut leanh::LeanObject,
    mut v_a_3228_: *mut leanh::LeanObject,
    mut v_a_3229_: *mut leanh::LeanObject,
    mut v_a_3230_: *mut leanh::LeanObject,
    mut v_a_3231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3232_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
    leanh::lean_dec(v_a_3230_);
    leanh::lean_dec_ref(v_a_3229_);
    leanh::lean_dec(v_a_3228_);
    leanh::lean_dec_ref(v_a_3227_);
    return v_res_3232_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(
    mut v_mvarId_3233_: *mut leanh::LeanObject,
    mut v_val_3234_: *mut leanh::LeanObject,
    mut v___y_3235_: *mut leanh::LeanObject,
    mut v___y_3236_: *mut leanh::LeanObject,
    mut v___y_3237_: *mut leanh::LeanObject,
    mut v___y_3238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3240_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_3233_, v_val_3234_, v___y_3236_);
    return v___x_3240_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(
    mut v_mvarId_3241_: *mut leanh::LeanObject,
    mut v_val_3242_: *mut leanh::LeanObject,
    mut v___y_3243_: *mut leanh::LeanObject,
    mut v___y_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3248_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_3241_, v_val_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
    leanh::lean_dec(v___y_3246_);
    leanh::lean_dec_ref(v___y_3245_);
    leanh::lean_dec(v___y_3244_);
    leanh::lean_dec_ref(v___y_3243_);
    return v_res_3248_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(
    mut v_00_u03b2_3249_: *mut leanh::LeanObject,
    mut v_x_3250_: *mut leanh::LeanObject,
    mut v_x_3251_: *mut leanh::LeanObject,
    mut v_x_3252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3253_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_3250_, v_x_3251_, v_x_3252_);
    return v___x_3253_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(
    mut v_00_u03b2_3254_: *mut leanh::LeanObject,
    mut v_x_3255_: *mut leanh::LeanObject,
    mut v_x_3256_: usize,
    mut v_x_3257_: usize,
    mut v_x_3258_: *mut leanh::LeanObject,
    mut v_x_3259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_3255_, v_x_3256_, v_x_3257_, v_x_3258_, v_x_3259_);
    return v___x_3260_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_3261_: *mut leanh::LeanObject,
    mut v_x_3262_: *mut leanh::LeanObject,
    mut v_x_3263_: *mut leanh::LeanObject,
    mut v_x_3264_: *mut leanh::LeanObject,
    mut v_x_3265_: *mut leanh::LeanObject,
    mut v_x_3266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2609__boxed_3267_: usize = 0;
    let mut v_x_2610__boxed_3268_: usize = 0;
    let mut v_res_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2609__boxed_3267_ = leanh::lean_unbox_usize(v_x_3263_);
    leanh::lean_dec(v_x_3263_);
    v_x_2610__boxed_3268_ = leanh::lean_unbox_usize(v_x_3264_);
    leanh::lean_dec(v_x_3264_);
    v_res_3269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_3261_, v_x_3262_, v_x_2609__boxed_3267_, v_x_2610__boxed_3268_, v_x_3265_, v_x_3266_);
    return v_res_3269_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3270_: *mut leanh::LeanObject,
    mut v_n_3271_: *mut leanh::LeanObject,
    mut v_k_3272_: *mut leanh::LeanObject,
    mut v_v_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3274_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_3271_, v_k_3272_, v_v_3273_);
    return v___x_3274_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3275_: *mut leanh::LeanObject,
    mut v_depth_3276_: usize,
    mut v_keys_3277_: *mut leanh::LeanObject,
    mut v_vals_3278_: *mut leanh::LeanObject,
    mut v_heq_3279_: *mut leanh::LeanObject,
    mut v_i_3280_: *mut leanh::LeanObject,
    mut v_entries_3281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_3276_, v_keys_3277_, v_vals_3278_, v_i_3280_, v_entries_3281_);
    return v___x_3282_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3283_: *mut leanh::LeanObject,
    mut v_depth_3284_: *mut leanh::LeanObject,
    mut v_keys_3285_: *mut leanh::LeanObject,
    mut v_vals_3286_: *mut leanh::LeanObject,
    mut v_heq_3287_: *mut leanh::LeanObject,
    mut v_i_3288_: *mut leanh::LeanObject,
    mut v_entries_3289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3290_: usize = 0;
    let mut v_res_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3290_ = leanh::lean_unbox_usize(v_depth_3284_);
    leanh::lean_dec(v_depth_3284_);
    v_res_3291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_3283_, v_depth_boxed_3290_, v_keys_3285_, v_vals_3286_, v_heq_3287_, v_i_3288_, v_entries_3289_);
    leanh::lean_dec_ref(v_vals_3286_);
    leanh::lean_dec_ref(v_keys_3285_);
    return v_res_3291_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_3292_: *mut leanh::LeanObject,
    mut v_x_3293_: *mut leanh::LeanObject,
    mut v_x_3294_: *mut leanh::LeanObject,
    mut v_x_3295_: *mut leanh::LeanObject,
    mut v_x_3296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3297_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_3293_, v_x_3294_, v_x_3295_, v_x_3296_);
    return v___x_3297_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(
    mut v_opts_3298_: *mut leanh::LeanObject,
    mut v_opt_3299_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3300_ = leanh::lean_ctor_get(v_opt_3299_, 0);
    v_defValue_3301_ = leanh::lean_ctor_get(v_opt_3299_, 1);
    v_map_3302_ = leanh::lean_ctor_get(v_opts_3298_, 0);
    v___x_3303_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3302_,
            v_name_3300_,
        );
    if leanh::lean_obj_tag(v___x_3303_) == 0 {
        let mut v___x_3304_: u8 = 0;
        v___x_3304_ = (leanh::lean_unbox(v_defValue_3301_) as u8);
        return v___x_3304_;
    } else {
        let mut v_val_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3305_ = leanh::lean_ctor_get(v___x_3303_, 0);
        leanh::lean_inc(v_val_3305_);
        leanh::lean_dec_ref_known(v___x_3303_, 1);
        if leanh::lean_obj_tag(v_val_3305_) == 1 {
            let mut v_v_3306_: u8 = 0;
            v_v_3306_ = leanh::lean_ctor_get_uint8(v_val_3305_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3305_, 0);
            return v_v_3306_;
        } else {
            let mut v___x_3307_: u8 = 0;
            leanh::lean_dec(v_val_3305_);
            v___x_3307_ = (leanh::lean_unbox(v_defValue_3301_) as u8);
            return v___x_3307_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(
    mut v_opts_3308_: *mut leanh::LeanObject,
    mut v_opt_3309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3310_: u8 = 0;
    let mut v_r_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3310_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_3308_, v_opt_3309_);
    leanh::lean_dec_ref(v_opt_3309_);
    leanh::lean_dec_ref(v_opts_3308_);
    v_r_3311_ = leanh::lean_box((v_res_3310_) as usize);
    return v_r_3311_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(
    mut v_opts_3312_: *mut leanh::LeanObject,
    mut v_opt_3313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3314_ = leanh::lean_ctor_get(v_opt_3313_, 0);
    v_defValue_3315_ = leanh::lean_ctor_get(v_opt_3313_, 1);
    v_map_3316_ = leanh::lean_ctor_get(v_opts_3312_, 0);
    v___x_3317_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3316_,
            v_name_3314_,
        );
    if leanh::lean_obj_tag(v___x_3317_) == 0 {
        leanh::lean_inc(v_defValue_3315_);
        return v_defValue_3315_;
    } else {
        let mut v_val_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3318_ = leanh::lean_ctor_get(v___x_3317_, 0);
        leanh::lean_inc(v_val_3318_);
        leanh::lean_dec_ref_known(v___x_3317_, 1);
        if leanh::lean_obj_tag(v_val_3318_) == 3 {
            let mut v_v_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_3319_ = leanh::lean_ctor_get(v_val_3318_, 0);
            leanh::lean_inc(v_v_3319_);
            leanh::lean_dec_ref_known(v_val_3318_, 1);
            return v_v_3319_;
        } else {
            leanh::lean_dec(v_val_3318_);
            leanh::lean_inc(v_defValue_3315_);
            return v_defValue_3315_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(
    mut v_opts_3320_: *mut leanh::LeanObject,
    mut v_opt_3321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3322_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_3320_, v_opt_3321_);
    leanh::lean_dec_ref(v_opt_3321_);
    leanh::lean_dec_ref(v_opts_3320_);
    return v_res_3322_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(
    mut v_e_3323_: *mut leanh::LeanObject,
    mut v___y_3324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3326_ = l_Lean_Expr_hasMVar(v_e_3323_);
                if v___x_3326_ == 0 {
                    v___x_3327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3327_, 0, v_e_3323_);
                    return v___x_3327_;
                } else {
                    v___x_3328_ = lean_st_ref_get(v___y_3324_);
                    v_mctx_3329_ = leanh::lean_ctor_get(v___x_3328_, 0);
                    leanh::lean_inc_ref(v_mctx_3329_);
                    leanh::lean_dec(v___x_3328_);
                    v___x_3330_ = l_Lean_instantiateMVarsCore(v_mctx_3329_, v_e_3323_);
                    v_fst_3331_ = leanh::lean_ctor_get(v___x_3330_, 0);
                    leanh::lean_inc(v_fst_3331_);
                    v_snd_3332_ = leanh::lean_ctor_get(v___x_3330_, 1);
                    leanh::lean_inc(v_snd_3332_);
                    leanh::lean_dec_ref(v___x_3330_);
                    v___x_3333_ = lean_st_ref_take(v___y_3324_);
                    v_cache_3334_ = leanh::lean_ctor_get(v___x_3333_, 1);
                    v_zetaDeltaFVarIds_3335_ = leanh::lean_ctor_get(v___x_3333_, 2);
                    v_postponed_3336_ = leanh::lean_ctor_get(v___x_3333_, 3);
                    v_diag_3337_ = leanh::lean_ctor_get(v___x_3333_, 4);
                    v_isSharedCheck_3346_ = (!leanh::lean_is_exclusive(v___x_3333_)) as u8;
                    if v_isSharedCheck_3346_ == 0 {
                        v_unused_3347_ = leanh::lean_ctor_get(v___x_3333_, 0);
                        leanh::lean_dec(v_unused_3347_);
                        v___x_3339_ = v___x_3333_;
                        v_isShared_3340_ = v_isSharedCheck_3346_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_3337_);
                        leanh::lean_inc(v_postponed_3336_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3335_);
                        leanh::lean_inc(v_cache_3334_);
                        leanh::lean_dec(v___x_3333_);
                        v___x_3339_ = leanh::lean_box(0);
                        v_isShared_3340_ = v_isSharedCheck_3346_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3340_ == 0 {
                    leanh::lean_ctor_set(v___x_3339_, 0, v_snd_3332_);
                    v___x_3342_ = v___x_3339_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_snd_3332_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_cache_3334_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3345_,
                        2,
                        v_zetaDeltaFVarIds_3335_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 3, v_postponed_3336_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 4, v_diag_3337_);
                    v___x_3342_ = v_reuseFailAlloc_3345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3343_ = lean_st_ref_set(v___y_3324_, v___x_3342_);
                v___x_3344_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3344_, 0, v_fst_3331_);
                return v___x_3344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(
    mut v_e_3348_: *mut leanh::LeanObject,
    mut v___y_3349_: *mut leanh::LeanObject,
    mut v___y_3350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3351_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_3348_, v___y_3349_);
    leanh::lean_dec(v___y_3349_);
    return v_res_3351_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(
    mut v_e_3352_: *mut leanh::LeanObject,
    mut v___y_3353_: *mut leanh::LeanObject,
    mut v___y_3354_: *mut leanh::LeanObject,
    mut v___y_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3358_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_3352_, v___y_3354_);
    return v___x_3358_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(
    mut v_e_3359_: *mut leanh::LeanObject,
    mut v___y_3360_: *mut leanh::LeanObject,
    mut v___y_3361_: *mut leanh::LeanObject,
    mut v___y_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3365_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_e_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
    leanh::lean_dec(v___y_3363_);
    leanh::lean_dec_ref(v___y_3362_);
    leanh::lean_dec(v___y_3361_);
    leanh::lean_dec_ref(v___y_3360_);
    return v_res_3365_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(
    mut v_k_3366_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3367_: u8,
    mut v___y_3368_: *mut leanh::LeanObject,
    mut v___y_3369_: *mut leanh::LeanObject,
    mut v___y_3370_: *mut leanh::LeanObject,
    mut v___y_3371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3377_: u8 = 0;
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_a_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3385_: u8 = 0;
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    leanh::lean_box(0),
                    v_allowLevelAssignments_3367_,
                    v_k_3366_,
                    v___y_3368_,
                    v___y_3369_,
                    v___y_3370_,
                    v___y_3371_,
                );
                if leanh::lean_obj_tag(v___x_3373_) == 0 {
                    v_a_3374_ = leanh::lean_ctor_get(v___x_3373_, 0);
                    v_isSharedCheck_3381_ = (!leanh::lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3381_ == 0 {
                        v___x_3376_ = v___x_3373_;
                        v_isShared_3377_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3374_);
                        leanh::lean_dec(v___x_3373_);
                        v___x_3376_ = leanh::lean_box(0);
                        v_isShared_3377_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3382_ = leanh::lean_ctor_get(v___x_3373_, 0);
                    v_isSharedCheck_3389_ = (!leanh::lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3389_ == 0 {
                        v___x_3384_ = v___x_3373_;
                        v_isShared_3385_ = v_isSharedCheck_3389_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3382_);
                        leanh::lean_dec(v___x_3373_);
                        v___x_3384_ = leanh::lean_box(0);
                        v_isShared_3385_ = v_isSharedCheck_3389_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3377_ == 0 {
                    v___x_3379_ = v___x_3376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
                    v___x_3379_ = v_reuseFailAlloc_3380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3379_;
            }
            3 => {
                if v_isShared_3385_ == 0 {
                    v___x_3387_ = v___x_3384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
                    v___x_3387_ = v_reuseFailAlloc_3388_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg___boxed(
    mut v_k_3390_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
    mut v___y_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_3397_: u8 = 0;
    let mut v_res_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3397_ =
        (leanh::lean_unbox(v_allowLevelAssignments_3391_) as u8);
    v_res_3398_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_3390_, v_allowLevelAssignments_boxed_3397_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
    leanh::lean_dec(v___y_3395_);
    leanh::lean_dec_ref(v___y_3394_);
    leanh::lean_dec(v___y_3393_);
    leanh::lean_dec_ref(v___y_3392_);
    return v_res_3398_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(
    mut v_00_u03b1_3399_: *mut leanh::LeanObject,
    mut v_k_3400_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3401_: u8,
    mut v___y_3402_: *mut leanh::LeanObject,
    mut v___y_3403_: *mut leanh::LeanObject,
    mut v___y_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_3400_, v_allowLevelAssignments_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
    return v___x_3407_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(
    mut v_00_u03b1_3408_: *mut leanh::LeanObject,
    mut v_k_3409_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
    mut v___y_3413_: *mut leanh::LeanObject,
    mut v___y_3414_: *mut leanh::LeanObject,
    mut v___y_3415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_3416_: u8 = 0;
    let mut v_res_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3416_ =
        (leanh::lean_unbox(v_allowLevelAssignments_3410_) as u8);
    v_res_3417_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v_00_u03b1_3408_, v_k_3409_, v_allowLevelAssignments_boxed_3416_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
    leanh::lean_dec(v___y_3414_);
    leanh::lean_dec_ref(v___y_3413_);
    leanh::lean_dec(v___y_3412_);
    leanh::lean_dec_ref(v___y_3411_);
    return v_res_3417_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(
    mut v_thm_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3427_: u8 = 0;
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3421_ = lean_st_ref_get(v___y_3419_);
                v_env_3422_ = leanh::lean_ctor_get(v___x_3421_, 0);
                leanh::lean_inc_ref_n(v_env_3422_, 2);
                leanh::lean_dec(v___x_3421_);
                v_toConstantVal_3423_ = leanh::lean_ctor_get(v_thm_3418_, 0);
                v_value_3424_ = leanh::lean_ctor_get(v_thm_3418_, 1);
                v_all_3425_ = leanh::lean_ctor_get(v_thm_3418_, 2);
                v_type_3435_ = leanh::lean_ctor_get(v_toConstantVal_3423_, 2);
                v___x_3436_ = l_Lean_Environment_hasUnsafe(v_env_3422_, v_type_3435_);
                if v___x_3436_ == 0 {
                    v___x_3437_ = l_Lean_Environment_hasUnsafe(v_env_3422_, v_value_3424_);
                    v___y_3427_ = v___x_3437_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_3422_);
                    v___y_3427_ = v___x_3436_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3427_ == 0 {
                    v___x_3428_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3428_, 0, v_thm_3418_);
                    v___x_3429_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3429_, 0, v___x_3428_);
                    return v___x_3429_;
                } else {
                    leanh::lean_inc(v_all_3425_);
                    leanh::lean_inc_ref(v_value_3424_);
                    leanh::lean_inc_ref(v_toConstantVal_3423_);
                    leanh::lean_dec_ref(v_thm_3418_);
                    v___x_3430_ = leanh::lean_box(0);
                    v___x_3431_ = 0;
                    v___x_3432_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_3432_, 0, v_toConstantVal_3423_);
                    leanh::lean_ctor_set(v___x_3432_, 1, v_value_3424_);
                    leanh::lean_ctor_set(v___x_3432_, 2, v___x_3430_);
                    leanh::lean_ctor_set(v___x_3432_, 3, v_all_3425_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3432_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_3431_,
                    );
                    v___x_3433_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3433_, 0, v___x_3432_);
                    v___x_3434_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3434_, 0, v___x_3433_);
                    return v___x_3434_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(
    mut v_thm_3438_: *mut leanh::LeanObject,
    mut v___y_3439_: *mut leanh::LeanObject,
    mut v___y_3440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3441_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_3438_, v___y_3439_);
    leanh::lean_dec(v___y_3439_);
    return v_res_3441_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(
    mut v_thm_3442_: *mut leanh::LeanObject,
    mut v___y_3443_: *mut leanh::LeanObject,
    mut v___y_3444_: *mut leanh::LeanObject,
    mut v___y_3445_: *mut leanh::LeanObject,
    mut v___y_3446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3448_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_3442_, v___y_3446_);
    return v___x_3448_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(
    mut v_thm_3449_: *mut leanh::LeanObject,
    mut v___y_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
    mut v___y_3452_: *mut leanh::LeanObject,
    mut v___y_3453_: *mut leanh::LeanObject,
    mut v___y_3454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3455_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(v_thm_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
    leanh::lean_dec(v___y_3453_);
    leanh::lean_dec_ref(v___y_3452_);
    leanh::lean_dec(v___y_3451_);
    leanh::lean_dec_ref(v___y_3450_);
    return v_res_3455_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(
    mut v_k_3456_: *mut leanh::LeanObject,
    mut v_b_3457_: *mut leanh::LeanObject,
    mut v_c_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
    mut v___y_3460_: *mut leanh::LeanObject,
    mut v___y_3461_: *mut leanh::LeanObject,
    mut v___y_3462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3462_);
    leanh::lean_inc_ref(v___y_3461_);
    leanh::lean_inc(v___y_3460_);
    leanh::lean_inc_ref(v___y_3459_);
    v___x_3464_ = leanh::lean_apply_7(
        v_k_3456_,
        v_b_3457_,
        v_c_3458_,
        v___y_3459_,
        v___y_3460_,
        v___y_3461_,
        v___y_3462_,
        leanh::lean_box(0),
    );
    return v___x_3464_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed(
    mut v_k_3465_: *mut leanh::LeanObject,
    mut v_b_3466_: *mut leanh::LeanObject,
    mut v_c_3467_: *mut leanh::LeanObject,
    mut v___y_3468_: *mut leanh::LeanObject,
    mut v___y_3469_: *mut leanh::LeanObject,
    mut v___y_3470_: *mut leanh::LeanObject,
    mut v___y_3471_: *mut leanh::LeanObject,
    mut v___y_3472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3473_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(v_k_3465_, v_b_3466_, v_c_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
    leanh::lean_dec(v___y_3471_);
    leanh::lean_dec_ref(v___y_3470_);
    leanh::lean_dec(v___y_3469_);
    leanh::lean_dec_ref(v___y_3468_);
    return v_res_3473_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(
    mut v_e_3474_: *mut leanh::LeanObject,
    mut v_k_3475_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3476_: u8,
    mut v___y_3477_: *mut leanh::LeanObject,
    mut v___y_3478_: *mut leanh::LeanObject,
    mut v___y_3479_: *mut leanh::LeanObject,
    mut v___y_3480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: u8 = 0;
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3494_: u8 = 0;
    let mut v_a_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3482_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_3482_, 0, v_k_3475_);
                v___x_3483_ = 1;
                v___x_3484_ = 0;
                v___x_3485_ = leanh::lean_box(0);
                v___x_3486_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
                    v_e_3474_,
                    v___x_3483_,
                    v___x_3484_,
                    v___x_3483_,
                    v___x_3484_,
                    v___x_3485_,
                    v___f_3482_,
                    v_cleanupAnnotations_3476_,
                    v___y_3477_,
                    v___y_3478_,
                    v___y_3479_,
                    v___y_3480_,
                );
                if leanh::lean_obj_tag(v___x_3486_) == 0 {
                    v_a_3487_ = leanh::lean_ctor_get(v___x_3486_, 0);
                    v_isSharedCheck_3494_ = (!leanh::lean_is_exclusive(v___x_3486_)) as u8;
                    if v_isSharedCheck_3494_ == 0 {
                        v___x_3489_ = v___x_3486_;
                        v_isShared_3490_ = v_isSharedCheck_3494_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3487_);
                        leanh::lean_dec(v___x_3486_);
                        v___x_3489_ = leanh::lean_box(0);
                        v_isShared_3490_ = v_isSharedCheck_3494_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3495_ = leanh::lean_ctor_get(v___x_3486_, 0);
                    v_isSharedCheck_3502_ = (!leanh::lean_is_exclusive(v___x_3486_)) as u8;
                    if v_isSharedCheck_3502_ == 0 {
                        v___x_3497_ = v___x_3486_;
                        v_isShared_3498_ = v_isSharedCheck_3502_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3495_);
                        leanh::lean_dec(v___x_3486_);
                        v___x_3497_ = leanh::lean_box(0);
                        v_isShared_3498_ = v_isSharedCheck_3502_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3490_ == 0 {
                    v___x_3492_ = v___x_3489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3493_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
                    v___x_3492_ = v_reuseFailAlloc_3493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3492_;
            }
            3 => {
                if v_isShared_3498_ == 0 {
                    v___x_3500_ = v___x_3497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
                    v___x_3500_ = v_reuseFailAlloc_3501_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___boxed(
    mut v_e_3503_: *mut leanh::LeanObject,
    mut v_k_3504_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3505_: *mut leanh::LeanObject,
    mut v___y_3506_: *mut leanh::LeanObject,
    mut v___y_3507_: *mut leanh::LeanObject,
    mut v___y_3508_: *mut leanh::LeanObject,
    mut v___y_3509_: *mut leanh::LeanObject,
    mut v___y_3510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3511_: u8 = 0;
    let mut v_res_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3511_ = (leanh::lean_unbox(v_cleanupAnnotations_3505_) as u8);
    v_res_3512_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_3503_, v_k_3504_, v_cleanupAnnotations_boxed_3511_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
    leanh::lean_dec(v___y_3509_);
    leanh::lean_dec_ref(v___y_3508_);
    leanh::lean_dec(v___y_3507_);
    leanh::lean_dec_ref(v___y_3506_);
    return v_res_3512_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(
    mut v_00_u03b1_3513_: *mut leanh::LeanObject,
    mut v_e_3514_: *mut leanh::LeanObject,
    mut v_k_3515_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3516_: u8,
    mut v___y_3517_: *mut leanh::LeanObject,
    mut v___y_3518_: *mut leanh::LeanObject,
    mut v___y_3519_: *mut leanh::LeanObject,
    mut v___y_3520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3522_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_3514_, v_k_3515_, v_cleanupAnnotations_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
    return v___x_3522_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(
    mut v_00_u03b1_3523_: *mut leanh::LeanObject,
    mut v_e_3524_: *mut leanh::LeanObject,
    mut v_k_3525_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3526_: *mut leanh::LeanObject,
    mut v___y_3527_: *mut leanh::LeanObject,
    mut v___y_3528_: *mut leanh::LeanObject,
    mut v___y_3529_: *mut leanh::LeanObject,
    mut v___y_3530_: *mut leanh::LeanObject,
    mut v___y_3531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3532_: u8 = 0;
    let mut v_res_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3532_ = (leanh::lean_unbox(v_cleanupAnnotations_3526_) as u8);
    v_res_3533_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(v_00_u03b1_3523_, v_e_3524_, v_k_3525_, v_cleanupAnnotations_boxed_3532_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
    leanh::lean_dec(v___y_3530_);
    leanh::lean_dec_ref(v___y_3529_);
    leanh::lean_dec(v___y_3528_);
    leanh::lean_dec_ref(v___y_3527_);
    return v_res_3533_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(
    mut v___x_3537_: *mut leanh::LeanObject,
    mut v___y_3538_: *mut leanh::LeanObject,
    mut v___y_3539_: *mut leanh::LeanObject,
    mut v___y_3540_: *mut leanh::LeanObject,
    mut v___y_3541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3544_: u8 = 0;
    v_options_3543_ = leanh::lean_ctor_get(v___y_3540_, 2);
    v_hasTrace_3544_ = leanh::lean_ctor_get_uint8(
        v_options_3543_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_3544_ == 0 {
        let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_3537_);
        v___x_3545_ = leanh::lean_box((v_hasTrace_3544_) as usize);
        v___x_3546_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3546_, 0, v___x_3545_);
        return v___x_3546_;
    } else {
        let mut v_inheritedTraceOptions_3547_: *mut leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3550_: u8 = 0;
        let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_3547_ = leanh::lean_ctor_get(v___y_3540_, 13);
        v___x_3548_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
        v___x_3549_ = l_Lean_Name_append(v___x_3548_, v___x_3537_);
        v___x_3550_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_3547_,
            v_options_3543_,
            v___x_3549_,
        );
        leanh::lean_dec(v___x_3549_);
        v___x_3551_ = leanh::lean_box((v___x_3550_) as usize);
        v___x_3552_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3552_, 0, v___x_3551_);
        return v___x_3552_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(
    mut v___x_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
    mut v___y_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
    leanh::lean_dec(v___y_3557_);
    leanh::lean_dec_ref(v___y_3556_);
    leanh::lean_dec(v___y_3555_);
    leanh::lean_dec_ref(v___y_3554_);
    return v_res_3559_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0()
-> f64 {
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: f64 = 0.0;
    v___x_3560_ = leanh::lean_unsigned_to_nat(0);
    v___x_3561_ = lean_float_of_nat(v___x_3560_);
    return v___x_3561_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(
    mut v_cls_3565_: *mut leanh::LeanObject,
    mut v_msg_3566_: *mut leanh::LeanObject,
    mut v___y_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3577_: u8 = 0;
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3590_: u8 = 0;
    let mut v_tid_3591_: u64 = 0;
    let mut v_traces_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3595_: u8 = 0;
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: f64 = 0.0;
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3616_: u8 = 0;
    let mut v_isSharedCheck_3617_: u8 = 0;
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3572_ = leanh::lean_ctor_get(v___y_3569_, 5);
                v___x_3573_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
                v_a_3574_ = leanh::lean_ctor_get(v___x_3573_, 0);
                v_isSharedCheck_3618_ = (!leanh::lean_is_exclusive(v___x_3573_)) as u8;
                if v_isSharedCheck_3618_ == 0 {
                    v___x_3576_ = v___x_3573_;
                    v_isShared_3577_ = v_isSharedCheck_3618_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3574_);
                    leanh::lean_dec(v___x_3573_);
                    v___x_3576_ = leanh::lean_box(0);
                    v_isShared_3577_ = v_isSharedCheck_3618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3578_ = lean_st_ref_take(v___y_3570_);
                v_traceState_3579_ = leanh::lean_ctor_get(v___x_3578_, 4);
                v_env_3580_ = leanh::lean_ctor_get(v___x_3578_, 0);
                v_nextMacroScope_3581_ = leanh::lean_ctor_get(v___x_3578_, 1);
                v_ngen_3582_ = leanh::lean_ctor_get(v___x_3578_, 2);
                v_auxDeclNGen_3583_ = leanh::lean_ctor_get(v___x_3578_, 3);
                v_cache_3584_ = leanh::lean_ctor_get(v___x_3578_, 5);
                v_messages_3585_ = leanh::lean_ctor_get(v___x_3578_, 6);
                v_infoState_3586_ = leanh::lean_ctor_get(v___x_3578_, 7);
                v_snapshotTasks_3587_ = leanh::lean_ctor_get(v___x_3578_, 8);
                v_isSharedCheck_3617_ = (!leanh::lean_is_exclusive(v___x_3578_)) as u8;
                if v_isSharedCheck_3617_ == 0 {
                    v___x_3589_ = v___x_3578_;
                    v_isShared_3590_ = v_isSharedCheck_3617_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3587_);
                    leanh::lean_inc(v_infoState_3586_);
                    leanh::lean_inc(v_messages_3585_);
                    leanh::lean_inc(v_cache_3584_);
                    leanh::lean_inc(v_traceState_3579_);
                    leanh::lean_inc(v_auxDeclNGen_3583_);
                    leanh::lean_inc(v_ngen_3582_);
                    leanh::lean_inc(v_nextMacroScope_3581_);
                    leanh::lean_inc(v_env_3580_);
                    leanh::lean_dec(v___x_3578_);
                    v___x_3589_ = leanh::lean_box(0);
                    v_isShared_3590_ = v_isSharedCheck_3617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3591_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3579_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3592_ = leanh::lean_ctor_get(v_traceState_3579_, 0);
                v_isSharedCheck_3616_ =
                    (!leanh::lean_is_exclusive(v_traceState_3579_)) as u8;
                if v_isSharedCheck_3616_ == 0 {
                    v___x_3594_ = v_traceState_3579_;
                    v_isShared_3595_ = v_isSharedCheck_3616_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3592_);
                    leanh::lean_dec(v_traceState_3579_);
                    v___x_3594_ = leanh::lean_box(0);
                    v_isShared_3595_ = v_isSharedCheck_3616_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3596_ = leanh::lean_box(0);
                v___x_3597_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0);
                v___x_3598_ = 0;
                v___x_3599_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1;
                v___x_3600_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_3600_, 0, v_cls_3565_);
                leanh::lean_ctor_set(v___x_3600_, 1, v___x_3596_);
                leanh::lean_ctor_set(v___x_3600_, 2, v___x_3599_);
                leanh::lean_ctor_set_float(
                    v___x_3600_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3597_,
                );
                leanh::lean_ctor_set_float(
                    v___x_3600_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3597_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3600_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3598_,
                );
                v___x_3601_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2;
                v___x_3602_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3602_, 0, v___x_3600_);
                leanh::lean_ctor_set(v___x_3602_, 1, v_a_3574_);
                leanh::lean_ctor_set(v___x_3602_, 2, v___x_3601_);
                leanh::lean_inc(v_ref_3572_);
                v___x_3603_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3603_, 0, v_ref_3572_);
                leanh::lean_ctor_set(v___x_3603_, 1, v___x_3602_);
                v___x_3604_ = l_Lean_PersistentArray_push___redArg(v_traces_3592_, v___x_3603_);
                if v_isShared_3595_ == 0 {
                    leanh::lean_ctor_set(v___x_3594_, 0, v___x_3604_);
                    v___x_3606_ = v___x_3594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3615_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3604_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3615_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3591_,
                    );
                    v___x_3606_ = v_reuseFailAlloc_3615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3590_ == 0 {
                    leanh::lean_ctor_set(v___x_3589_, 4, v___x_3606_);
                    v___x_3608_ = v___x_3589_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3614_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_env_3580_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_nextMacroScope_3581_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3614_, 2, v_ngen_3582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3614_, 3, v_auxDeclNGen_3583_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3614_, 4, v___x_3606_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3614_, 5, v_cache_3584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3614_, 6, v_messages_3585_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3614_, 7, v_infoState_3586_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3614_, 8, v_snapshotTasks_3587_);
                    v___x_3608_ = v_reuseFailAlloc_3614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3609_ = lean_st_ref_set(v___y_3570_, v___x_3608_);
                v___x_3610_ = leanh::lean_box(0);
                if v_isShared_3577_ == 0 {
                    leanh::lean_ctor_set(v___x_3576_, 0, v___x_3610_);
                    v___x_3612_ = v___x_3576_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
                    v___x_3612_ = v_reuseFailAlloc_3613_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___boxed(
    mut v_cls_3619_: *mut leanh::LeanObject,
    mut v_msg_3620_: *mut leanh::LeanObject,
    mut v___y_3621_: *mut leanh::LeanObject,
    mut v___y_3622_: *mut leanh::LeanObject,
    mut v___y_3623_: *mut leanh::LeanObject,
    mut v___y_3624_: *mut leanh::LeanObject,
    mut v___y_3625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3626_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v_cls_3619_, v_msg_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
    leanh::lean_dec(v___y_3624_);
    leanh::lean_dec_ref(v___y_3623_);
    leanh::lean_dec(v___y_3622_);
    leanh::lean_dec_ref(v___y_3621_);
    return v_res_3626_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(
    mut v_o_3627_: *mut leanh::LeanObject,
    mut v_k_3628_: *mut leanh::LeanObject,
    mut v_v_3629_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3631_: u8 = 0;
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3630_ = leanh::lean_ctor_get(v_o_3627_, 0);
                v_hasTrace_3631_ = leanh::lean_ctor_get_uint8(
                    v_o_3627_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3645_ = (!leanh::lean_is_exclusive(v_o_3627_)) as u8;
                if v_isSharedCheck_3645_ == 0 {
                    v___x_3633_ = v_o_3627_;
                    v_isShared_3634_ = v_isSharedCheck_3645_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_3630_);
                    leanh::lean_dec(v_o_3627_);
                    v___x_3633_ = leanh::lean_box(0);
                    v_isShared_3634_ = v_isSharedCheck_3645_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3635_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_3635_, 0 as u32, v_v_3629_);
                leanh::lean_inc(v_k_3628_);
                v___x_3636_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3628_, v___x_3635_, v_map_3630_);
                if v_hasTrace_3631_ == 0 {
                    v___x_3637_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
                    v___x_3638_ = l_Lean_Name_isPrefixOf(v___x_3637_, v_k_3628_);
                    leanh::lean_dec(v_k_3628_);
                    if v_isShared_3634_ == 0 {
                        leanh::lean_ctor_set(v___x_3633_, 0, v___x_3636_);
                        v___x_3640_ = v___x_3633_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3641_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3636_);
                        v___x_3640_ = v_reuseFailAlloc_3641_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_3628_);
                    if v_isShared_3634_ == 0 {
                        leanh::lean_ctor_set(v___x_3633_, 0, v___x_3636_);
                        v___x_3643_ = v___x_3633_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3644_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3636_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_3644_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_3631_,
                        );
                        v___x_3643_ = v_reuseFailAlloc_3644_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3640_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3638_,
                );
                return v___x_3640_;
            }
            3 => {
                return v___x_3643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(
    mut v_o_3646_: *mut leanh::LeanObject,
    mut v_k_3647_: *mut leanh::LeanObject,
    mut v_v_3648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_3649_: u8 = 0;
    let mut v_res_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_3649_ = (leanh::lean_unbox(v_v_3648_) as u8);
    v_res_3650_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_o_3646_, v_k_3647_, v_v_boxed_3649_);
    return v_res_3650_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(
    mut v_opts_3651_: *mut leanh::LeanObject,
    mut v_opt_3652_: *mut leanh::LeanObject,
    mut v_val_3653_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3654_ = leanh::lean_ctor_get(v_opt_3652_, 0);
    leanh::lean_inc(v_name_3654_);
    leanh::lean_dec_ref(v_opt_3652_);
    v___x_3655_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_opts_3651_, v_name_3654_, v_val_3653_);
    return v___x_3655_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(
    mut v_opts_3656_: *mut leanh::LeanObject,
    mut v_opt_3657_: *mut leanh::LeanObject,
    mut v_val_3658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_3659_: u8 = 0;
    let mut v_res_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_3659_ = (leanh::lean_unbox(v_val_3658_) as u8);
    v_res_3660_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_opts_3656_, v_opt_3657_, v_val_boxed_3659_);
    return v_res_3660_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3662_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0;
    v___x_3663_ = l_Lean_stringToMessageData(v___x_3662_);
    return v___x_3663_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2;
    v___x_3666_ = l_Lean_stringToMessageData(v___x_3665_);
    return v___x_3666_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3668_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4;
    v___x_3669_ = l_Lean_stringToMessageData(v___x_3668_);
    return v___x_3669_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(
    mut v_declName_3670_: *mut leanh::LeanObject,
    mut v_declNameNonRec_3671_: *mut leanh::LeanObject,
    mut v___x_3672_: *mut leanh::LeanObject,
    mut v___f_3673_: *mut leanh::LeanObject,
    mut v_a_3674_: *mut leanh::LeanObject,
    mut v___x_3675_: *mut leanh::LeanObject,
    mut v_____r_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3691_: u8 = 0;
    let mut v___y_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: u8 = 0;
    let mut v_fileName_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3705_: u8 = 0;
    let mut v_inheritedTraceOptions_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3712_: u8 = 0;
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: u8 = 0;
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___y_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: u8 = 0;
    let mut v___y_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: u8 = 0;
    let mut v___y_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3762_: u8 = 0;
    let mut v_inheritedTraceOptions_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: u8 = 0;
    let mut v___y_3774_: u8 = 0;
    let mut v___y_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: u8 = 0;
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3788_: u8 = 0;
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v_unused_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3802_: u8 = 0;
    let mut v___y_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3804_: u8 = 0;
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3807_: u8 = 0;
    let mut v_ctxApprox_3808_: u8 = 0;
    let mut v_quasiPatternApprox_3809_: u8 = 0;
    let mut v_constApprox_3810_: u8 = 0;
    let mut v_isDefEqStuckEx_3811_: u8 = 0;
    let mut v_unificationHints_3812_: u8 = 0;
    let mut v_proofIrrelevance_3813_: u8 = 0;
    let mut v_assignSyntheticOpaque_3814_: u8 = 0;
    let mut v_offsetCnstrs_3815_: u8 = 0;
    let mut v_etaStruct_3816_: u8 = 0;
    let mut v_univApprox_3817_: u8 = 0;
    let mut v_iota_3818_: u8 = 0;
    let mut v_beta_3819_: u8 = 0;
    let mut v_proj_3820_: u8 = 0;
    let mut v_zeta_3821_: u8 = 0;
    let mut v_zetaDelta_3822_: u8 = 0;
    let mut v_zetaUnused_3823_: u8 = 0;
    let mut v_zetaHave_3824_: u8 = 0;
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v_trackZetaDelta_3828_: u8 = 0;
    let mut v_zetaDeltaSet_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3835_: u8 = 0;
    let mut v_inTypeClassResolution_3836_: u8 = 0;
    let mut v_cacheInferType_3837_: u8 = 0;
    let mut v_fileName_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3850_: u8 = 0;
    let mut v_inheritedTraceOptions_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: u64 = 0;
    let mut v___x_3856_: u64 = 0;
    let mut v___x_3857_: u64 = 0;
    let mut v___x_3858_: u64 = 0;
    let mut v___x_3859_: u64 = 0;
    let mut v_key_3860_: u64 = 0;
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: u8 = 0;
    let mut v_reuseFailAlloc_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut v___y_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transparency_3878_: u8 = 0;
    let mut v___x_3879_: u8 = 0;
    let mut v___x_3880_: u8 = 0;
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: u8 = 0;
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_a_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_a_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3917_: u8 = 0;
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3932_: u8 = 0;
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_a_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3944_: u8 = 0;
    let mut v_a_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3948_: u8 = 0;
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3882_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_3670_, v_declNameNonRec_3671_, v___x_3672_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
                if leanh::lean_obj_tag(v___x_3882_) == 0 {
                    v_a_3883_ = leanh::lean_ctor_get(v___x_3882_, 0);
                    leanh::lean_inc(v_a_3883_);
                    leanh::lean_dec_ref_known(v___x_3882_, 1);
                    leanh::lean_inc_ref(v___f_3673_);
                    leanh::lean_inc(v___y_3680_);
                    leanh::lean_inc_ref(v___y_3679_);
                    leanh::lean_inc(v___y_3678_);
                    leanh::lean_inc_ref(v___y_3677_);
                    v___x_3922_ = leanh::lean_apply_5(
                        v___f_3673_,
                        v___y_3677_,
                        v___y_3678_,
                        v___y_3679_,
                        v___y_3680_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3922_) == 0 {
                        v_a_3923_ = leanh::lean_ctor_get(v___x_3922_, 0);
                        leanh::lean_inc(v_a_3923_);
                        leanh::lean_dec_ref_known(v___x_3922_, 1);
                        v___x_3924_ = (leanh::lean_unbox(v_a_3923_) as u8);
                        leanh::lean_dec(v_a_3923_);
                        if v___x_3924_ == 0 {
                            v___y_3885_ = v___y_3677_;
                            v___y_3886_ = v___y_3678_;
                            v___y_3887_ = v___y_3679_;
                            v___y_3888_ = v___y_3680_;
                            state = 14;
                            continue;
                        } else {
                            v___x_3925_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5);
                            leanh::lean_inc(v_a_3883_);
                            v___x_3926_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3926_, 0, v_a_3883_);
                            v___x_3927_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3927_, 0, v___x_3925_);
                            leanh::lean_ctor_set(v___x_3927_, 1, v___x_3926_);
                            leanh::lean_inc(v___x_3675_);
                            v___x_3928_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_3675_, v___x_3927_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
                            if leanh::lean_obj_tag(v___x_3928_) == 0 {
                                leanh::lean_dec_ref_known(v___x_3928_, 1);
                                v___y_3885_ = v___y_3677_;
                                v___y_3886_ = v___y_3678_;
                                v___y_3887_ = v___y_3679_;
                                v___y_3888_ = v___y_3680_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_3883_);
                                leanh::lean_dec(v___x_3675_);
                                leanh::lean_dec_ref(v_a_3674_);
                                leanh::lean_dec_ref(v___f_3673_);
                                v_a_3929_ = leanh::lean_ctor_get(v___x_3928_, 0);
                                v_isSharedCheck_3936_ =
                                    (!leanh::lean_is_exclusive(v___x_3928_)) as u8;
                                if v_isSharedCheck_3936_ == 0 {
                                    v___x_3931_ = v___x_3928_;
                                    v_isShared_3932_ = v_isSharedCheck_3936_;
                                    state = 21;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3929_);
                                    leanh::lean_dec(v___x_3928_);
                                    v___x_3931_ = leanh::lean_box(0);
                                    v_isShared_3932_ = v_isSharedCheck_3936_;
                                    state = 21;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3883_);
                        leanh::lean_dec(v___x_3675_);
                        leanh::lean_dec_ref(v_a_3674_);
                        leanh::lean_dec_ref(v___f_3673_);
                        v_a_3937_ = leanh::lean_ctor_get(v___x_3922_, 0);
                        v_isSharedCheck_3944_ =
                            (!leanh::lean_is_exclusive(v___x_3922_)) as u8;
                        if v_isSharedCheck_3944_ == 0 {
                            v___x_3939_ = v___x_3922_;
                            v_isShared_3940_ = v_isSharedCheck_3944_;
                            state = 23;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3937_);
                            leanh::lean_dec(v___x_3922_);
                            v___x_3939_ = leanh::lean_box(0);
                            v_isShared_3940_ = v_isSharedCheck_3944_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3675_);
                    leanh::lean_dec_ref(v_a_3674_);
                    leanh::lean_dec_ref(v___f_3673_);
                    v_a_3945_ = leanh::lean_ctor_get(v___x_3882_, 0);
                    v_isSharedCheck_3952_ = (!leanh::lean_is_exclusive(v___x_3882_)) as u8;
                    if v_isSharedCheck_3952_ == 0 {
                        v___x_3947_ = v___x_3882_;
                        v_isShared_3948_ = v_isSharedCheck_3952_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3945_);
                        leanh::lean_dec(v___x_3882_);
                        v___x_3947_ = leanh::lean_box(0);
                        v_isShared_3948_ = v_isSharedCheck_3952_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3708_ = l_Lean_maxRecDepth;
                v___x_3709_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___y_3688_, v___x_3708_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_3706_);
                leanh::lean_inc(v_cancelTk_x3f_3704_);
                leanh::lean_inc(v_currMacroScope_3703_);
                leanh::lean_inc(v_quotContext_3702_);
                leanh::lean_inc(v_maxHeartbeats_3701_);
                leanh::lean_inc(v_initHeartbeats_3700_);
                leanh::lean_inc(v_openDecls_3699_);
                leanh::lean_inc(v_currNamespace_3698_);
                leanh::lean_inc(v_ref_3697_);
                leanh::lean_inc(v_currRecDepth_3696_);
                leanh::lean_inc_ref(v_fileMap_3695_);
                leanh::lean_inc_ref(v_fileName_3694_);
                v___x_3710_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_3710_, 0, v_fileName_3694_);
                leanh::lean_ctor_set(v___x_3710_, 1, v_fileMap_3695_);
                leanh::lean_ctor_set(v___x_3710_, 2, v___y_3688_);
                leanh::lean_ctor_set(v___x_3710_, 3, v_currRecDepth_3696_);
                leanh::lean_ctor_set(v___x_3710_, 4, v___x_3709_);
                leanh::lean_ctor_set(v___x_3710_, 5, v_ref_3697_);
                leanh::lean_ctor_set(v___x_3710_, 6, v_currNamespace_3698_);
                leanh::lean_ctor_set(v___x_3710_, 7, v_openDecls_3699_);
                leanh::lean_ctor_set(v___x_3710_, 8, v_initHeartbeats_3700_);
                leanh::lean_ctor_set(v___x_3710_, 9, v_maxHeartbeats_3701_);
                leanh::lean_ctor_set(v___x_3710_, 10, v_quotContext_3702_);
                leanh::lean_ctor_set(v___x_3710_, 11, v_currMacroScope_3703_);
                leanh::lean_ctor_set(v___x_3710_, 12, v_cancelTk_x3f_3704_);
                leanh::lean_ctor_set(v___x_3710_, 13, v_inheritedTraceOptions_3706_);
                leanh::lean_ctor_set_uint8(
                    v___x_3710_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_3691_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3710_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3705_,
                );
                v___x_3711_ = l_Lean_MVarId_refl(
                    v___y_3687_,
                    v___y_3693_,
                    v___y_3686_,
                    v___y_3689_,
                    v___x_3710_,
                    v___y_3707_,
                );
                leanh::lean_dec_ref_known(v___x_3710_, 14);
                leanh::lean_dec_ref(v___y_3686_);
                if leanh::lean_obj_tag(v___x_3711_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3711_, 1);
                    v_hasTrace_3712_ = leanh::lean_ctor_get_uint8(
                        v___y_3685_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3712_ == 0 {
                        leanh::lean_dec_ref(v___y_3685_);
                        leanh::lean_dec(v___x_3675_);
                        v___x_3713_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_3674_, v___y_3689_);
                        return v___x_3713_;
                    } else {
                        v___x_3714_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
                        leanh::lean_inc(v___x_3675_);
                        v___x_3715_ = l_Lean_Name_append(v___x_3714_, v___x_3675_);
                        v___x_3716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___y_3690_,
                            v___y_3685_,
                            v___x_3715_,
                        );
                        leanh::lean_dec(v___x_3715_);
                        leanh::lean_dec_ref(v___y_3685_);
                        if v___x_3716_ == 0 {
                            leanh::lean_dec(v___x_3675_);
                            v___x_3717_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_3674_, v___y_3689_);
                            return v___x_3717_;
                        } else {
                            v___x_3718_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1);
                            v___x_3719_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_3675_, v___x_3718_, v___y_3684_, v___y_3689_, v___y_3692_, v___y_3683_);
                            if leanh::lean_obj_tag(v___x_3719_) == 0 {
                                leanh::lean_dec_ref_known(v___x_3719_, 1);
                                v___x_3720_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_3674_, v___y_3689_);
                                return v___x_3720_;
                            } else {
                                leanh::lean_dec_ref(v_a_3674_);
                                v_a_3721_ = leanh::lean_ctor_get(v___x_3719_, 0);
                                v_isSharedCheck_3728_ =
                                    (!leanh::lean_is_exclusive(v___x_3719_)) as u8;
                                if v_isSharedCheck_3728_ == 0 {
                                    v___x_3723_ = v___x_3719_;
                                    v_isShared_3724_ = v_isSharedCheck_3728_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3721_);
                                    leanh::lean_dec(v___x_3719_);
                                    v___x_3723_ = leanh::lean_box(0);
                                    v_isShared_3724_ = v_isSharedCheck_3728_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3685_);
                    leanh::lean_dec(v___x_3675_);
                    leanh::lean_dec_ref(v_a_3674_);
                    v_a_3729_ = leanh::lean_ctor_get(v___x_3711_, 0);
                    v_isSharedCheck_3736_ = (!leanh::lean_is_exclusive(v___x_3711_)) as u8;
                    if v_isSharedCheck_3736_ == 0 {
                        v___x_3731_ = v___x_3711_;
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3729_);
                        leanh::lean_dec(v___x_3711_);
                        v___x_3731_ = leanh::lean_box(0);
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3724_ == 0 {
                    v___x_3726_ = v___x_3723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
                    v___x_3726_ = v_reuseFailAlloc_3727_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3726_;
            }
            4 => {
                if v_isShared_3732_ == 0 {
                    v___x_3734_ = v___x_3731_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
                    v___x_3734_ = v_reuseFailAlloc_3735_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3734_;
            }
            6 => {
                v_fileName_3751_ = leanh::lean_ctor_get(v___y_3749_, 0);
                v_fileMap_3752_ = leanh::lean_ctor_get(v___y_3749_, 1);
                v_currRecDepth_3753_ = leanh::lean_ctor_get(v___y_3749_, 3);
                v_ref_3754_ = leanh::lean_ctor_get(v___y_3749_, 5);
                v_currNamespace_3755_ = leanh::lean_ctor_get(v___y_3749_, 6);
                v_openDecls_3756_ = leanh::lean_ctor_get(v___y_3749_, 7);
                v_initHeartbeats_3757_ = leanh::lean_ctor_get(v___y_3749_, 8);
                v_maxHeartbeats_3758_ = leanh::lean_ctor_get(v___y_3749_, 9);
                v_quotContext_3759_ = leanh::lean_ctor_get(v___y_3749_, 10);
                v_currMacroScope_3760_ = leanh::lean_ctor_get(v___y_3749_, 11);
                v_cancelTk_x3f_3761_ = leanh::lean_ctor_get(v___y_3749_, 12);
                v_suppressElabErrors_3762_ = leanh::lean_ctor_get_uint8(
                    v___y_3749_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3763_ = leanh::lean_ctor_get(v___y_3749_, 13);
                v___y_3683_ = v___y_3738_;
                v___y_3684_ = v___y_3739_;
                v___y_3685_ = v___y_3740_;
                v___y_3686_ = v___y_3741_;
                v___y_3687_ = v___y_3742_;
                v___y_3688_ = v___y_3743_;
                v___y_3689_ = v___y_3744_;
                v___y_3690_ = v___y_3745_;
                v___y_3691_ = v___y_3746_;
                v___y_3692_ = v___y_3747_;
                v___y_3693_ = v___y_3748_;
                v_fileName_3694_ = v_fileName_3751_;
                v_fileMap_3695_ = v_fileMap_3752_;
                v_currRecDepth_3696_ = v_currRecDepth_3753_;
                v_ref_3697_ = v_ref_3754_;
                v_currNamespace_3698_ = v_currNamespace_3755_;
                v_openDecls_3699_ = v_openDecls_3756_;
                v_initHeartbeats_3700_ = v_initHeartbeats_3757_;
                v_maxHeartbeats_3701_ = v_maxHeartbeats_3758_;
                v_quotContext_3702_ = v_quotContext_3759_;
                v_currMacroScope_3703_ = v_currMacroScope_3760_;
                v_cancelTk_x3f_3704_ = v_cancelTk_x3f_3761_;
                v_suppressElabErrors_3705_ = v_suppressElabErrors_3762_;
                v_inheritedTraceOptions_3706_ = v_inheritedTraceOptions_3763_;
                v___y_3707_ = v___y_3750_;
                state = 1;
                continue;
            }
            7 => {
                if v___y_3776_ == 0 {
                    v___x_3777_ = lean_st_ref_take(v___y_3765_);
                    v_env_3778_ = leanh::lean_ctor_get(v___x_3777_, 0);
                    v_nextMacroScope_3779_ = leanh::lean_ctor_get(v___x_3777_, 1);
                    v_ngen_3780_ = leanh::lean_ctor_get(v___x_3777_, 2);
                    v_auxDeclNGen_3781_ = leanh::lean_ctor_get(v___x_3777_, 3);
                    v_traceState_3782_ = leanh::lean_ctor_get(v___x_3777_, 4);
                    v_messages_3783_ = leanh::lean_ctor_get(v___x_3777_, 6);
                    v_infoState_3784_ = leanh::lean_ctor_get(v___x_3777_, 7);
                    v_snapshotTasks_3785_ = leanh::lean_ctor_get(v___x_3777_, 8);
                    v_isSharedCheck_3795_ = (!leanh::lean_is_exclusive(v___x_3777_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v_unused_3796_ = leanh::lean_ctor_get(v___x_3777_, 5);
                        leanh::lean_dec(v_unused_3796_);
                        v___x_3787_ = v___x_3777_;
                        v_isShared_3788_ = v_isSharedCheck_3795_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_3785_);
                        leanh::lean_inc(v_infoState_3784_);
                        leanh::lean_inc(v_messages_3783_);
                        leanh::lean_inc(v_traceState_3782_);
                        leanh::lean_inc(v_auxDeclNGen_3781_);
                        leanh::lean_inc(v_ngen_3780_);
                        leanh::lean_inc(v_nextMacroScope_3779_);
                        leanh::lean_inc(v_env_3778_);
                        leanh::lean_dec(v___x_3777_);
                        v___x_3787_ = leanh::lean_box(0);
                        v_isShared_3788_ = v_isSharedCheck_3795_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___y_3738_ = v___y_3765_;
                    v___y_3739_ = v___y_3766_;
                    v___y_3740_ = v___y_3770_;
                    v___y_3741_ = v___y_3769_;
                    v___y_3742_ = v___y_3768_;
                    v___y_3743_ = v___y_3767_;
                    v___y_3744_ = v___y_3771_;
                    v___y_3745_ = v___y_3772_;
                    v___y_3746_ = v___y_3773_;
                    v___y_3747_ = v___y_3775_;
                    v___y_3748_ = v___y_3774_;
                    v___y_3749_ = v___y_3775_;
                    v___y_3750_ = v___y_3765_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_3789_ = l_Lean_Kernel_enableDiag(v_env_3778_, v___y_3773_);
                v___x_3790_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once
                    ),
                    _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2,
                );
                if v_isShared_3788_ == 0 {
                    leanh::lean_ctor_set(v___x_3787_, 5, v___x_3790_);
                    leanh::lean_ctor_set(v___x_3787_, 0, v___x_3789_);
                    v___x_3792_ = v___x_3787_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_nextMacroScope_3779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_ngen_3780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 3, v_auxDeclNGen_3781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 4, v_traceState_3782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 5, v___x_3790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 6, v_messages_3783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 7, v_infoState_3784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 8, v_snapshotTasks_3785_);
                    v___x_3792_ = v_reuseFailAlloc_3794_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3793_ = lean_st_ref_set(v___y_3765_, v___x_3792_);
                v___y_3738_ = v___y_3765_;
                v___y_3739_ = v___y_3766_;
                v___y_3740_ = v___y_3770_;
                v___y_3741_ = v___y_3769_;
                v___y_3742_ = v___y_3768_;
                v___y_3743_ = v___y_3767_;
                v___y_3744_ = v___y_3771_;
                v___y_3745_ = v___y_3772_;
                v___y_3746_ = v___y_3773_;
                v___y_3747_ = v___y_3775_;
                v___y_3748_ = v___y_3774_;
                v___y_3749_ = v___y_3775_;
                v___y_3750_ = v___y_3765_;
                state = 6;
                continue;
            }
            10 => {
                v___x_3805_ = lean_st_ref_get(v___y_3798_);
                v___x_3806_ = l_Lean_Meta_Context_config(v___y_3799_);
                v_foApprox_3807_ = leanh::lean_ctor_get_uint8(v___x_3806_, 0 as u32);
                v_ctxApprox_3808_ = leanh::lean_ctor_get_uint8(v___x_3806_, 1 as u32);
                v_quasiPatternApprox_3809_ =
                    leanh::lean_ctor_get_uint8(v___x_3806_, 2 as u32);
                v_constApprox_3810_ = leanh::lean_ctor_get_uint8(v___x_3806_, 3 as u32);
                v_isDefEqStuckEx_3811_ = leanh::lean_ctor_get_uint8(v___x_3806_, 4 as u32);
                v_unificationHints_3812_ = leanh::lean_ctor_get_uint8(v___x_3806_, 5 as u32);
                v_proofIrrelevance_3813_ = leanh::lean_ctor_get_uint8(v___x_3806_, 6 as u32);
                v_assignSyntheticOpaque_3814_ =
                    leanh::lean_ctor_get_uint8(v___x_3806_, 7 as u32);
                v_offsetCnstrs_3815_ = leanh::lean_ctor_get_uint8(v___x_3806_, 8 as u32);
                v_etaStruct_3816_ = leanh::lean_ctor_get_uint8(v___x_3806_, 10 as u32);
                v_univApprox_3817_ = leanh::lean_ctor_get_uint8(v___x_3806_, 11 as u32);
                v_iota_3818_ = leanh::lean_ctor_get_uint8(v___x_3806_, 12 as u32);
                v_beta_3819_ = leanh::lean_ctor_get_uint8(v___x_3806_, 13 as u32);
                v_proj_3820_ = leanh::lean_ctor_get_uint8(v___x_3806_, 14 as u32);
                v_zeta_3821_ = leanh::lean_ctor_get_uint8(v___x_3806_, 15 as u32);
                v_zetaDelta_3822_ = leanh::lean_ctor_get_uint8(v___x_3806_, 16 as u32);
                v_zetaUnused_3823_ = leanh::lean_ctor_get_uint8(v___x_3806_, 17 as u32);
                v_zetaHave_3824_ = leanh::lean_ctor_get_uint8(v___x_3806_, 18 as u32);
                v_isSharedCheck_3870_ = (!leanh::lean_is_exclusive(v___x_3806_)) as u8;
                if v_isSharedCheck_3870_ == 0 {
                    v___x_3826_ = v___x_3806_;
                    v_isShared_3827_ = v_isSharedCheck_3870_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3806_);
                    v___x_3826_ = leanh::lean_box(0);
                    v_isShared_3827_ = v_isSharedCheck_3870_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_trackZetaDelta_3828_ = leanh::lean_ctor_get_uint8(
                    v___y_3799_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3829_ = leanh::lean_ctor_get(v___y_3799_, 1);
                v_lctx_3830_ = leanh::lean_ctor_get(v___y_3799_, 2);
                v_localInstances_3831_ = leanh::lean_ctor_get(v___y_3799_, 3);
                v_defEqCtx_x3f_3832_ = leanh::lean_ctor_get(v___y_3799_, 4);
                v_synthPendingDepth_3833_ = leanh::lean_ctor_get(v___y_3799_, 5);
                v_canUnfold_x3f_3834_ = leanh::lean_ctor_get(v___y_3799_, 6);
                v_univApprox_3835_ = leanh::lean_ctor_get_uint8(
                    v___y_3799_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3836_ = leanh::lean_ctor_get_uint8(
                    v___y_3799_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3837_ = leanh::lean_ctor_get_uint8(
                    v___y_3799_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v_fileName_3838_ = leanh::lean_ctor_get(v___y_3803_, 0);
                v_fileMap_3839_ = leanh::lean_ctor_get(v___y_3803_, 1);
                v_options_3840_ = leanh::lean_ctor_get(v___y_3803_, 2);
                v_currRecDepth_3841_ = leanh::lean_ctor_get(v___y_3803_, 3);
                v_ref_3842_ = leanh::lean_ctor_get(v___y_3803_, 5);
                v_currNamespace_3843_ = leanh::lean_ctor_get(v___y_3803_, 6);
                v_openDecls_3844_ = leanh::lean_ctor_get(v___y_3803_, 7);
                v_initHeartbeats_3845_ = leanh::lean_ctor_get(v___y_3803_, 8);
                v_maxHeartbeats_3846_ = leanh::lean_ctor_get(v___y_3803_, 9);
                v_quotContext_3847_ = leanh::lean_ctor_get(v___y_3803_, 10);
                v_currMacroScope_3848_ = leanh::lean_ctor_get(v___y_3803_, 11);
                v_cancelTk_x3f_3849_ = leanh::lean_ctor_get(v___y_3803_, 12);
                v_suppressElabErrors_3850_ = leanh::lean_ctor_get_uint8(
                    v___y_3803_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3851_ = leanh::lean_ctor_get(v___y_3803_, 13);
                v_env_3852_ = leanh::lean_ctor_get(v___x_3805_, 0);
                leanh::lean_inc_ref(v_env_3852_);
                leanh::lean_dec(v___x_3805_);
                if v_isShared_3827_ == 0 {
                    v_config_3854_ = v___x_3826_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        0 as u32,
                        v_foApprox_3807_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        1 as u32,
                        v_ctxApprox_3808_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        2 as u32,
                        v_quasiPatternApprox_3809_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        3 as u32,
                        v_constApprox_3810_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        4 as u32,
                        v_isDefEqStuckEx_3811_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        5 as u32,
                        v_unificationHints_3812_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        6 as u32,
                        v_proofIrrelevance_3813_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        7 as u32,
                        v_assignSyntheticOpaque_3814_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        8 as u32,
                        v_offsetCnstrs_3815_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        10 as u32,
                        v_etaStruct_3816_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        11 as u32,
                        v_univApprox_3817_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        12 as u32,
                        v_iota_3818_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        13 as u32,
                        v_beta_3819_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        14 as u32,
                        v_proj_3820_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        15 as u32,
                        v_zeta_3821_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        16 as u32,
                        v_zetaDelta_3822_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        17 as u32,
                        v_zetaUnused_3823_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        18 as u32,
                        v_zetaHave_3824_,
                    );
                    v_config_3854_ = v_reuseFailAlloc_3869_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                leanh::lean_ctor_set_uint8(v_config_3854_, 9 as u32, v___y_3804_);
                v___x_3855_ = l_Lean_Meta_Context_configKey(v___y_3799_);
                v___x_3856_ = 3u64;
                v___x_3857_ = lean_uint64_shift_right(v___x_3855_, v___x_3856_);
                v___x_3858_ = lean_uint64_shift_left(v___x_3857_, v___x_3856_);
                v___x_3859_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3804_);
                v_key_3860_ = lean_uint64_lor(v___x_3858_, v___x_3859_);
                v___x_3861_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_3861_, 0, v_config_3854_);
                leanh::lean_ctor_set_uint64(
                    v___x_3861_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_3860_,
                );
                leanh::lean_inc(v_canUnfold_x3f_3834_);
                leanh::lean_inc(v_synthPendingDepth_3833_);
                leanh::lean_inc(v_defEqCtx_x3f_3832_);
                leanh::lean_inc_ref(v_localInstances_3831_);
                leanh::lean_inc_ref(v_lctx_3830_);
                leanh::lean_inc(v_zetaDeltaSet_3829_);
                v___x_3862_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_3862_, 0, v___x_3861_);
                leanh::lean_ctor_set(v___x_3862_, 1, v_zetaDeltaSet_3829_);
                leanh::lean_ctor_set(v___x_3862_, 2, v_lctx_3830_);
                leanh::lean_ctor_set(v___x_3862_, 3, v_localInstances_3831_);
                leanh::lean_ctor_set(v___x_3862_, 4, v_defEqCtx_x3f_3832_);
                leanh::lean_ctor_set(v___x_3862_, 5, v_synthPendingDepth_3833_);
                leanh::lean_ctor_set(v___x_3862_, 6, v_canUnfold_x3f_3834_);
                leanh::lean_ctor_set_uint8(
                    v___x_3862_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3828_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3862_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3835_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3862_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3836_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3862_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3837_,
                );
                v___x_3863_ = l_Lean_Meta_smartUnfolding;
                v___x_3864_ = 0;
                leanh::lean_inc_ref(v_options_3840_);
                v___x_3865_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_3840_, v___x_3863_, v___x_3864_);
                v___x_3866_ = l_Lean_diagnostics;
                v___x_3867_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_3865_, v___x_3866_);
                v___x_3868_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3852_);
                leanh::lean_dec_ref(v_env_3852_);
                if v___x_3868_ == 0 {
                    if v___x_3867_ == 0 {
                        leanh::lean_inc_ref(v_options_3840_);
                        v___y_3683_ = v___y_3798_;
                        v___y_3684_ = v___y_3799_;
                        v___y_3685_ = v_options_3840_;
                        v___y_3686_ = v___x_3862_;
                        v___y_3687_ = v___y_3800_;
                        v___y_3688_ = v___x_3865_;
                        v___y_3689_ = v___y_3801_;
                        v___y_3690_ = v_inheritedTraceOptions_3851_;
                        v___y_3691_ = v___x_3867_;
                        v___y_3692_ = v___y_3803_;
                        v___y_3693_ = v___y_3802_;
                        v_fileName_3694_ = v_fileName_3838_;
                        v_fileMap_3695_ = v_fileMap_3839_;
                        v_currRecDepth_3696_ = v_currRecDepth_3841_;
                        v_ref_3697_ = v_ref_3842_;
                        v_currNamespace_3698_ = v_currNamespace_3843_;
                        v_openDecls_3699_ = v_openDecls_3844_;
                        v_initHeartbeats_3700_ = v_initHeartbeats_3845_;
                        v_maxHeartbeats_3701_ = v_maxHeartbeats_3846_;
                        v_quotContext_3702_ = v_quotContext_3847_;
                        v_currMacroScope_3703_ = v_currMacroScope_3848_;
                        v_cancelTk_x3f_3704_ = v_cancelTk_x3f_3849_;
                        v_suppressElabErrors_3705_ = v_suppressElabErrors_3850_;
                        v_inheritedTraceOptions_3706_ = v_inheritedTraceOptions_3851_;
                        v___y_3707_ = v___y_3798_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_options_3840_);
                        v___y_3765_ = v___y_3798_;
                        v___y_3766_ = v___y_3799_;
                        v___y_3767_ = v___x_3865_;
                        v___y_3768_ = v___y_3800_;
                        v___y_3769_ = v___x_3862_;
                        v___y_3770_ = v_options_3840_;
                        v___y_3771_ = v___y_3801_;
                        v___y_3772_ = v_inheritedTraceOptions_3851_;
                        v___y_3773_ = v___x_3867_;
                        v___y_3774_ = v___y_3802_;
                        v___y_3775_ = v___y_3803_;
                        v___y_3776_ = v___x_3868_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_options_3840_);
                    v___y_3765_ = v___y_3798_;
                    v___y_3766_ = v___y_3799_;
                    v___y_3767_ = v___x_3865_;
                    v___y_3768_ = v___y_3800_;
                    v___y_3769_ = v___x_3862_;
                    v___y_3770_ = v_options_3840_;
                    v___y_3771_ = v___y_3801_;
                    v___y_3772_ = v_inheritedTraceOptions_3851_;
                    v___y_3773_ = v___x_3867_;
                    v___y_3774_ = v___y_3802_;
                    v___y_3775_ = v___y_3803_;
                    v___y_3776_ = v___x_3867_;
                    state = 7;
                    continue;
                }
            }
            13 => {
                v___x_3877_ = l_Lean_Meta_Context_config(v___y_3873_);
                v_transparency_3878_ = leanh::lean_ctor_get_uint8(v___x_3877_, 9 as u32);
                leanh::lean_dec_ref(v___x_3877_);
                v___x_3879_ = 0;
                v___x_3880_ = 1;
                v___x_3881_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3878_, v___x_3879_);
                if v___x_3881_ == 0 {
                    v___y_3798_ = v___y_3876_;
                    v___y_3799_ = v___y_3873_;
                    v___y_3800_ = v___y_3872_;
                    v___y_3801_ = v___y_3874_;
                    v___y_3802_ = v___x_3880_;
                    v___y_3803_ = v___y_3875_;
                    v___y_3804_ = v_transparency_3878_;
                    state = 10;
                    continue;
                } else {
                    v___y_3798_ = v___y_3876_;
                    v___y_3799_ = v___y_3873_;
                    v___y_3800_ = v___y_3872_;
                    v___y_3801_ = v___y_3874_;
                    v___y_3802_ = v___x_3880_;
                    v___y_3803_ = v___y_3875_;
                    v___y_3804_ = v___x_3879_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_3889_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_a_3883_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
                if leanh::lean_obj_tag(v___x_3889_) == 0 {
                    v_a_3890_ = leanh::lean_ctor_get(v___x_3889_, 0);
                    leanh::lean_inc(v_a_3890_);
                    leanh::lean_dec_ref_known(v___x_3889_, 1);
                    leanh::lean_inc(v___y_3888_);
                    leanh::lean_inc_ref(v___y_3887_);
                    leanh::lean_inc(v___y_3886_);
                    leanh::lean_inc_ref(v___y_3885_);
                    v___x_3891_ = leanh::lean_apply_5(
                        v___f_3673_,
                        v___y_3885_,
                        v___y_3886_,
                        v___y_3887_,
                        v___y_3888_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3891_) == 0 {
                        v_a_3892_ = leanh::lean_ctor_get(v___x_3891_, 0);
                        leanh::lean_inc(v_a_3892_);
                        leanh::lean_dec_ref_known(v___x_3891_, 1);
                        v___x_3893_ = (leanh::lean_unbox(v_a_3892_) as u8);
                        leanh::lean_dec(v_a_3892_);
                        if v___x_3893_ == 0 {
                            v___y_3872_ = v_a_3890_;
                            v___y_3873_ = v___y_3885_;
                            v___y_3874_ = v___y_3886_;
                            v___y_3875_ = v___y_3887_;
                            v___y_3876_ = v___y_3888_;
                            state = 13;
                            continue;
                        } else {
                            v___x_3894_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3);
                            leanh::lean_inc(v_a_3890_);
                            v___x_3895_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3895_, 0, v_a_3890_);
                            v___x_3896_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3896_, 0, v___x_3894_);
                            leanh::lean_ctor_set(v___x_3896_, 1, v___x_3895_);
                            leanh::lean_inc(v___x_3675_);
                            v___x_3897_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_3675_, v___x_3896_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
                            if leanh::lean_obj_tag(v___x_3897_) == 0 {
                                leanh::lean_dec_ref_known(v___x_3897_, 1);
                                v___y_3872_ = v_a_3890_;
                                v___y_3873_ = v___y_3885_;
                                v___y_3874_ = v___y_3886_;
                                v___y_3875_ = v___y_3887_;
                                v___y_3876_ = v___y_3888_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_3890_);
                                leanh::lean_dec(v___x_3675_);
                                leanh::lean_dec_ref(v_a_3674_);
                                v_a_3898_ = leanh::lean_ctor_get(v___x_3897_, 0);
                                v_isSharedCheck_3905_ =
                                    (!leanh::lean_is_exclusive(v___x_3897_)) as u8;
                                if v_isSharedCheck_3905_ == 0 {
                                    v___x_3900_ = v___x_3897_;
                                    v_isShared_3901_ = v_isSharedCheck_3905_;
                                    state = 15;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3898_);
                                    leanh::lean_dec(v___x_3897_);
                                    v___x_3900_ = leanh::lean_box(0);
                                    v_isShared_3901_ = v_isSharedCheck_3905_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3890_);
                        leanh::lean_dec(v___x_3675_);
                        leanh::lean_dec_ref(v_a_3674_);
                        v_a_3906_ = leanh::lean_ctor_get(v___x_3891_, 0);
                        v_isSharedCheck_3913_ =
                            (!leanh::lean_is_exclusive(v___x_3891_)) as u8;
                        if v_isSharedCheck_3913_ == 0 {
                            v___x_3908_ = v___x_3891_;
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3906_);
                            leanh::lean_dec(v___x_3891_);
                            v___x_3908_ = leanh::lean_box(0);
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3675_);
                    leanh::lean_dec_ref(v_a_3674_);
                    leanh::lean_dec_ref(v___f_3673_);
                    v_a_3914_ = leanh::lean_ctor_get(v___x_3889_, 0);
                    v_isSharedCheck_3921_ = (!leanh::lean_is_exclusive(v___x_3889_)) as u8;
                    if v_isSharedCheck_3921_ == 0 {
                        v___x_3916_ = v___x_3889_;
                        v_isShared_3917_ = v_isSharedCheck_3921_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3914_);
                        leanh::lean_dec(v___x_3889_);
                        v___x_3916_ = leanh::lean_box(0);
                        v_isShared_3917_ = v_isSharedCheck_3921_;
                        state = 19;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_3901_ == 0 {
                    v___x_3903_ = v___x_3900_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
                    v___x_3903_ = v_reuseFailAlloc_3904_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3903_;
            }
            17 => {
                if v_isShared_3909_ == 0 {
                    v___x_3911_ = v___x_3908_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3912_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
                    v___x_3911_ = v_reuseFailAlloc_3912_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3911_;
            }
            19 => {
                if v_isShared_3917_ == 0 {
                    v___x_3919_ = v___x_3916_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3920_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
                    v___x_3919_ = v_reuseFailAlloc_3920_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3919_;
            }
            21 => {
                if v_isShared_3932_ == 0 {
                    v___x_3934_ = v___x_3931_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3935_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
                    v___x_3934_ = v_reuseFailAlloc_3935_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3934_;
            }
            23 => {
                if v_isShared_3940_ == 0 {
                    v___x_3942_ = v___x_3939_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3943_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
                    v___x_3942_ = v_reuseFailAlloc_3943_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3942_;
            }
            25 => {
                if v_isShared_3948_ == 0 {
                    v___x_3950_ = v___x_3947_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3951_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
                    v___x_3950_ = v_reuseFailAlloc_3951_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___boxed(
    mut v_declName_3953_: *mut leanh::LeanObject,
    mut v_declNameNonRec_3954_: *mut leanh::LeanObject,
    mut v___x_3955_: *mut leanh::LeanObject,
    mut v___f_3956_: *mut leanh::LeanObject,
    mut v_a_3957_: *mut leanh::LeanObject,
    mut v___x_3958_: *mut leanh::LeanObject,
    mut v_____r_3959_: *mut leanh::LeanObject,
    mut v___y_3960_: *mut leanh::LeanObject,
    mut v___y_3961_: *mut leanh::LeanObject,
    mut v___y_3962_: *mut leanh::LeanObject,
    mut v___y_3963_: *mut leanh::LeanObject,
    mut v___y_3964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3965_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_3953_, v_declNameNonRec_3954_, v___x_3955_, v___f_3956_, v_a_3957_, v___x_3958_, v_____r_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
    leanh::lean_dec(v___y_3963_);
    leanh::lean_dec_ref(v___y_3962_);
    leanh::lean_dec(v___y_3961_);
    leanh::lean_dec_ref(v___y_3960_);
    return v_res_3965_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3967_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0;
    v___x_3968_ = l_Lean_stringToMessageData(v___x_3967_);
    return v___x_3968_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3970_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2;
    v___x_3971_ = l_Lean_stringToMessageData(v___x_3970_);
    return v___x_3971_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3981_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8;
    v___x_3982_ = l_Lean_stringToMessageData(v___x_3981_);
    return v___x_3982_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(
    mut v_declName_3983_: *mut leanh::LeanObject,
    mut v_a_3984_: *mut leanh::LeanObject,
    mut v___x_3985_: *mut leanh::LeanObject,
    mut v_declNameNonRec_3986_: *mut leanh::LeanObject,
    mut v___y_3987_: *mut leanh::LeanObject,
    mut v___y_3988_: *mut leanh::LeanObject,
    mut v___y_3989_: *mut leanh::LeanObject,
    mut v___y_3990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3995_: u8 = 0;
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: u8 = 0;
    let mut v___y_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4020_: u8 = 0;
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4039_: u8 = 0;
    let mut v_reuseFailAlloc_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4012_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v_a_3984_,
                    v___x_3985_,
                    v___y_3987_,
                    v___y_3988_,
                    v___y_3989_,
                    v___y_3990_,
                );
                if leanh::lean_obj_tag(v___x_4012_) == 0 {
                    v_a_4013_ = leanh::lean_ctor_get(v___x_4012_, 0);
                    leanh::lean_inc(v_a_4013_);
                    leanh::lean_dec_ref_known(v___x_4012_, 1);
                    v___x_4014_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6;
                    v___f_4015_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7;
                    v___x_4016_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_4014_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                    v_a_4017_ = leanh::lean_ctor_get(v___x_4016_, 0);
                    v_isSharedCheck_4041_ = (!leanh::lean_is_exclusive(v___x_4016_)) as u8;
                    if v_isSharedCheck_4041_ == 0 {
                        v___x_4019_ = v___x_4016_;
                        v_isShared_4020_ = v_isSharedCheck_4041_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4017_);
                        leanh::lean_dec(v___x_4016_);
                        v___x_4019_ = leanh::lean_box(0);
                        v_isShared_4020_ = v_isSharedCheck_4041_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declNameNonRec_3986_);
                    v___y_4010_ = v___x_4012_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_3995_ == 0 {
                    leanh::lean_dec_ref(v___y_3993_);
                    v___x_3996_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
                    v___x_3997_ = l_Lean_MessageData_ofConstName(v_declName_3983_, v___y_3995_);
                    v___x_3998_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3998_, 0, v___x_3996_);
                    leanh::lean_ctor_set(v___x_3998_, 1, v___x_3997_);
                    v___x_3999_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
                    v___x_4000_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4000_, 0, v___x_3998_);
                    leanh::lean_ctor_set(v___x_4000_, 1, v___x_3999_);
                    v___x_4001_ = l_Lean_Exception_toMessageData(v___y_3994_);
                    v___x_4002_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4002_, 0, v___x_4000_);
                    leanh::lean_ctor_set(v___x_4002_, 1, v___x_4001_);
                    v___x_4003_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_4002_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                    return v___x_4003_;
                } else {
                    leanh::lean_dec_ref(v___y_3994_);
                    leanh::lean_dec(v_declName_3983_);
                    return v___y_3993_;
                }
            }
            2 => {
                v___x_4007_ = l_Lean_Exception_isInterrupt(v_a_4006_);
                if v___x_4007_ == 0 {
                    leanh::lean_inc_ref(v_a_4006_);
                    v___x_4008_ = l_Lean_Exception_isRuntime(v_a_4006_);
                    v___y_3993_ = v___y_4005_;
                    v___y_3994_ = v_a_4006_;
                    v___y_3995_ = v___x_4008_;
                    state = 1;
                    continue;
                } else {
                    v___y_3993_ = v___y_4005_;
                    v___y_3994_ = v_a_4006_;
                    v___y_3995_ = v___x_4007_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v___y_4010_) == 0 {
                    leanh::lean_dec(v_declName_3983_);
                    return v___y_4010_;
                } else {
                    v_a_4011_ = leanh::lean_ctor_get(v___y_4010_, 0);
                    leanh::lean_inc(v_a_4011_);
                    v___y_4005_ = v___y_4010_;
                    v_a_4006_ = v_a_4011_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_4021_ = l_Lean_Expr_mvarId_x21(v_a_4013_);
                v___x_4022_ = (leanh::lean_unbox(v_a_4017_) as u8);
                leanh::lean_dec(v_a_4017_);
                if v___x_4022_ == 0 {
                    leanh::lean_del_object(v___x_4019_);
                    v___x_4023_ = leanh::lean_box(0);
                    leanh::lean_inc(v_declName_3983_);
                    v___x_4024_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_3983_, v_declNameNonRec_3986_, v___x_4021_, v___f_4015_, v_a_4013_, v___x_4014_, v___x_4023_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                    v___y_4010_ = v___x_4024_;
                    state = 3;
                    continue;
                } else {
                    v___x_4025_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9);
                    leanh::lean_inc(v___x_4021_);
                    if v_isShared_4020_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4019_, 1);
                        leanh::lean_ctor_set(v___x_4019_, 0, v___x_4021_);
                        v___x_4027_ = v___x_4019_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4040_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4021_);
                        v___x_4027_ = v_reuseFailAlloc_4040_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4028_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4028_, 0, v___x_4025_);
                leanh::lean_ctor_set(v___x_4028_, 1, v___x_4027_);
                v___x_4029_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_4014_, v___x_4028_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                if leanh::lean_obj_tag(v___x_4029_) == 0 {
                    v_a_4030_ = leanh::lean_ctor_get(v___x_4029_, 0);
                    leanh::lean_inc(v_a_4030_);
                    leanh::lean_dec_ref_known(v___x_4029_, 1);
                    leanh::lean_inc(v_declName_3983_);
                    v___x_4031_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_3983_, v_declNameNonRec_3986_, v___x_4021_, v___f_4015_, v_a_4013_, v___x_4014_, v_a_4030_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                    v___y_4010_ = v___x_4031_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4021_);
                    leanh::lean_dec(v_a_4013_);
                    leanh::lean_dec(v_declNameNonRec_3986_);
                    v_a_4032_ = leanh::lean_ctor_get(v___x_4029_, 0);
                    v_isSharedCheck_4039_ = (!leanh::lean_is_exclusive(v___x_4029_)) as u8;
                    if v_isSharedCheck_4039_ == 0 {
                        v___x_4034_ = v___x_4029_;
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4032_);
                        leanh::lean_dec(v___x_4029_);
                        v___x_4034_ = leanh::lean_box(0);
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                leanh::lean_inc(v_a_4032_);
                if v_isShared_4035_ == 0 {
                    v___x_4037_ = v___x_4034_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
                    v___x_4037_ = v_reuseFailAlloc_4038_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4005_ = v___x_4037_;
                v_a_4006_ = v_a_4032_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed(
    mut v_declName_4042_: *mut leanh::LeanObject,
    mut v_a_4043_: *mut leanh::LeanObject,
    mut v___x_4044_: *mut leanh::LeanObject,
    mut v_declNameNonRec_4045_: *mut leanh::LeanObject,
    mut v___y_4046_: *mut leanh::LeanObject,
    mut v___y_4047_: *mut leanh::LeanObject,
    mut v___y_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4051_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_declName_4042_, v_a_4043_, v___x_4044_, v_declNameNonRec_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
    leanh::lean_dec(v___y_4049_);
    leanh::lean_dec_ref(v___y_4048_);
    leanh::lean_dec(v___y_4047_);
    leanh::lean_dec_ref(v___y_4046_);
    return v_res_4051_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(
    mut v_a_4052_: *mut leanh::LeanObject,
    mut v_a_4053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4052_) == 0 {
                    v___x_4054_ = l_List_reverse___redArg(v_a_4053_);
                    return v___x_4054_;
                } else {
                    v_head_4055_ = leanh::lean_ctor_get(v_a_4052_, 0);
                    v_tail_4056_ = leanh::lean_ctor_get(v_a_4052_, 1);
                    v_isSharedCheck_4065_ = (!leanh::lean_is_exclusive(v_a_4052_)) as u8;
                    if v_isSharedCheck_4065_ == 0 {
                        v___x_4058_ = v_a_4052_;
                        v_isShared_4059_ = v_isSharedCheck_4065_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4056_);
                        leanh::lean_inc(v_head_4055_);
                        leanh::lean_dec(v_a_4052_);
                        v___x_4058_ = leanh::lean_box(0);
                        v_isShared_4059_ = v_isSharedCheck_4065_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4060_ = l_Lean_mkLevelParam(v_head_4055_);
                if v_isShared_4059_ == 0 {
                    leanh::lean_ctor_set(v___x_4058_, 1, v_a_4053_);
                    leanh::lean_ctor_set(v___x_4058_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4058_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4064_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_a_4053_);
                    v___x_4062_ = v_reuseFailAlloc_4064_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4052_ = v_tail_4056_;
                v_a_4053_ = v___x_4062_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(
    mut v_levelParams_4066_: *mut leanh::LeanObject,
    mut v_declName_4067_: *mut leanh::LeanObject,
    mut v_declNameNonRec_4068_: *mut leanh::LeanObject,
    mut v_name_4069_: *mut leanh::LeanObject,
    mut v_xs_4070_: *mut leanh::LeanObject,
    mut v_body_4071_: *mut leanh::LeanObject,
    mut v___y_4072_: *mut leanh::LeanObject,
    mut v___y_4073_: *mut leanh::LeanObject,
    mut v___y_4074_: *mut leanh::LeanObject,
    mut v___y_4075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u8 = 0;
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4105_: u8 = 0;
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4109_: u8 = 0;
    let mut v_a_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4113_: u8 = 0;
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v_a_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4125_: u8 = 0;
    let mut v_a_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4129_: u8 = 0;
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut v_a_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4077_ = leanh::lean_box(0);
                leanh::lean_inc(v_levelParams_4066_);
                v_us_4078_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_levelParams_4066_, v___x_4077_);
                leanh::lean_inc(v_declName_4067_);
                v___x_4079_ = l_Lean_mkConst(v_declName_4067_, v_us_4078_);
                v___x_4080_ = l_Lean_mkAppN(v___x_4079_, v_xs_4070_);
                v___x_4081_ = l_Lean_Meta_mkEq(
                    v___x_4080_,
                    v_body_4071_,
                    v___y_4072_,
                    v___y_4073_,
                    v___y_4074_,
                    v___y_4075_,
                );
                if leanh::lean_obj_tag(v___x_4081_) == 0 {
                    v_a_4082_ = leanh::lean_ctor_get(v___x_4081_, 0);
                    leanh::lean_inc_n(v_a_4082_, 2);
                    leanh::lean_dec_ref_known(v___x_4081_, 1);
                    v___x_4083_ = leanh::lean_box(0);
                    v___f_4084_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed as *mut core::ffi::c_void, 9, 4);
                    leanh::lean_closure_set(v___f_4084_, 0, v_declName_4067_);
                    leanh::lean_closure_set(v___f_4084_, 1, v_a_4082_);
                    leanh::lean_closure_set(v___f_4084_, 2, v___x_4083_);
                    leanh::lean_closure_set(v___f_4084_, 3, v_declNameNonRec_4068_);
                    v___x_4085_ = 0;
                    v___x_4086_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v___f_4084_, v___x_4085_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
                    if leanh::lean_obj_tag(v___x_4086_) == 0 {
                        v_a_4087_ = leanh::lean_ctor_get(v___x_4086_, 0);
                        leanh::lean_inc(v_a_4087_);
                        leanh::lean_dec_ref_known(v___x_4086_, 1);
                        v___x_4088_ = 1;
                        v___x_4089_ = 1;
                        v___x_4090_ = l_Lean_Meta_mkForallFVars(
                            v_xs_4070_,
                            v_a_4082_,
                            v___x_4085_,
                            v___x_4088_,
                            v___x_4088_,
                            v___x_4089_,
                            v___y_4072_,
                            v___y_4073_,
                            v___y_4074_,
                            v___y_4075_,
                        );
                        if leanh::lean_obj_tag(v___x_4090_) == 0 {
                            v_a_4091_ = leanh::lean_ctor_get(v___x_4090_, 0);
                            leanh::lean_inc(v_a_4091_);
                            leanh::lean_dec_ref_known(v___x_4090_, 1);
                            v___x_4092_ = l_Lean_Meta_letToHave(
                                v_a_4091_,
                                v___y_4072_,
                                v___y_4073_,
                                v___y_4074_,
                                v___y_4075_,
                            );
                            if leanh::lean_obj_tag(v___x_4092_) == 0 {
                                v_a_4093_ = leanh::lean_ctor_get(v___x_4092_, 0);
                                leanh::lean_inc(v_a_4093_);
                                leanh::lean_dec_ref_known(v___x_4092_, 1);
                                v___x_4094_ = l_Lean_Meta_mkLambdaFVars(
                                    v_xs_4070_,
                                    v_a_4087_,
                                    v___x_4085_,
                                    v___x_4088_,
                                    v___x_4085_,
                                    v___x_4088_,
                                    v___x_4089_,
                                    v___y_4072_,
                                    v___y_4073_,
                                    v___y_4074_,
                                    v___y_4075_,
                                );
                                if leanh::lean_obj_tag(v___x_4094_) == 0 {
                                    v_a_4095_ = leanh::lean_ctor_get(v___x_4094_, 0);
                                    leanh::lean_inc(v_a_4095_);
                                    leanh::lean_dec_ref_known(v___x_4094_, 1);
                                    leanh::lean_inc(v_name_4069_);
                                    v___x_4096_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4096_, 0, v_name_4069_);
                                    leanh::lean_ctor_set(
                                        v___x_4096_,
                                        1,
                                        v_levelParams_4066_,
                                    );
                                    leanh::lean_ctor_set(v___x_4096_, 2, v_a_4093_);
                                    v___x_4097_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4097_, 0, v_name_4069_);
                                    leanh::lean_ctor_set(v___x_4097_, 1, v___x_4077_);
                                    v___x_4098_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4098_, 0, v___x_4096_);
                                    leanh::lean_ctor_set(v___x_4098_, 1, v_a_4095_);
                                    leanh::lean_ctor_set(v___x_4098_, 2, v___x_4097_);
                                    v___x_4099_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v___x_4098_, v___y_4075_);
                                    v_a_4100_ = leanh::lean_ctor_get(v___x_4099_, 0);
                                    leanh::lean_inc(v_a_4100_);
                                    leanh::lean_dec_ref(v___x_4099_);
                                    v___x_4101_ = l_Lean_addDecl(
                                        v_a_4100_,
                                        v___x_4085_,
                                        v___y_4074_,
                                        v___y_4075_,
                                    );
                                    return v___x_4101_;
                                } else {
                                    leanh::lean_dec(v_a_4093_);
                                    leanh::lean_dec(v_name_4069_);
                                    leanh::lean_dec(v_levelParams_4066_);
                                    v_a_4102_ = leanh::lean_ctor_get(v___x_4094_, 0);
                                    v_isSharedCheck_4109_ =
                                        (!leanh::lean_is_exclusive(v___x_4094_)) as u8;
                                    if v_isSharedCheck_4109_ == 0 {
                                        v___x_4104_ = v___x_4094_;
                                        v_isShared_4105_ = v_isSharedCheck_4109_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4102_);
                                        leanh::lean_dec(v___x_4094_);
                                        v___x_4104_ = leanh::lean_box(0);
                                        v_isShared_4105_ = v_isSharedCheck_4109_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_4087_);
                                leanh::lean_dec(v_name_4069_);
                                leanh::lean_dec(v_levelParams_4066_);
                                v_a_4110_ = leanh::lean_ctor_get(v___x_4092_, 0);
                                v_isSharedCheck_4117_ =
                                    (!leanh::lean_is_exclusive(v___x_4092_)) as u8;
                                if v_isSharedCheck_4117_ == 0 {
                                    v___x_4112_ = v___x_4092_;
                                    v_isShared_4113_ = v_isSharedCheck_4117_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4110_);
                                    leanh::lean_dec(v___x_4092_);
                                    v___x_4112_ = leanh::lean_box(0);
                                    v_isShared_4113_ = v_isSharedCheck_4117_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4087_);
                            leanh::lean_dec(v_name_4069_);
                            leanh::lean_dec(v_levelParams_4066_);
                            v_a_4118_ = leanh::lean_ctor_get(v___x_4090_, 0);
                            v_isSharedCheck_4125_ =
                                (!leanh::lean_is_exclusive(v___x_4090_)) as u8;
                            if v_isSharedCheck_4125_ == 0 {
                                v___x_4120_ = v___x_4090_;
                                v_isShared_4121_ = v_isSharedCheck_4125_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4118_);
                                leanh::lean_dec(v___x_4090_);
                                v___x_4120_ = leanh::lean_box(0);
                                v_isShared_4121_ = v_isSharedCheck_4125_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4082_);
                        leanh::lean_dec(v_name_4069_);
                        leanh::lean_dec(v_levelParams_4066_);
                        v_a_4126_ = leanh::lean_ctor_get(v___x_4086_, 0);
                        v_isSharedCheck_4133_ =
                            (!leanh::lean_is_exclusive(v___x_4086_)) as u8;
                        if v_isSharedCheck_4133_ == 0 {
                            v___x_4128_ = v___x_4086_;
                            v_isShared_4129_ = v_isSharedCheck_4133_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4126_);
                            leanh::lean_dec(v___x_4086_);
                            v___x_4128_ = leanh::lean_box(0);
                            v_isShared_4129_ = v_isSharedCheck_4133_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_name_4069_);
                    leanh::lean_dec(v_declNameNonRec_4068_);
                    leanh::lean_dec(v_declName_4067_);
                    leanh::lean_dec(v_levelParams_4066_);
                    v_a_4134_ = leanh::lean_ctor_get(v___x_4081_, 0);
                    v_isSharedCheck_4141_ = (!leanh::lean_is_exclusive(v___x_4081_)) as u8;
                    if v_isSharedCheck_4141_ == 0 {
                        v___x_4136_ = v___x_4081_;
                        v_isShared_4137_ = v_isSharedCheck_4141_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4134_);
                        leanh::lean_dec(v___x_4081_);
                        v___x_4136_ = leanh::lean_box(0);
                        v_isShared_4137_ = v_isSharedCheck_4141_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4105_ == 0 {
                    v___x_4107_ = v___x_4104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4108_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
                    v___x_4107_ = v_reuseFailAlloc_4108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4107_;
            }
            3 => {
                if v_isShared_4113_ == 0 {
                    v___x_4115_ = v___x_4112_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4116_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
                    v___x_4115_ = v_reuseFailAlloc_4116_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4115_;
            }
            5 => {
                if v_isShared_4121_ == 0 {
                    v___x_4123_ = v___x_4120_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
                    v___x_4123_ = v_reuseFailAlloc_4124_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4123_;
            }
            7 => {
                if v_isShared_4129_ == 0 {
                    v___x_4131_ = v___x_4128_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4132_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
                    v___x_4131_ = v_reuseFailAlloc_4132_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4131_;
            }
            9 => {
                if v_isShared_4137_ == 0 {
                    v___x_4139_ = v___x_4136_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
                    v___x_4139_ = v_reuseFailAlloc_4140_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed(
    mut v_levelParams_4142_: *mut leanh::LeanObject,
    mut v_declName_4143_: *mut leanh::LeanObject,
    mut v_declNameNonRec_4144_: *mut leanh::LeanObject,
    mut v_name_4145_: *mut leanh::LeanObject,
    mut v_xs_4146_: *mut leanh::LeanObject,
    mut v_body_4147_: *mut leanh::LeanObject,
    mut v___y_4148_: *mut leanh::LeanObject,
    mut v___y_4149_: *mut leanh::LeanObject,
    mut v___y_4150_: *mut leanh::LeanObject,
    mut v___y_4151_: *mut leanh::LeanObject,
    mut v___y_4152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4153_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_levelParams_4142_, v_declName_4143_, v_declNameNonRec_4144_, v_name_4145_, v_xs_4146_, v_body_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
    leanh::lean_dec(v___y_4151_);
    leanh::lean_dec_ref(v___y_4150_);
    leanh::lean_dec(v___y_4149_);
    leanh::lean_dec_ref(v___y_4148_);
    leanh::lean_dec_ref(v_xs_4146_);
    return v_res_4153_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(
    mut v_declName_4154_: *mut leanh::LeanObject,
    mut v_info_4155_: *mut leanh::LeanObject,
    mut v_name_4156_: *mut leanh::LeanObject,
    mut v_a_4157_: *mut leanh::LeanObject,
    mut v_a_4158_: *mut leanh::LeanObject,
    mut v_a_4159_: *mut leanh::LeanObject,
    mut v_a_4160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declNameNonRec_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4178_: u8 = 0;
    let mut v_inheritedTraceOptions_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: u8 = 0;
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    let mut v_fileName_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4199_: u8 = 0;
    let mut v_inheritedTraceOptions_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4207_: u8 = 0;
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4219_: u8 = 0;
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4226_: u8 = 0;
    let mut v_unused_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4162_ = lean_st_ref_get(v_a_4160_);
                v_levelParams_4163_ = leanh::lean_ctor_get(v_info_4155_, 1);
                leanh::lean_inc(v_levelParams_4163_);
                v_value_4164_ = leanh::lean_ctor_get(v_info_4155_, 3);
                leanh::lean_inc_ref(v_value_4164_);
                v_declNameNonRec_4165_ = leanh::lean_ctor_get(v_info_4155_, 5);
                leanh::lean_inc(v_declNameNonRec_4165_);
                leanh::lean_dec_ref(v_info_4155_);
                v_fileName_4166_ = leanh::lean_ctor_get(v_a_4159_, 0);
                v_fileMap_4167_ = leanh::lean_ctor_get(v_a_4159_, 1);
                v_options_4168_ = leanh::lean_ctor_get(v_a_4159_, 2);
                v_currRecDepth_4169_ = leanh::lean_ctor_get(v_a_4159_, 3);
                v_ref_4170_ = leanh::lean_ctor_get(v_a_4159_, 5);
                v_currNamespace_4171_ = leanh::lean_ctor_get(v_a_4159_, 6);
                v_openDecls_4172_ = leanh::lean_ctor_get(v_a_4159_, 7);
                v_initHeartbeats_4173_ = leanh::lean_ctor_get(v_a_4159_, 8);
                v_maxHeartbeats_4174_ = leanh::lean_ctor_get(v_a_4159_, 9);
                v_quotContext_4175_ = leanh::lean_ctor_get(v_a_4159_, 10);
                v_currMacroScope_4176_ = leanh::lean_ctor_get(v_a_4159_, 11);
                v_cancelTk_x3f_4177_ = leanh::lean_ctor_get(v_a_4159_, 12);
                v_suppressElabErrors_4178_ = leanh::lean_ctor_get_uint8(
                    v_a_4159_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4179_ = leanh::lean_ctor_get(v_a_4159_, 13);
                v_env_4180_ = leanh::lean_ctor_get(v___x_4162_, 0);
                leanh::lean_inc_ref(v_env_4180_);
                leanh::lean_dec(v___x_4162_);
                v___f_4181_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed as *mut core::ffi::c_void, 11, 4);
                leanh::lean_closure_set(v___f_4181_, 0, v_levelParams_4163_);
                leanh::lean_closure_set(v___f_4181_, 1, v_declName_4154_);
                leanh::lean_closure_set(v___f_4181_, 2, v_declNameNonRec_4165_);
                leanh::lean_closure_set(v___f_4181_, 3, v_name_4156_);
                v___x_4182_ = 0;
                v___x_4183_ = l_Lean_Meta_tactic_hygienic;
                leanh::lean_inc_ref(v_options_4168_);
                v___x_4184_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_4168_, v___x_4183_, v___x_4182_);
                v___x_4185_ = l_Lean_diagnostics;
                v___x_4186_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_4184_, v___x_4185_);
                v___x_4228_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4180_);
                leanh::lean_dec_ref(v_env_4180_);
                if v___x_4228_ == 0 {
                    if v___x_4186_ == 0 {
                        v_fileName_4188_ = v_fileName_4166_;
                        v_fileMap_4189_ = v_fileMap_4167_;
                        v_currRecDepth_4190_ = v_currRecDepth_4169_;
                        v_ref_4191_ = v_ref_4170_;
                        v_currNamespace_4192_ = v_currNamespace_4171_;
                        v_openDecls_4193_ = v_openDecls_4172_;
                        v_initHeartbeats_4194_ = v_initHeartbeats_4173_;
                        v_maxHeartbeats_4195_ = v_maxHeartbeats_4174_;
                        v_quotContext_4196_ = v_quotContext_4175_;
                        v_currMacroScope_4197_ = v_currMacroScope_4176_;
                        v_cancelTk_x3f_4198_ = v_cancelTk_x3f_4177_;
                        v_suppressElabErrors_4199_ = v_suppressElabErrors_4178_;
                        v_inheritedTraceOptions_4200_ = v_inheritedTraceOptions_4179_;
                        v___y_4201_ = v_a_4160_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4207_ = v___x_4228_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_4207_ = v___x_4186_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4202_ = l_Lean_maxRecDepth;
                v___x_4203_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___x_4184_, v___x_4202_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_4200_);
                leanh::lean_inc(v_cancelTk_x3f_4198_);
                leanh::lean_inc(v_currMacroScope_4197_);
                leanh::lean_inc(v_quotContext_4196_);
                leanh::lean_inc(v_maxHeartbeats_4195_);
                leanh::lean_inc(v_initHeartbeats_4194_);
                leanh::lean_inc(v_openDecls_4193_);
                leanh::lean_inc(v_currNamespace_4192_);
                leanh::lean_inc(v_ref_4191_);
                leanh::lean_inc(v_currRecDepth_4190_);
                leanh::lean_inc_ref(v_fileMap_4189_);
                leanh::lean_inc_ref(v_fileName_4188_);
                v___x_4204_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4204_, 0, v_fileName_4188_);
                leanh::lean_ctor_set(v___x_4204_, 1, v_fileMap_4189_);
                leanh::lean_ctor_set(v___x_4204_, 2, v___x_4184_);
                leanh::lean_ctor_set(v___x_4204_, 3, v_currRecDepth_4190_);
                leanh::lean_ctor_set(v___x_4204_, 4, v___x_4203_);
                leanh::lean_ctor_set(v___x_4204_, 5, v_ref_4191_);
                leanh::lean_ctor_set(v___x_4204_, 6, v_currNamespace_4192_);
                leanh::lean_ctor_set(v___x_4204_, 7, v_openDecls_4193_);
                leanh::lean_ctor_set(v___x_4204_, 8, v_initHeartbeats_4194_);
                leanh::lean_ctor_set(v___x_4204_, 9, v_maxHeartbeats_4195_);
                leanh::lean_ctor_set(v___x_4204_, 10, v_quotContext_4196_);
                leanh::lean_ctor_set(v___x_4204_, 11, v_currMacroScope_4197_);
                leanh::lean_ctor_set(v___x_4204_, 12, v_cancelTk_x3f_4198_);
                leanh::lean_ctor_set(v___x_4204_, 13, v_inheritedTraceOptions_4200_);
                leanh::lean_ctor_set_uint8(
                    v___x_4204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_4186_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4199_,
                );
                v___x_4205_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_value_4164_, v___f_4181_, v___x_4182_, v_a_4157_, v_a_4158_, v___x_4204_, v___y_4201_);
                leanh::lean_dec_ref_known(v___x_4204_, 14);
                return v___x_4205_;
            }
            2 => {
                if v___y_4207_ == 0 {
                    v___x_4208_ = lean_st_ref_take(v_a_4160_);
                    v_env_4209_ = leanh::lean_ctor_get(v___x_4208_, 0);
                    v_nextMacroScope_4210_ = leanh::lean_ctor_get(v___x_4208_, 1);
                    v_ngen_4211_ = leanh::lean_ctor_get(v___x_4208_, 2);
                    v_auxDeclNGen_4212_ = leanh::lean_ctor_get(v___x_4208_, 3);
                    v_traceState_4213_ = leanh::lean_ctor_get(v___x_4208_, 4);
                    v_messages_4214_ = leanh::lean_ctor_get(v___x_4208_, 6);
                    v_infoState_4215_ = leanh::lean_ctor_get(v___x_4208_, 7);
                    v_snapshotTasks_4216_ = leanh::lean_ctor_get(v___x_4208_, 8);
                    v_isSharedCheck_4226_ = (!leanh::lean_is_exclusive(v___x_4208_)) as u8;
                    if v_isSharedCheck_4226_ == 0 {
                        v_unused_4227_ = leanh::lean_ctor_get(v___x_4208_, 5);
                        leanh::lean_dec(v_unused_4227_);
                        v___x_4218_ = v___x_4208_;
                        v_isShared_4219_ = v_isSharedCheck_4226_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_4216_);
                        leanh::lean_inc(v_infoState_4215_);
                        leanh::lean_inc(v_messages_4214_);
                        leanh::lean_inc(v_traceState_4213_);
                        leanh::lean_inc(v_auxDeclNGen_4212_);
                        leanh::lean_inc(v_ngen_4211_);
                        leanh::lean_inc(v_nextMacroScope_4210_);
                        leanh::lean_inc(v_env_4209_);
                        leanh::lean_dec(v___x_4208_);
                        v___x_4218_ = leanh::lean_box(0);
                        v_isShared_4219_ = v_isSharedCheck_4226_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_fileName_4188_ = v_fileName_4166_;
                    v_fileMap_4189_ = v_fileMap_4167_;
                    v_currRecDepth_4190_ = v_currRecDepth_4169_;
                    v_ref_4191_ = v_ref_4170_;
                    v_currNamespace_4192_ = v_currNamespace_4171_;
                    v_openDecls_4193_ = v_openDecls_4172_;
                    v_initHeartbeats_4194_ = v_initHeartbeats_4173_;
                    v_maxHeartbeats_4195_ = v_maxHeartbeats_4174_;
                    v_quotContext_4196_ = v_quotContext_4175_;
                    v_currMacroScope_4197_ = v_currMacroScope_4176_;
                    v_cancelTk_x3f_4198_ = v_cancelTk_x3f_4177_;
                    v_suppressElabErrors_4199_ = v_suppressElabErrors_4178_;
                    v_inheritedTraceOptions_4200_ = v_inheritedTraceOptions_4179_;
                    v___y_4201_ = v_a_4160_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4220_ = l_Lean_Kernel_enableDiag(v_env_4209_, v___x_4186_);
                v___x_4221_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once
                    ),
                    _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2,
                );
                if v_isShared_4219_ == 0 {
                    leanh::lean_ctor_set(v___x_4218_, 5, v___x_4221_);
                    leanh::lean_ctor_set(v___x_4218_, 0, v___x_4220_);
                    v___x_4223_ = v___x_4218_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4225_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_nextMacroScope_4210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 2, v_ngen_4211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 3, v_auxDeclNGen_4212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 4, v_traceState_4213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 5, v___x_4221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 6, v_messages_4214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 7, v_infoState_4215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 8, v_snapshotTasks_4216_);
                    v___x_4223_ = v_reuseFailAlloc_4225_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4224_ = lean_st_ref_set(v_a_4160_, v___x_4223_);
                v_fileName_4188_ = v_fileName_4166_;
                v_fileMap_4189_ = v_fileMap_4167_;
                v_currRecDepth_4190_ = v_currRecDepth_4169_;
                v_ref_4191_ = v_ref_4170_;
                v_currNamespace_4192_ = v_currNamespace_4171_;
                v_openDecls_4193_ = v_openDecls_4172_;
                v_initHeartbeats_4194_ = v_initHeartbeats_4173_;
                v_maxHeartbeats_4195_ = v_maxHeartbeats_4174_;
                v_quotContext_4196_ = v_quotContext_4175_;
                v_currMacroScope_4197_ = v_currMacroScope_4176_;
                v_cancelTk_x3f_4198_ = v_cancelTk_x3f_4177_;
                v_suppressElabErrors_4199_ = v_suppressElabErrors_4178_;
                v_inheritedTraceOptions_4200_ = v_inheritedTraceOptions_4179_;
                v___y_4201_ = v_a_4160_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed(
    mut v_declName_4229_: *mut leanh::LeanObject,
    mut v_info_4230_: *mut leanh::LeanObject,
    mut v_name_4231_: *mut leanh::LeanObject,
    mut v_a_4232_: *mut leanh::LeanObject,
    mut v_a_4233_: *mut leanh::LeanObject,
    mut v_a_4234_: *mut leanh::LeanObject,
    mut v_a_4235_: *mut leanh::LeanObject,
    mut v_a_4236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4237_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_4229_, v_info_4230_, v_name_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_);
    leanh::lean_dec(v_a_4235_);
    leanh::lean_dec_ref(v_a_4234_);
    leanh::lean_dec(v_a_4233_);
    leanh::lean_dec_ref(v_a_4232_);
    return v_res_4237_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(
    mut v_declName_4238_: *mut leanh::LeanObject,
    mut v_info_4239_: *mut leanh::LeanObject,
    mut v_a_4240_: *mut leanh::LeanObject,
    mut v_a_4241_: *mut leanh::LeanObject,
    mut v_a_4242_: *mut leanh::LeanObject,
    mut v_a_4243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4253_: u8 = 0;
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut v_unused_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4245_ = lean_st_ref_get(v_a_4243_);
                v_env_4246_ = leanh::lean_ctor_get(v___x_4245_, 0);
                leanh::lean_inc_ref(v_env_4246_);
                leanh::lean_dec(v___x_4245_);
                v___x_4247_ = l_Lean_Meta_unfoldThmSuffix;
                leanh::lean_inc_n(v_declName_4238_, 2);
                v___x_4248_ =
                    l_Lean_Meta_mkEqLikeNameFor(v_env_4246_, v_declName_4238_, v___x_4247_);
                leanh::lean_inc_n(v___x_4248_, 2);
                v___x_4249_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___x_4249_, 0, v_declName_4238_);
                leanh::lean_closure_set(v___x_4249_, 1, v_info_4239_);
                leanh::lean_closure_set(v___x_4249_, 2, v___x_4248_);
                v___x_4250_ = l_Lean_Meta_realizeConst(
                    v_declName_4238_,
                    v___x_4248_,
                    v___x_4249_,
                    v_a_4240_,
                    v_a_4241_,
                    v_a_4242_,
                    v_a_4243_,
                );
                if leanh::lean_obj_tag(v___x_4250_) == 0 {
                    v_isSharedCheck_4257_ = (!leanh::lean_is_exclusive(v___x_4250_)) as u8;
                    if v_isSharedCheck_4257_ == 0 {
                        v_unused_4258_ = leanh::lean_ctor_get(v___x_4250_, 0);
                        leanh::lean_dec(v_unused_4258_);
                        v___x_4252_ = v___x_4250_;
                        v_isShared_4253_ = v_isSharedCheck_4257_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4250_);
                        v___x_4252_ = leanh::lean_box(0);
                        v_isShared_4253_ = v_isSharedCheck_4257_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4248_);
                    v_a_4259_ = leanh::lean_ctor_get(v___x_4250_, 0);
                    v_isSharedCheck_4266_ = (!leanh::lean_is_exclusive(v___x_4250_)) as u8;
                    if v_isSharedCheck_4266_ == 0 {
                        v___x_4261_ = v___x_4250_;
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4259_);
                        leanh::lean_dec(v___x_4250_);
                        v___x_4261_ = leanh::lean_box(0);
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4253_ == 0 {
                    leanh::lean_ctor_set(v___x_4252_, 0, v___x_4248_);
                    v___x_4255_ = v___x_4252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4256_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4248_);
                    v___x_4255_ = v_reuseFailAlloc_4256_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4255_;
            }
            3 => {
                if v_isShared_4262_ == 0 {
                    v___x_4264_ = v___x_4261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4265_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
                    v___x_4264_ = v_reuseFailAlloc_4265_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq___boxed(
    mut v_declName_4267_: *mut leanh::LeanObject,
    mut v_info_4268_: *mut leanh::LeanObject,
    mut v_a_4269_: *mut leanh::LeanObject,
    mut v_a_4270_: *mut leanh::LeanObject,
    mut v_a_4271_: *mut leanh::LeanObject,
    mut v_a_4272_: *mut leanh::LeanObject,
    mut v_a_4273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4274_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_4267_, v_info_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
    leanh::lean_dec(v_a_4272_);
    leanh::lean_dec_ref(v_a_4271_);
    leanh::lean_dec(v_a_4270_);
    leanh::lean_dec_ref(v_a_4269_);
    return v_res_4274_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(
    mut v_declName_4275_: *mut leanh::LeanObject,
    mut v_a_4276_: *mut leanh::LeanObject,
    mut v_a_4277_: *mut leanh::LeanObject,
    mut v_a_4278_: *mut leanh::LeanObject,
    mut v_a_4279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___x_4288_: u8 = 0;
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4298_: u8 = 0;
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4303_: u8 = 0;
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v_a_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4318_: u8 = 0;
    let mut v_isSharedCheck_4319_: u8 = 0;
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4281_ = lean_st_ref_get(v_a_4279_);
                v___x_4282_ = lean_st_ref_get(v_a_4279_);
                v_env_4283_ = leanh::lean_ctor_get(v___x_4281_, 0);
                leanh::lean_inc_ref(v_env_4283_);
                leanh::lean_dec(v___x_4281_);
                v_env_4284_ = leanh::lean_ctor_get(v___x_4282_, 0);
                leanh::lean_inc_ref_n(v_env_4284_, 2);
                leanh::lean_dec(v___x_4282_);
                v___x_4285_ = l_Lean_Meta_unfoldThmSuffix;
                leanh::lean_inc(v_declName_4275_);
                v___x_4286_ =
                    l_Lean_Meta_mkEqLikeNameFor(v_env_4283_, v_declName_4275_, v___x_4285_);
                v___x_4287_ = 1;
                leanh::lean_inc(v___x_4286_);
                v___x_4288_ = l_Lean_Environment_contains(v_env_4284_, v___x_4286_, v___x_4287_);
                if v___x_4288_ == 0 {
                    leanh::lean_dec(v___x_4286_);
                    v___x_4289_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
                    v_toEnvExtension_4290_ = leanh::lean_ctor_get(v___x_4289_, 0);
                    v_asyncMode_4291_ = leanh::lean_ctor_get(v_toEnvExtension_4290_, 2);
                    v___x_4292_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
                    v___x_4293_ = 0;
                    leanh::lean_inc(v_declName_4275_);
                    v___x_4294_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                        v___x_4292_,
                        v___x_4289_,
                        v_env_4284_,
                        v_declName_4275_,
                        v_asyncMode_4291_,
                        v___x_4293_,
                    );
                    if leanh::lean_obj_tag(v___x_4294_) == 1 {
                        v_val_4295_ = leanh::lean_ctor_get(v___x_4294_, 0);
                        v_isSharedCheck_4319_ =
                            (!leanh::lean_is_exclusive(v___x_4294_)) as u8;
                        if v_isSharedCheck_4319_ == 0 {
                            v___x_4297_ = v___x_4294_;
                            v_isShared_4298_ = v_isSharedCheck_4319_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4295_);
                            leanh::lean_dec(v___x_4294_);
                            v___x_4297_ = leanh::lean_box(0);
                            v_isShared_4298_ = v_isSharedCheck_4319_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4294_);
                        leanh::lean_dec(v_declName_4275_);
                        v___x_4320_ = leanh::lean_box(0);
                        v___x_4321_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4321_, 0, v___x_4320_);
                        return v___x_4321_;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4284_);
                    leanh::lean_dec(v_declName_4275_);
                    v___x_4322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4322_, 0, v___x_4286_);
                    v___x_4323_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4323_, 0, v___x_4322_);
                    return v___x_4323_;
                }
            }
            1 => {
                v___x_4299_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_4275_, v_val_4295_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_);
                if leanh::lean_obj_tag(v___x_4299_) == 0 {
                    v_a_4300_ = leanh::lean_ctor_get(v___x_4299_, 0);
                    v_isSharedCheck_4310_ = (!leanh::lean_is_exclusive(v___x_4299_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4302_ = v___x_4299_;
                        v_isShared_4303_ = v_isSharedCheck_4310_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4300_);
                        leanh::lean_dec(v___x_4299_);
                        v___x_4302_ = leanh::lean_box(0);
                        v_isShared_4303_ = v_isSharedCheck_4310_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4297_);
                    v_a_4311_ = leanh::lean_ctor_get(v___x_4299_, 0);
                    v_isSharedCheck_4318_ = (!leanh::lean_is_exclusive(v___x_4299_)) as u8;
                    if v_isSharedCheck_4318_ == 0 {
                        v___x_4313_ = v___x_4299_;
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4311_);
                        leanh::lean_dec(v___x_4299_);
                        v___x_4313_ = leanh::lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4298_ == 0 {
                    leanh::lean_ctor_set(v___x_4297_, 0, v_a_4300_);
                    v___x_4305_ = v___x_4297_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4300_);
                    v___x_4305_ = v_reuseFailAlloc_4309_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4303_ == 0 {
                    leanh::lean_ctor_set(v___x_4302_, 0, v___x_4305_);
                    v___x_4307_ = v___x_4302_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
                    v___x_4307_ = v_reuseFailAlloc_4308_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4307_;
            }
            5 => {
                if v_isShared_4314_ == 0 {
                    v___x_4316_ = v___x_4313_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4317_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
                    v___x_4316_ = v_reuseFailAlloc_4317_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed(
    mut v_declName_4324_: *mut leanh::LeanObject,
    mut v_a_4325_: *mut leanh::LeanObject,
    mut v_a_4326_: *mut leanh::LeanObject,
    mut v_a_4327_: *mut leanh::LeanObject,
    mut v_a_4328_: *mut leanh::LeanObject,
    mut v_a_4329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4330_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_);
    leanh::lean_dec(v_a_4328_);
    leanh::lean_dec_ref(v_a_4327_);
    leanh::lean_dec(v_a_4326_);
    leanh::lean_dec_ref(v_a_4325_);
    return v_res_4330_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4333_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_;
    v___x_4334_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_4333_);
    return v___x_4334_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(
    mut v_a_4335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4336_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
    return v_res_4336_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default =
        _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default();
    leanh::lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default);
    l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo =
        _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo();
    leanh::lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo);
    res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_PartialFixpoint_eqnInfoExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_PartialFixpoint_eqnInfoExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Internal_Order_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
}