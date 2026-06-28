// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Eqns
// Imports: Lean.Elab.PreDefinition.FixedParams Init.Internal.Order.Basic Lean.Meta.Tactic.Delta Lean.Meta.Tactic.Refl
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Internal::Order::Basic::{
    initialize_Init_Internal_Order_Basic, runtime_initialize_Init_Internal_Order_Basic,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__0_value
        ) as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 113, 110, 73, 110, 102, 111, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject,14538583185260052093 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject,60575703006878408 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 101, 108, 116, 97, 76, 72, 83, 85, 110, 116, 105, 108, 70, 105, 120, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2_value) as *mut LeanObject,11109162375831805875 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 113, 117, 97, 108, 105, 116, 121, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 114, 100, 101, 114, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 105, 120, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__1_value) as *mut LeanObject,1180902349914728466 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [108, 102, 112, 95, 109, 111, 110, 111, 116, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__3_value) as *mut LeanObject,2249643242235982818 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [114, 119, 70, 105, 120, 85, 110, 100, 101, 114, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [112, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__7_value) as *mut LeanObject,9720699510028671266 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__9_value) as *mut LeanObject,2642306550782628284 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12: usize = 0;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [76, 101, 97, 110, 46, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14_value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 48, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 80, 114, 111, 106, 33, 73, 109, 112, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 111, 106, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 103, 114, 70, 117, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__17_value) as *mut LeanObject,10988039791356833343 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 102, 112, 95, 109, 111, 110, 111, 116, 111, 110, 101, 95, 102, 105, 120, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__19_value) as *mut LeanObject,5842129990421541298 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 105, 120, 95, 101, 113, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__0_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__22_value) as *mut LeanObject,1315671465214526803 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0_value: LeanStringObject<45> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 46, 69, 113, 110, 115, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1_value: LeanStringObject<90> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 90, m_capacity: 90, m_length: 89, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 46, 69, 113, 110, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 46, 114, 119, 70, 105, 120, 69, 113, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [109, 107, 85, 110, 102, 111, 108, 100, 69, 113, 32, 114, 102, 108, 32, 115, 117, 99, 99, 101, 101, 100, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [109, 107, 85, 110, 102, 111, 108, 100, 69, 113, 32, 97, 102, 116, 101, 114, 32, 114, 119, 70, 105, 120, 69, 113, 58, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [109, 107, 85, 110, 102, 111, 108, 100, 69, 113, 32, 97, 102, 116, 101, 114, 32, 100, 101, 108, 116, 97, 76, 72, 83, 58, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 117, 110, 102, 111, 108, 100, 32, 116, 104, 101, 111, 114, 101, 109, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [96, 58, 10, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [112, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__4_value) as *mut LeanObject,6897119537390546559 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__5_value) as *mut LeanObject,3297018234817926677 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [109, 107, 85, 110, 102, 111, 108, 100, 69, 113, 32, 115, 116, 97, 114, 116, 58, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2()
-> *mut LeanObject {
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    v___x_2172_ = lean_box(0);
    v___x_2173_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__1;
    v___x_2174_ = l_Lean_Expr_const___override(v___x_2173_, v___x_2172_);
    return v___x_2174_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__4()
-> *mut LeanObject {
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    v___x_2177_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
    v___x_2178_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__3;
    v___x_2179_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2_once
        ),
        _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default___closed__2,
    );
    v___x_2180_ = lean_box(0);
    v___x_2181_ = lean_box(0);
    v___x_2182_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_2182_, 0, v___x_2181_);
    lean_ctor_set(v___x_2182_, 1, v___x_2180_);
    lean_ctor_set(v___x_2182_, 2, v___x_2179_);
    lean_ctor_set(v___x_2182_, 3, v___x_2179_);
    lean_ctor_set(v___x_2182_, 4, v___x_2178_);
    lean_ctor_set(v___x_2182_, 5, v___x_2181_);
    lean_ctor_set(v___x_2182_, 6, v___x_2177_);
    lean_ctor_set(v___x_2182_, 7, v___x_2178_);
    return v___x_2182_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default() -> *mut LeanObject {
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    v___x_2183_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo() -> *mut LeanObject {
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    v___x_2184_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
    return v___x_2184_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_(
    mut v_env_2185_: *mut LeanObject,
    mut v_n_2186_: *mut LeanObject,
    mut v_x_2187_: *mut LeanObject,
) -> u8 {
    let mut v___x_2188_: u8 = 0;
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    v___x_2188_ = 1;
    v___x_2189_ = l_Lean_Environment_setExporting(v_env_2185_, v___x_2188_);
    v___x_2190_ = 0;
    v___x_2191_ = l_Lean_Environment_find_x3f(v___x_2189_, v_n_2186_, v___x_2190_);
    if lean_obj_tag(v___x_2191_) == 0 {
        return v___x_2190_;
    } else {
        let mut v_val_2192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: u8 = 0;
        v_val_2192_ = lean_ctor_get(v___x_2191_, 0);
        lean_inc(v_val_2192_);
        lean_dec_ref_known(v___x_2191_, 1);
        v___x_2193_ = l_Lean_ConstantInfo_hasValue(v_val_2192_, v___x_2190_);
        lean_dec(v_val_2192_);
        return v___x_2193_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2____boxed(
    mut v_env_2194_: *mut LeanObject,
    mut v_n_2195_: *mut LeanObject,
    mut v_x_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2197_: u8 = 0;
    let mut v_r_2198_: *mut LeanObject = core::ptr::null_mut();
    v_res_2197_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_(v_env_2194_, v_n_2195_, v_x_2196_);
    lean_dec_ref(v_x_2196_);
    v_r_2198_ = lean_box((v_res_2197_) as usize);
    return v_r_2198_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_2199_: *mut LeanObject,
    mut v_x_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2200_) == 0 {
                    v_k_2201_ = lean_ctor_get(v_x_2200_, 1);
                    v_v_2202_ = lean_ctor_get(v_x_2200_, 2);
                    v_l_2203_ = lean_ctor_get(v_x_2200_, 3);
                    v_r_2204_ = lean_ctor_get(v_x_2200_, 4);
                    v___x_2205_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_2199_, v_l_2203_);
                    lean_inc(v_v_2202_);
                    lean_inc(v_k_2201_);
                    v___x_2206_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2206_, 0, v_k_2201_);
                    lean_ctor_set(v___x_2206_, 1, v_v_2202_);
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
    mut v_init_2209_: *mut LeanObject,
    mut v_x_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2211_: *mut LeanObject = core::ptr::null_mut();
    v_res_2211_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_2209_, v_x_2210_);
    lean_dec(v_x_2210_);
    return v_res_2211_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_(
    mut v_env_2214_: *mut LeanObject,
    mut v_s_2215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    v___f_2216_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_2216_, 0, v_env_2214_);
    v___x_2217_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_;
    v_all_2218_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_2217_, v_s_2215_);
    v___x_2219_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
        v___f_2216_,
        v_s_2215_,
    );
    v_exported_2220_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_2217_, v___x_2219_);
    lean_dec(v___x_2219_);
    lean_inc_ref(v_exported_2220_);
    v___x_2221_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2221_, 0, v_exported_2220_);
    lean_ctor_set(v___x_2221_, 1, v_exported_2220_);
    lean_ctor_set(v___x_2221_, 2, v_all_2218_);
    return v___x_2221_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    v___f_2235_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_;
    v___x_2236_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_;
    v___x_2237_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_;
    v___x_2238_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_2236_, v___x_2237_, v___f_2235_);
    return v___x_2238_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2____boxed(
    mut v_a_2239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2240_: *mut LeanObject = core::ptr::null_mut();
    v_res_2240_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_();
    return v_res_2240_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0(
    mut v_init_2241_: *mut LeanObject,
    mut v_t_2242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    v___x_2243_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_2241_, v_t_2242_);
    return v___x_2243_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_2244_: *mut LeanObject,
    mut v_t_2245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2246_: *mut LeanObject = core::ptr::null_mut();
    v_res_2246_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2__spec__0(v_init_2244_, v_t_2245_);
    lean_dec(v_t_2245_);
    return v_res_2246_;
}
pub unsafe fn l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(
    mut v___x_2247_: u8,
    mut v___x_2248_: u8,
    mut v_____do__lift_2249_: u8,
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
    mut v___y_2253_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_2249_ == 0 {
        let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
        v___x_2255_ = lean_box((v___x_2247_) as usize);
        v___x_2256_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2256_, 0, v___x_2255_);
        return v___x_2256_;
    } else {
        let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
        v___x_2257_ = lean_box((v___x_2248_) as usize);
        v___x_2258_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2258_, 0, v___x_2257_);
        return v___x_2258_;
    }
}
pub unsafe fn l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(
    mut v___x_2259_: *mut LeanObject,
    mut v___x_2260_: *mut LeanObject,
    mut v_____do__lift_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
    mut v___y_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4040__boxed_2267_: u8 = 0;
    let mut v___x_4041__boxed_2268_: u8 = 0;
    let mut v_____do__lift_4042__boxed_2269_: u8 = 0;
    let mut v_res_2270_: *mut LeanObject = core::ptr::null_mut();
    v___x_4040__boxed_2267_ = (lean_unbox(v___x_2259_) as u8);
    v___x_4041__boxed_2268_ = (lean_unbox(v___x_2260_) as u8);
    v_____do__lift_4042__boxed_2269_ = (lean_unbox(v_____do__lift_2261_) as u8);
    v_res_2270_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(
        v___x_4040__boxed_2267_,
        v___x_4041__boxed_2268_,
        v_____do__lift_4042__boxed_2269_,
        v___y_2262_,
        v___y_2263_,
        v___y_2264_,
        v___y_2265_,
    );
    lean_dec(v___y_2265_);
    lean_dec_ref(v___y_2264_);
    lean_dec(v___y_2263_);
    lean_dec_ref(v___y_2262_);
    return v_res_2270_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(
    mut v_as_2271_: *mut LeanObject,
    mut v_i_2272_: usize,
    mut v_stop_2273_: usize,
) -> u8 {
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
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
                    v_kind_2276_ = lean_ctor_get_uint8(
                        v___x_2275_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
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
    mut v_as_2283_: *mut LeanObject,
    mut v_i_2284_: *mut LeanObject,
    mut v_stop_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2286_: usize = 0;
    let mut v_stop_boxed_2287_: usize = 0;
    let mut v_res_2288_: u8 = 0;
    let mut v_r_2289_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2286_ = lean_unbox_usize(v_i_2284_);
    lean_dec(v_i_2284_);
    v_stop_boxed_2287_ = lean_unbox_usize(v_stop_2285_);
    lean_dec(v_stop_2285_);
    v_res_2288_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_as_2283_, v_i_boxed_2286_, v_stop_boxed_2287_);
    lean_dec_ref(v_as_2283_);
    v_r_2289_ = lean_box((v_res_2288_) as usize);
    return v_r_2289_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(
    mut v___x_2290_: *mut LeanObject,
    mut v_declNameNonRec_2291_: *mut LeanObject,
    mut v_fixedParamPerms_2292_: *mut LeanObject,
    mut v_fixpointType_2293_: *mut LeanObject,
    mut v_as_2294_: *mut LeanObject,
    mut v_i_2295_: usize,
    mut v_stop_2296_: usize,
    mut v_b_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: usize = 0;
    let mut v___x_2308_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2298_ = lean_usize_dec_eq(v_i_2295_, v_stop_2296_);
                if v___x_2298_ == 0 {
                    v___x_2299_ = lean_array_uget_borrowed(v_as_2294_, v_i_2295_);
                    v_levelParams_2300_ = lean_ctor_get(v___x_2299_, 1);
                    v_declName_2301_ = lean_ctor_get(v___x_2299_, 3);
                    v_type_2302_ = lean_ctor_get(v___x_2299_, 6);
                    v_value_2303_ = lean_ctor_get(v___x_2299_, 7);
                    v___x_2304_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
                    lean_inc_ref(v_fixpointType_2293_);
                    lean_inc_ref(v_fixedParamPerms_2292_);
                    lean_inc(v_declNameNonRec_2291_);
                    lean_inc_ref(v___x_2290_);
                    lean_inc_ref(v_value_2303_);
                    lean_inc_ref(v_type_2302_);
                    lean_inc(v_levelParams_2300_);
                    lean_inc_n(v_declName_2301_, 2);
                    v___x_2305_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v___x_2305_, 0, v_declName_2301_);
                    lean_ctor_set(v___x_2305_, 1, v_levelParams_2300_);
                    lean_ctor_set(v___x_2305_, 2, v_type_2302_);
                    lean_ctor_set(v___x_2305_, 3, v_value_2303_);
                    lean_ctor_set(v___x_2305_, 4, v___x_2290_);
                    lean_ctor_set(v___x_2305_, 5, v_declNameNonRec_2291_);
                    lean_ctor_set(v___x_2305_, 6, v_fixedParamPerms_2292_);
                    lean_ctor_set(v___x_2305_, 7, v_fixpointType_2293_);
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
                    lean_dec_ref(v_fixpointType_2293_);
                    lean_dec_ref(v_fixedParamPerms_2292_);
                    lean_dec(v_declNameNonRec_2291_);
                    lean_dec_ref(v___x_2290_);
                    return v_b_2297_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(
    mut v___x_2310_: *mut LeanObject,
    mut v_declNameNonRec_2311_: *mut LeanObject,
    mut v_fixedParamPerms_2312_: *mut LeanObject,
    mut v_fixpointType_2313_: *mut LeanObject,
    mut v_as_2314_: *mut LeanObject,
    mut v_i_2315_: *mut LeanObject,
    mut v_stop_2316_: *mut LeanObject,
    mut v_b_2317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2318_: usize = 0;
    let mut v_stop_boxed_2319_: usize = 0;
    let mut v_res_2320_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2318_ = lean_unbox_usize(v_i_2315_);
    lean_dec(v_i_2315_);
    v_stop_boxed_2319_ = lean_unbox_usize(v_stop_2316_);
    lean_dec(v_stop_2316_);
    v_res_2320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(v___x_2310_, v_declNameNonRec_2311_, v_fixedParamPerms_2312_, v_fixpointType_2313_, v_as_2314_, v_i_boxed_2318_, v_stop_boxed_2319_, v_b_2317_);
    lean_dec_ref(v_as_2314_);
    return v_res_2320_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(
    mut v_sz_2321_: usize,
    mut v_i_2322_: usize,
    mut v_bs_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2324_: u8 = 0;
    let mut v_v_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2324_ = lean_usize_dec_lt(v_i_2322_, v_sz_2321_);
                if v___x_2324_ == 0 {
                    return v_bs_2323_;
                } else {
                    v_v_2325_ = lean_array_uget_borrowed(v_bs_2323_, v_i_2322_);
                    v_declName_2326_ = lean_ctor_get(v_v_2325_, 3);
                    lean_inc(v_declName_2326_);
                    v___x_2327_ = lean_unsigned_to_nat(0);
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
    mut v_sz_2333_: *mut LeanObject,
    mut v_i_2334_: *mut LeanObject,
    mut v_bs_2335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2336_: usize = 0;
    let mut v_i_boxed_2337_: usize = 0;
    let mut v_res_2338_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2333_);
    lean_dec(v_sz_2333_);
    v_i_boxed_2337_ = lean_unbox_usize(v_i_2334_);
    lean_dec(v_i_2334_);
    v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_boxed_2336_, v_i_boxed_2337_, v_bs_2335_);
    return v_res_2338_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(
    mut v_as_2339_: *mut LeanObject,
    mut v_i_2340_: usize,
    mut v_stop_2341_: usize,
    mut v_b_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: usize = 0;
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2346_ = lean_usize_dec_eq(v_i_2340_, v_stop_2341_);
                if v___x_2346_ == 0 {
                    v___x_2347_ = lean_array_uget_borrowed(v_as_2339_, v_i_2340_);
                    v_declName_2348_ = lean_ctor_get(v___x_2347_, 3);
                    lean_inc(v_declName_2348_);
                    v___x_2349_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(
                        v_declName_2348_,
                        v___y_2343_,
                        v___y_2344_,
                    );
                    if lean_obj_tag(v___x_2349_) == 0 {
                        v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
                        lean_inc(v_a_2350_);
                        lean_dec_ref_known(v___x_2349_, 1);
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
                    v___x_2354_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2354_, 0, v_b_2342_);
                    return v___x_2354_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(
    mut v_as_2355_: *mut LeanObject,
    mut v_i_2356_: *mut LeanObject,
    mut v_stop_2357_: *mut LeanObject,
    mut v_b_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2362_: usize = 0;
    let mut v_stop_boxed_2363_: usize = 0;
    let mut v_res_2364_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2362_ = lean_unbox_usize(v_i_2356_);
    lean_dec(v_i_2356_);
    v_stop_boxed_2363_ = lean_unbox_usize(v_stop_2357_);
    lean_dec(v_stop_2357_);
    v_res_2364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_2355_, v_i_boxed_2362_, v_stop_boxed_2363_, v_b_2358_, v___y_2359_, v___y_2360_);
    lean_dec(v___y_2360_);
    lean_dec_ref(v___y_2359_);
    lean_dec_ref(v_as_2355_);
    return v_res_2364_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(
    mut v___x_2365_: u8,
    mut v_as_2366_: *mut LeanObject,
    mut v_i_2367_: usize,
    mut v_stop_2368_: usize,
    mut v___y_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2375_: usize = 0;
    let mut v___x_2376_: usize = 0;
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: u8 = 0;
    let mut v_a_2383_: u8 = 0;
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    let mut v_a_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2378_ = lean_usize_dec_eq(v_i_2367_, v_stop_2368_);
                if v___x_2378_ == 0 {
                    v___x_2379_ = lean_array_uget_borrowed(v_as_2366_, v_i_2367_);
                    v_type_2380_ = lean_ctor_get(v___x_2379_, 6);
                    v___x_2381_ = 1;
                    lean_inc_ref(v_type_2380_);
                    v___x_2386_ = l_Lean_Meta_isProp(
                        v_type_2380_,
                        v___y_2369_,
                        v___y_2370_,
                        v___y_2371_,
                        v___y_2372_,
                    );
                    if lean_obj_tag(v___x_2386_) == 0 {
                        v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
                        lean_inc(v_a_2387_);
                        lean_dec_ref_known(v___x_2386_, 1);
                        v___x_2388_ = (lean_unbox(v_a_2387_) as u8);
                        lean_dec(v_a_2387_);
                        if v___x_2388_ == 0 {
                            v_a_2383_ = v___x_2365_;
                            state = 2;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_2386_) == 0 {
                            v_a_2389_ = lean_ctor_get(v___x_2386_, 0);
                            lean_inc(v_a_2389_);
                            lean_dec_ref_known(v___x_2386_, 1);
                            v___x_2390_ = (lean_unbox(v_a_2389_) as u8);
                            lean_dec(v_a_2389_);
                            v_a_2383_ = v___x_2390_;
                            state = 2;
                            continue;
                        } else {
                            return v___x_2386_;
                        }
                    }
                } else {
                    v___x_2391_ = 0;
                    v___x_2392_ = lean_box((v___x_2391_) as usize);
                    v___x_2393_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2393_, 0, v___x_2392_);
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
                    v___x_2384_ = lean_box((v___x_2381_) as usize);
                    v___x_2385_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2385_, 0, v___x_2384_);
                    return v___x_2385_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(
    mut v___x_2394_: *mut LeanObject,
    mut v_as_2395_: *mut LeanObject,
    mut v_i_2396_: *mut LeanObject,
    mut v_stop_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4145__boxed_2403_: u8 = 0;
    let mut v_i_boxed_2404_: usize = 0;
    let mut v_stop_boxed_2405_: usize = 0;
    let mut v_res_2406_: *mut LeanObject = core::ptr::null_mut();
    v___x_4145__boxed_2403_ = (lean_unbox(v___x_2394_) as u8);
    v_i_boxed_2404_ = lean_unbox_usize(v_i_2396_);
    lean_dec(v_i_2396_);
    v_stop_boxed_2405_ = lean_unbox_usize(v_stop_2397_);
    lean_dec(v_stop_2397_);
    v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_4145__boxed_2403_, v_as_2395_, v_i_boxed_2404_, v_stop_boxed_2405_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
    lean_dec(v___y_2401_);
    lean_dec_ref(v___y_2400_);
    lean_dec(v___y_2399_);
    lean_dec_ref(v___y_2398_);
    lean_dec_ref(v_as_2395_);
    return v_res_2406_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0() -> *mut LeanObject {
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    v___x_2407_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2407_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1() -> *mut LeanObject {
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    v___x_2408_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0_once),
        _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0,
    );
    v___x_2409_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2409_, 0, v___x_2408_);
    return v___x_2409_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2() -> *mut LeanObject {
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    v___x_2410_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once),
        _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1,
    );
    v___x_2411_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2411_, 0, v___x_2410_);
    lean_ctor_set(v___x_2411_, 1, v___x_2410_);
    return v___x_2411_;
}
pub unsafe fn _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3() -> *mut LeanObject {
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    v___x_2412_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1_once),
        _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1,
    );
    v___x_2413_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2413_, 0, v___x_2412_);
    lean_ctor_set(v___x_2413_, 1, v___x_2412_);
    lean_ctor_set(v___x_2413_, 2, v___x_2412_);
    lean_ctor_set(v___x_2413_, 3, v___x_2412_);
    lean_ctor_set(v___x_2413_, 4, v___x_2412_);
    lean_ctor_set(v___x_2413_, 5, v___x_2412_);
    return v___x_2413_;
}
pub unsafe fn l_Lean_Elab_PartialFixpoint_registerEqnsInfo(
    mut v_preDefs_2414_: *mut LeanObject,
    mut v_declNameNonRec_2415_: *mut LeanObject,
    mut v_fixedParamPerms_2416_: *mut LeanObject,
    mut v_fixpointType_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
    mut v_a_2421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2445_: u8 = 0;
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2453_: u8 = 0;
    let mut v_unused_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: u8 = 0;
    let mut v_sz_2474_: usize = 0;
    let mut v___x_2475_: usize = 0;
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: u8 = 0;
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: usize = 0;
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2489_: u8 = 0;
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: usize = 0;
    let mut v___x_2493_: usize = 0;
    let mut v___x_2494_: u8 = 0;
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: u8 = 0;
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: u8 = 0;
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: usize = 0;
    let mut v___x_2507_: usize = 0;
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: usize = 0;
    let mut v___x_2510_: usize = 0;
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2458_ = lean_unsigned_to_nat(0);
                v___x_2459_ = lean_array_get_size(v_preDefs_2414_);
                v___x_2503_ = lean_nat_dec_lt(v___x_2458_, v___x_2459_);
                if v___x_2503_ == 0 {
                    state = 9;
                    continue;
                } else {
                    v___x_2504_ = lean_box(0);
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
                v___x_2424_ = lean_box(0);
                v___x_2425_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2425_, 0, v___x_2424_);
                return v___x_2425_;
            }
            2 => {
                v___x_2435_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once
                    ),
                    _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2,
                );
                v___x_2436_ = lean_alloc_ctor(0, 9, (0) as u32);
                lean_ctor_set(v___x_2436_, 0, v___y_2434_);
                lean_ctor_set(v___x_2436_, 1, v_nextMacroScope_2427_);
                lean_ctor_set(v___x_2436_, 2, v_ngen_2428_);
                lean_ctor_set(v___x_2436_, 3, v_auxDeclNGen_2429_);
                lean_ctor_set(v___x_2436_, 4, v_traceState_2430_);
                lean_ctor_set(v___x_2436_, 5, v___x_2435_);
                lean_ctor_set(v___x_2436_, 6, v_messages_2431_);
                lean_ctor_set(v___x_2436_, 7, v_infoState_2432_);
                lean_ctor_set(v___x_2436_, 8, v_snapshotTasks_2433_);
                v___x_2437_ = lean_st_ref_set(v_a_2421_, v___x_2436_);
                v___x_2438_ = lean_st_ref_take(v_a_2419_);
                v_mctx_2439_ = lean_ctor_get(v___x_2438_, 0);
                v_zetaDeltaFVarIds_2440_ = lean_ctor_get(v___x_2438_, 2);
                v_postponed_2441_ = lean_ctor_get(v___x_2438_, 3);
                v_diag_2442_ = lean_ctor_get(v___x_2438_, 4);
                v_isSharedCheck_2453_ = (!lean_is_exclusive(v___x_2438_)) as u8;
                if v_isSharedCheck_2453_ == 0 {
                    v_unused_2454_ = lean_ctor_get(v___x_2438_, 1);
                    lean_dec(v_unused_2454_);
                    v___x_2444_ = v___x_2438_;
                    v_isShared_2445_ = v_isSharedCheck_2453_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_2442_);
                    lean_inc(v_postponed_2441_);
                    lean_inc(v_zetaDeltaFVarIds_2440_);
                    lean_inc(v_mctx_2439_);
                    lean_dec(v___x_2438_);
                    v___x_2444_ = lean_box(0);
                    v_isShared_2445_ = v_isSharedCheck_2453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2446_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3_once
                    ),
                    _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3,
                );
                if v_isShared_2445_ == 0 {
                    lean_ctor_set(v___x_2444_, 1, v___x_2446_);
                    v___x_2448_ = v___x_2444_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_mctx_2439_);
                    lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2446_);
                    lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_zetaDeltaFVarIds_2440_);
                    lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_postponed_2441_);
                    lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_diag_2442_);
                    v___x_2448_ = v_reuseFailAlloc_2452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2449_ = lean_st_ref_set(v_a_2419_, v___x_2448_);
                v___x_2450_ = lean_box(0);
                v___x_2451_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2451_, 0, v___x_2450_);
                return v___x_2451_;
            }
            5 => {
                v___x_2456_ = lean_box(0);
                v___x_2457_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2457_, 0, v___x_2456_);
                return v___x_2457_;
            }
            6 => {
                if lean_obj_tag(v___y_2461_) == 0 {
                    v_a_2462_ = lean_ctor_get(v___y_2461_, 0);
                    lean_inc(v_a_2462_);
                    lean_dec_ref_known(v___y_2461_, 1);
                    v___x_2463_ = (lean_unbox(v_a_2462_) as u8);
                    lean_dec(v_a_2462_);
                    if v___x_2463_ == 0 {
                        v___x_2464_ = lean_st_ref_take(v_a_2421_);
                        v_env_2465_ = lean_ctor_get(v___x_2464_, 0);
                        lean_inc_ref(v_env_2465_);
                        v_nextMacroScope_2466_ = lean_ctor_get(v___x_2464_, 1);
                        lean_inc(v_nextMacroScope_2466_);
                        v_ngen_2467_ = lean_ctor_get(v___x_2464_, 2);
                        lean_inc_ref(v_ngen_2467_);
                        v_auxDeclNGen_2468_ = lean_ctor_get(v___x_2464_, 3);
                        lean_inc_ref(v_auxDeclNGen_2468_);
                        v_traceState_2469_ = lean_ctor_get(v___x_2464_, 4);
                        lean_inc_ref(v_traceState_2469_);
                        v_messages_2470_ = lean_ctor_get(v___x_2464_, 6);
                        lean_inc_ref(v_messages_2470_);
                        v_infoState_2471_ = lean_ctor_get(v___x_2464_, 7);
                        lean_inc_ref(v_infoState_2471_);
                        v_snapshotTasks_2472_ = lean_ctor_get(v___x_2464_, 8);
                        lean_inc_ref(v_snapshotTasks_2472_);
                        lean_dec(v___x_2464_);
                        v___x_2473_ = lean_nat_dec_lt(v___x_2458_, v___x_2459_);
                        if v___x_2473_ == 0 {
                            lean_dec_ref(v_fixpointType_2417_);
                            lean_dec_ref(v_fixedParamPerms_2416_);
                            lean_dec(v_declNameNonRec_2415_);
                            lean_dec_ref(v_preDefs_2414_);
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
                            lean_inc_ref(v_preDefs_2414_);
                            v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(v_sz_2474_, v___x_2475_, v_preDefs_2414_);
                            v___x_2477_ = lean_nat_dec_le(v___x_2459_, v___x_2459_);
                            if v___x_2477_ == 0 {
                                if v___x_2473_ == 0 {
                                    lean_dec_ref(v___x_2476_);
                                    lean_dec_ref(v_fixpointType_2417_);
                                    lean_dec_ref(v_fixedParamPerms_2416_);
                                    lean_dec(v_declNameNonRec_2415_);
                                    lean_dec_ref(v_preDefs_2414_);
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
                                    lean_dec_ref(v_preDefs_2414_);
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
                                lean_dec_ref(v_preDefs_2414_);
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
                        lean_dec_ref(v_fixpointType_2417_);
                        lean_dec_ref(v_fixedParamPerms_2416_);
                        lean_dec(v_declNameNonRec_2415_);
                        lean_dec_ref(v_preDefs_2414_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_fixpointType_2417_);
                    lean_dec_ref(v_fixedParamPerms_2416_);
                    lean_dec(v_declNameNonRec_2415_);
                    lean_dec_ref(v_preDefs_2414_);
                    v_a_2482_ = lean_ctor_get(v___y_2461_, 0);
                    v_isSharedCheck_2489_ = (!lean_is_exclusive(v___y_2461_)) as u8;
                    if v_isSharedCheck_2489_ == 0 {
                        v___x_2484_ = v___y_2461_;
                        v_isShared_2485_ = v_isSharedCheck_2489_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2482_);
                        lean_dec(v___y_2461_);
                        v___x_2484_ = lean_box(0);
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
                    v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
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
                    lean_dec_ref(v_fixpointType_2417_);
                    lean_dec_ref(v_fixedParamPerms_2416_);
                    lean_dec(v_declNameNonRec_2415_);
                    lean_dec_ref(v_preDefs_2414_);
                    state = 5;
                    continue;
                } else {
                    if v___x_2491_ == 0 {
                        lean_dec_ref(v_fixpointType_2417_);
                        lean_dec_ref(v_fixedParamPerms_2416_);
                        lean_dec(v_declNameNonRec_2415_);
                        lean_dec_ref(v_preDefs_2414_);
                        state = 5;
                        continue;
                    } else {
                        v___x_2492_ = 0usize;
                        v___x_2493_ = lean_usize_of_nat(v___x_2459_);
                        v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(v_preDefs_2414_, v___x_2492_, v___x_2493_);
                        if v___x_2494_ == 0 {
                            lean_dec_ref(v_fixpointType_2417_);
                            lean_dec_ref(v_fixedParamPerms_2416_);
                            lean_dec(v_declNameNonRec_2415_);
                            lean_dec_ref(v_preDefs_2414_);
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
                                    lean_dec_ref(v_fixpointType_2417_);
                                    lean_dec_ref(v_fixedParamPerms_2416_);
                                    lean_dec(v_declNameNonRec_2415_);
                                    lean_dec_ref(v_preDefs_2414_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(v___x_2494_, v_preDefs_2414_, v___x_2492_, v___x_2493_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
                                    if lean_obj_tag(v___x_2497_) == 0 {
                                        v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
                                        lean_inc(v_a_2498_);
                                        lean_dec_ref_known(v___x_2497_, 1);
                                        v___x_2499_ = (lean_unbox(v_a_2498_) as u8);
                                        lean_dec(v_a_2498_);
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
                if lean_obj_tag(v___y_2502_) == 0 {
                    lean_dec_ref_known(v___y_2502_, 1);
                    state = 9;
                    continue;
                } else {
                    lean_dec_ref(v_fixpointType_2417_);
                    lean_dec_ref(v_fixedParamPerms_2416_);
                    lean_dec(v_declNameNonRec_2415_);
                    lean_dec_ref(v_preDefs_2414_);
                    return v___y_2502_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_PartialFixpoint_registerEqnsInfo___boxed(
    mut v_preDefs_2512_: *mut LeanObject,
    mut v_declNameNonRec_2513_: *mut LeanObject,
    mut v_fixedParamPerms_2514_: *mut LeanObject,
    mut v_fixpointType_2515_: *mut LeanObject,
    mut v_a_2516_: *mut LeanObject,
    mut v_a_2517_: *mut LeanObject,
    mut v_a_2518_: *mut LeanObject,
    mut v_a_2519_: *mut LeanObject,
    mut v_a_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2521_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2519_);
    lean_dec_ref(v_a_2518_);
    lean_dec(v_a_2517_);
    lean_dec_ref(v_a_2516_);
    return v_res_2521_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(
    mut v_as_2522_: *mut LeanObject,
    mut v_i_2523_: usize,
    mut v_stop_2524_: usize,
    mut v_b_2525_: *mut LeanObject,
    mut v___y_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(v_as_2522_, v_i_2523_, v_stop_2524_, v_b_2525_, v___y_2528_, v___y_2529_);
    return v___x_2531_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(
    mut v_as_2532_: *mut LeanObject,
    mut v_i_2533_: *mut LeanObject,
    mut v_stop_2534_: *mut LeanObject,
    mut v_b_2535_: *mut LeanObject,
    mut v___y_2536_: *mut LeanObject,
    mut v___y_2537_: *mut LeanObject,
    mut v___y_2538_: *mut LeanObject,
    mut v___y_2539_: *mut LeanObject,
    mut v___y_2540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2541_: usize = 0;
    let mut v_stop_boxed_2542_: usize = 0;
    let mut v_res_2543_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2541_ = lean_unbox_usize(v_i_2533_);
    lean_dec(v_i_2533_);
    v_stop_boxed_2542_ = lean_unbox_usize(v_stop_2534_);
    lean_dec(v_stop_2534_);
    v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(v_as_2532_, v_i_boxed_2541_, v_stop_boxed_2542_, v_b_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
    lean_dec(v___y_2539_);
    lean_dec_ref(v___y_2538_);
    lean_dec(v___y_2537_);
    lean_dec_ref(v___y_2536_);
    lean_dec_ref(v_as_2532_);
    return v_res_2543_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(
    mut v_mvarId_2544_: *mut LeanObject,
    mut v_x_2545_: *mut LeanObject,
    mut v___y_2546_: *mut LeanObject,
    mut v___y_2547_: *mut LeanObject,
    mut v___y_2548_: *mut LeanObject,
    mut v___y_2549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_a_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2563_: u8 = 0;
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2551_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_2544_,
                    v_x_2545_,
                    v___y_2546_,
                    v___y_2547_,
                    v___y_2548_,
                    v___y_2549_,
                );
                if lean_obj_tag(v___x_2551_) == 0 {
                    v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
                    v_isSharedCheck_2559_ = (!lean_is_exclusive(v___x_2551_)) as u8;
                    if v_isSharedCheck_2559_ == 0 {
                        v___x_2554_ = v___x_2551_;
                        v_isShared_2555_ = v_isSharedCheck_2559_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2552_);
                        lean_dec(v___x_2551_);
                        v___x_2554_ = lean_box(0);
                        v_isShared_2555_ = v_isSharedCheck_2559_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2560_ = lean_ctor_get(v___x_2551_, 0);
                    v_isSharedCheck_2567_ = (!lean_is_exclusive(v___x_2551_)) as u8;
                    if v_isSharedCheck_2567_ == 0 {
                        v___x_2562_ = v___x_2551_;
                        v_isShared_2563_ = v_isSharedCheck_2567_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2560_);
                        lean_dec(v___x_2551_);
                        v___x_2562_ = lean_box(0);
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
                    v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
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
                    v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
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
    mut v_mvarId_2568_: *mut LeanObject,
    mut v_x_2569_: *mut LeanObject,
    mut v___y_2570_: *mut LeanObject,
    mut v___y_2571_: *mut LeanObject,
    mut v___y_2572_: *mut LeanObject,
    mut v___y_2573_: *mut LeanObject,
    mut v___y_2574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2575_: *mut LeanObject = core::ptr::null_mut();
    v_res_2575_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2568_, v_x_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
    lean_dec(v___y_2573_);
    lean_dec_ref(v___y_2572_);
    lean_dec(v___y_2571_);
    lean_dec_ref(v___y_2570_);
    return v_res_2575_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(
    mut v_00_u03b1_2576_: *mut LeanObject,
    mut v_mvarId_2577_: *mut LeanObject,
    mut v_x_2578_: *mut LeanObject,
    mut v___y_2579_: *mut LeanObject,
    mut v___y_2580_: *mut LeanObject,
    mut v___y_2581_: *mut LeanObject,
    mut v___y_2582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2577_, v_x_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
    return v___x_2584_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___boxed(
    mut v_00_u03b1_2585_: *mut LeanObject,
    mut v_mvarId_2586_: *mut LeanObject,
    mut v_x_2587_: *mut LeanObject,
    mut v___y_2588_: *mut LeanObject,
    mut v___y_2589_: *mut LeanObject,
    mut v___y_2590_: *mut LeanObject,
    mut v___y_2591_: *mut LeanObject,
    mut v___y_2592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2593_: *mut LeanObject = core::ptr::null_mut();
    v_res_2593_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0(v_00_u03b1_2585_, v_mvarId_2586_, v_x_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
    lean_dec(v___y_2591_);
    lean_dec_ref(v___y_2590_);
    lean_dec(v___y_2589_);
    lean_dec_ref(v___y_2588_);
    return v_res_2593_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(
    mut v_declName_2594_: *mut LeanObject,
    mut v_declNameNonRec_2595_: *mut LeanObject,
    mut v_n_2596_: *mut LeanObject,
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
    mut v_declName_2599_: *mut LeanObject,
    mut v_declNameNonRec_2600_: *mut LeanObject,
    mut v_n_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2602_: u8 = 0;
    let mut v_r_2603_: *mut LeanObject = core::ptr::null_mut();
    v_res_2602_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(v_declName_2599_, v_declNameNonRec_2600_, v_n_2601_);
    lean_dec(v_n_2601_);
    lean_dec(v_declNameNonRec_2600_);
    lean_dec(v_declName_2599_);
    v_r_2603_ = lean_box((v_res_2602_) as usize);
    return v_r_2603_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6()
-> *mut LeanObject {
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    v___x_2613_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5;
    v___x_2614_ = l_Lean_MessageData_ofFormat(v___x_2613_);
    return v___x_2614_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7()
-> *mut LeanObject {
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    v___x_2615_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
    v___x_2616_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2616_, 0, v___x_2615_);
    return v___x_2616_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(
    mut v_mvarId_2617_: *mut LeanObject,
    mut v___f_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: u8 = 0;
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2644_: u8 = 0;
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_a_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut v_a_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2660_: u8 = 0;
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_2617_);
                v___x_2624_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_2617_,
                    v___y_2619_,
                    v___y_2620_,
                    v___y_2621_,
                    v___y_2622_,
                );
                if lean_obj_tag(v___x_2624_) == 0 {
                    v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
                    lean_inc(v_a_2625_);
                    lean_dec_ref_known(v___x_2624_, 1);
                    v___x_2626_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1;
                    v___x_2627_ = lean_unsigned_to_nat(3);
                    v___x_2628_ = l_Lean_Expr_isAppOfArity(v_a_2625_, v___x_2626_, v___x_2627_);
                    if v___x_2628_ == 0 {
                        lean_dec(v_a_2625_);
                        lean_dec_ref(v___f_2618_);
                        v___x_2629_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3;
                        v___x_2630_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
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
                        lean_dec_ref(v___x_2632_);
                        v___x_2634_ = 0;
                        v___x_2635_ = l_Lean_Meta_deltaExpand(
                            v___x_2633_,
                            v___f_2618_,
                            v___x_2634_,
                            v___y_2621_,
                            v___y_2622_,
                        );
                        if lean_obj_tag(v___x_2635_) == 0 {
                            v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
                            lean_inc(v_a_2636_);
                            lean_dec_ref_known(v___x_2635_, 1);
                            v___x_2637_ = l_Lean_Expr_appArg_x21(v_a_2625_);
                            lean_dec(v_a_2625_);
                            v___x_2638_ = l_Lean_Meta_mkEq(
                                v_a_2636_,
                                v___x_2637_,
                                v___y_2619_,
                                v___y_2620_,
                                v___y_2621_,
                                v___y_2622_,
                            );
                            if lean_obj_tag(v___x_2638_) == 0 {
                                v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
                                lean_inc(v_a_2639_);
                                lean_dec_ref_known(v___x_2638_, 1);
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
                                lean_dec(v_mvarId_2617_);
                                v_a_2641_ = lean_ctor_get(v___x_2638_, 0);
                                v_isSharedCheck_2648_ = (!lean_is_exclusive(v___x_2638_)) as u8;
                                if v_isSharedCheck_2648_ == 0 {
                                    v___x_2643_ = v___x_2638_;
                                    v_isShared_2644_ = v_isSharedCheck_2648_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_2641_);
                                    lean_dec(v___x_2638_);
                                    v___x_2643_ = lean_box(0);
                                    v_isShared_2644_ = v_isSharedCheck_2648_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2625_);
                            lean_dec(v_mvarId_2617_);
                            v_a_2649_ = lean_ctor_get(v___x_2635_, 0);
                            v_isSharedCheck_2656_ = (!lean_is_exclusive(v___x_2635_)) as u8;
                            if v_isSharedCheck_2656_ == 0 {
                                v___x_2651_ = v___x_2635_;
                                v_isShared_2652_ = v_isSharedCheck_2656_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2649_);
                                lean_dec(v___x_2635_);
                                v___x_2651_ = lean_box(0);
                                v_isShared_2652_ = v_isSharedCheck_2656_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___f_2618_);
                    lean_dec(v_mvarId_2617_);
                    v_a_2657_ = lean_ctor_get(v___x_2624_, 0);
                    v_isSharedCheck_2664_ = (!lean_is_exclusive(v___x_2624_)) as u8;
                    if v_isSharedCheck_2664_ == 0 {
                        v___x_2659_ = v___x_2624_;
                        v_isShared_2660_ = v_isSharedCheck_2664_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2657_);
                        lean_dec(v___x_2624_);
                        v___x_2659_ = lean_box(0);
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
                    v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
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
                    v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
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
                    v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
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
    mut v_mvarId_2665_: *mut LeanObject,
    mut v___f_2666_: *mut LeanObject,
    mut v___y_2667_: *mut LeanObject,
    mut v___y_2668_: *mut LeanObject,
    mut v___y_2669_: *mut LeanObject,
    mut v___y_2670_: *mut LeanObject,
    mut v___y_2671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2672_: *mut LeanObject = core::ptr::null_mut();
    v_res_2672_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(v_mvarId_2665_, v___f_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
    lean_dec(v___y_2670_);
    lean_dec_ref(v___y_2669_);
    lean_dec(v___y_2668_);
    lean_dec_ref(v___y_2667_);
    return v_res_2672_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(
    mut v_declName_2673_: *mut LeanObject,
    mut v_declNameNonRec_2674_: *mut LeanObject,
    mut v_mvarId_2675_: *mut LeanObject,
    mut v_a_2676_: *mut LeanObject,
    mut v_a_2677_: *mut LeanObject,
    mut v_a_2678_: *mut LeanObject,
    mut v_a_2679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    v___f_2681_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___f_2681_, 0, v_declName_2673_);
    lean_closure_set(v___f_2681_, 1, v_declNameNonRec_2674_);
    lean_inc(v_mvarId_2675_);
    v___f_2682_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___boxed as *mut core::ffi::c_void, 7, 2);
    lean_closure_set(v___f_2682_, 0, v_mvarId_2675_);
    lean_closure_set(v___f_2682_, 1, v___f_2681_);
    v___x_2683_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_2675_, v___f_2682_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
    return v___x_2683_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___boxed(
    mut v_declName_2684_: *mut LeanObject,
    mut v_declNameNonRec_2685_: *mut LeanObject,
    mut v_mvarId_2686_: *mut LeanObject,
    mut v_a_2687_: *mut LeanObject,
    mut v_a_2688_: *mut LeanObject,
    mut v_a_2689_: *mut LeanObject,
    mut v_a_2690_: *mut LeanObject,
    mut v_a_2691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2692_: *mut LeanObject = core::ptr::null_mut();
    v_res_2692_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_2684_, v_declNameNonRec_2685_, v_mvarId_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
    lean_dec(v_a_2690_);
    lean_dec_ref(v_a_2689_);
    lean_dec(v_a_2688_);
    lean_dec_ref(v_a_2687_);
    return v_res_2692_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(
    mut v_msg_2693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    v___x_2694_ = l_Lean_instInhabitedExpr;
    v___x_2695_ = lean_panic_fn_borrowed(v___x_2694_, v_msg_2693_);
    return v___x_2695_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(
    mut v_msgData_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    v___x_2702_ = lean_st_ref_get(v___y_2700_);
    v_env_2703_ = lean_ctor_get(v___x_2702_, 0);
    lean_inc_ref(v_env_2703_);
    lean_dec(v___x_2702_);
    v___x_2704_ = lean_st_ref_get(v___y_2698_);
    v_mctx_2705_ = lean_ctor_get(v___x_2704_, 0);
    lean_inc_ref(v_mctx_2705_);
    lean_dec(v___x_2704_);
    v_lctx_2706_ = lean_ctor_get(v___y_2697_, 2);
    v_options_2707_ = lean_ctor_get(v___y_2699_, 2);
    lean_inc_ref(v_options_2707_);
    lean_inc_ref(v_lctx_2706_);
    v___x_2708_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2708_, 0, v_env_2703_);
    lean_ctor_set(v___x_2708_, 1, v_mctx_2705_);
    lean_ctor_set(v___x_2708_, 2, v_lctx_2706_);
    lean_ctor_set(v___x_2708_, 3, v_options_2707_);
    v___x_2709_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2709_, 0, v___x_2708_);
    lean_ctor_set(v___x_2709_, 1, v_msgData_2696_);
    v___x_2710_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2710_, 0, v___x_2709_);
    return v___x_2710_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0___boxed(
    mut v_msgData_2711_: *mut LeanObject,
    mut v___y_2712_: *mut LeanObject,
    mut v___y_2713_: *mut LeanObject,
    mut v___y_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2717_: *mut LeanObject = core::ptr::null_mut();
    v_res_2717_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msgData_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
    lean_dec(v___y_2715_);
    lean_dec_ref(v___y_2714_);
    lean_dec(v___y_2713_);
    lean_dec_ref(v___y_2712_);
    return v_res_2717_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(
    mut v_msg_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2729_: u8 = 0;
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2724_ = lean_ctor_get(v___y_2721_, 5);
                v___x_2725_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
                v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
                v_isSharedCheck_2734_ = (!lean_is_exclusive(v___x_2725_)) as u8;
                if v_isSharedCheck_2734_ == 0 {
                    v___x_2728_ = v___x_2725_;
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2726_);
                    lean_dec(v___x_2725_);
                    v___x_2728_ = lean_box(0);
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2724_);
                v___x_2730_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2730_, 0, v_ref_2724_);
                lean_ctor_set(v___x_2730_, 1, v_a_2726_);
                if v_isShared_2729_ == 0 {
                    lean_ctor_set_tag(v___x_2728_, 1);
                    lean_ctor_set(v___x_2728_, 0, v___x_2730_);
                    v___x_2732_ = v___x_2728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2730_);
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
    mut v_msg_2735_: *mut LeanObject,
    mut v___y_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2741_: *mut LeanObject = core::ptr::null_mut();
    v_res_2741_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
    lean_dec(v___y_2739_);
    lean_dec_ref(v___y_2738_);
    lean_dec(v___y_2737_);
    lean_dec_ref(v___y_2736_);
    return v_res_2741_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6()
-> *mut LeanObject {
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    v___x_2754_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__5;
    v___x_2755_ = l_Lean_stringToMessageData(v___x_2754_);
    return v___x_2755_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11()
-> *mut LeanObject {
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    v___x_2762_ = lean_unsigned_to_nat(0);
    v___x_2763_ = l_Lean_Expr_bvar___override(v___x_2762_);
    return v___x_2763_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12()
-> usize {
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: usize = 0;
    v___x_2764_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
    v___x_2765_ = lean_ptr_addr(v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16()
-> *mut LeanObject {
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    v___x_2769_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
    v___x_2770_ = lean_unsigned_to_nat(18);
    v___x_2771_ = lean_unsigned_to_nat(1887);
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
-> *mut LeanObject {
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2784_: *mut LeanObject = core::ptr::null_mut();
    v___x_2783_ = lean_box(0);
    v_dummy_2784_ = l_Lean_Expr_sort___override(v___x_2783_);
    return v_dummy_2784_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(
    mut v_lhs_2790_: *mut LeanObject,
    mut v_a_2791_: *mut LeanObject,
    mut v_a_2792_: *mut LeanObject,
    mut v_a_2793_: *mut LeanObject,
    mut v_a_2794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: u8 = 0;
    let mut v___x_2802_: u8 = 0;
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: u8 = 0;
    let mut v___y_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: usize = 0;
    let mut v___x_2828_: usize = 0;
    let mut v___x_2829_: u8 = 0;
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2796_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
                v___x_2797_ = lean_unsigned_to_nat(4);
                v___x_2798_ = l_Lean_Expr_isAppOfArity(v_lhs_2790_, v___x_2796_, v___x_2797_);
                if v___x_2798_ == 0 {
                    v___x_2799_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
                    v___x_2800_ = l_Lean_Expr_isAppOfArity(v_lhs_2790_, v___x_2799_, v___x_2797_);
                    if v___x_2800_ == 0 {
                        v___x_2801_ = l_Lean_Expr_isApp(v_lhs_2790_);
                        if v___x_2801_ == 0 {
                            v___x_2802_ = l_Lean_Expr_isProj(v_lhs_2790_);
                            if v___x_2802_ == 0 {
                                v___x_2803_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
                                v___x_2804_ = l_Lean_MessageData_ofExpr(v_lhs_2790_);
                                v___x_2805_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2805_, 0, v___x_2803_);
                                lean_ctor_set(v___x_2805_, 1, v___x_2804_);
                                v___x_2806_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_2805_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
                                return v___x_2806_;
                            } else {
                                v___x_2807_ = l_Lean_Expr_projExpr_x21(v_lhs_2790_);
                                lean_inc(v_a_2794_);
                                lean_inc_ref(v_a_2793_);
                                lean_inc(v_a_2792_);
                                lean_inc_ref(v_a_2791_);
                                lean_inc_ref(v___x_2807_);
                                v___x_2808_ = lean_infer_type(
                                    v___x_2807_,
                                    v_a_2791_,
                                    v_a_2792_,
                                    v_a_2793_,
                                    v_a_2794_,
                                );
                                if lean_obj_tag(v___x_2808_) == 0 {
                                    v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
                                    lean_inc(v_a_2809_);
                                    lean_dec_ref_known(v___x_2808_, 1);
                                    v___x_2810_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_2807_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
                                    if lean_obj_tag(v___x_2810_) == 0 {
                                        v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
                                        lean_inc(v_a_2811_);
                                        lean_dec_ref_known(v___x_2810_, 1);
                                        v___x_2812_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
                                        v___x_2813_ = 0;
                                        if lean_obj_tag(v_lhs_2790_) == 11 {
                                            v_typeName_2823_ = lean_ctor_get(v_lhs_2790_, 0);
                                            v_idx_2824_ = lean_ctor_get(v_lhs_2790_, 1);
                                            v_struct_2825_ = lean_ctor_get(v_lhs_2790_, 2);
                                            v___x_2826_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
                                            v___x_2827_ = lean_ptr_addr(v_struct_2825_);
                                            v___x_2828_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__12);
                                            v___x_2829_ =
                                                lean_usize_dec_eq(v___x_2827_, v___x_2828_);
                                            if v___x_2829_ == 0 {
                                                lean_inc(v_idx_2824_);
                                                lean_inc(v_typeName_2823_);
                                                lean_dec_ref_known(v_lhs_2790_, 3);
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
                                            lean_dec_ref(v_lhs_2790_);
                                            v___x_2831_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__16);
                                            v___x_2832_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__1(v___x_2831_);
                                            v___y_2815_ = v___x_2832_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_2809_);
                                        lean_dec_ref(v_lhs_2790_);
                                        return v___x_2810_;
                                    }
                                } else {
                                    lean_dec_ref(v___x_2807_);
                                    lean_dec_ref(v_lhs_2790_);
                                    return v___x_2808_;
                                }
                            }
                        } else {
                            v___x_2833_ = l_Lean_Expr_appFn_x21(v_lhs_2790_);
                            v___x_2834_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_2833_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
                            if lean_obj_tag(v___x_2834_) == 0 {
                                v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
                                lean_inc(v_a_2835_);
                                lean_dec_ref_known(v___x_2834_, 1);
                                v___x_2836_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
                                v___x_2837_ = l_Lean_Expr_appArg_x21(v_lhs_2790_);
                                lean_dec_ref(v_lhs_2790_);
                                v___x_2838_ = lean_unsigned_to_nat(2);
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
                                lean_dec_ref(v_lhs_2790_);
                                return v___x_2834_;
                            }
                        }
                    } else {
                        v___x_2843_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
                        v___x_2844_ = l_Lean_Expr_getAppFn(v_lhs_2790_);
                        v___x_2845_ = l_Lean_Expr_constLevels_x21(v___x_2844_);
                        lean_dec_ref(v___x_2844_);
                        v___x_2846_ = l_Lean_mkConst(v___x_2843_, v___x_2845_);
                        v_dummy_2847_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
                        v_nargs_2848_ = l_Lean_Expr_getAppNumArgs(v_lhs_2790_);
                        lean_inc(v_nargs_2848_);
                        v___x_2849_ = lean_mk_array(v_nargs_2848_, v_dummy_2847_);
                        v___x_2850_ = lean_unsigned_to_nat(1);
                        v___x_2851_ = lean_nat_sub(v_nargs_2848_, v___x_2850_);
                        lean_dec(v_nargs_2848_);
                        v___x_2852_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v_lhs_2790_,
                            v___x_2849_,
                            v___x_2851_,
                        );
                        v___x_2853_ = l_Lean_mkAppN(v___x_2846_, v___x_2852_);
                        lean_dec_ref(v___x_2852_);
                        v___x_2854_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2854_, 0, v___x_2853_);
                        return v___x_2854_;
                    }
                } else {
                    v___x_2855_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__23;
                    v___x_2856_ = l_Lean_Expr_getAppFn(v_lhs_2790_);
                    v___x_2857_ = l_Lean_Expr_constLevels_x21(v___x_2856_);
                    lean_dec_ref(v___x_2856_);
                    v___x_2858_ = l_Lean_mkConst(v___x_2855_, v___x_2857_);
                    v_dummy_2859_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
                    v_nargs_2860_ = l_Lean_Expr_getAppNumArgs(v_lhs_2790_);
                    lean_inc(v_nargs_2860_);
                    v___x_2861_ = lean_mk_array(v_nargs_2860_, v_dummy_2859_);
                    v___x_2862_ = lean_unsigned_to_nat(1);
                    v___x_2863_ = lean_nat_sub(v_nargs_2860_, v___x_2862_);
                    lean_dec(v_nargs_2860_);
                    v___x_2864_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_lhs_2790_,
                        v___x_2861_,
                        v___x_2863_,
                    );
                    v___x_2865_ = l_Lean_mkAppN(v___x_2858_, v___x_2864_);
                    lean_dec_ref(v___x_2864_);
                    v___x_2866_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2866_, 0, v___x_2865_);
                    return v___x_2866_;
                }
            }
            1 => {
                v___x_2816_ = l_Lean_mkLambda(v___x_2812_, v___x_2813_, v_a_2809_, v___y_2815_);
                v___x_2817_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
                v___x_2818_ = lean_unsigned_to_nat(2);
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
    mut v_lhs_2867_: *mut LeanObject,
    mut v_a_2868_: *mut LeanObject,
    mut v_a_2869_: *mut LeanObject,
    mut v_a_2870_: *mut LeanObject,
    mut v_a_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2873_: *mut LeanObject = core::ptr::null_mut();
    v_res_2873_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v_lhs_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
    lean_dec(v_a_2871_);
    lean_dec_ref(v_a_2870_);
    lean_dec(v_a_2869_);
    lean_dec_ref(v_a_2868_);
    return v_res_2873_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(
    mut v_00_u03b1_2874_: *mut LeanObject,
    mut v_msg_2875_: *mut LeanObject,
    mut v___y_2876_: *mut LeanObject,
    mut v___y_2877_: *mut LeanObject,
    mut v___y_2878_: *mut LeanObject,
    mut v___y_2879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    v___x_2881_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v_msg_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
    return v___x_2881_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___boxed(
    mut v_00_u03b1_2882_: *mut LeanObject,
    mut v_msg_2883_: *mut LeanObject,
    mut v___y_2884_: *mut LeanObject,
    mut v___y_2885_: *mut LeanObject,
    mut v___y_2886_: *mut LeanObject,
    mut v___y_2887_: *mut LeanObject,
    mut v___y_2888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2889_: *mut LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0(v_00_u03b1_2882_, v_msg_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    lean_dec(v___y_2887_);
    lean_dec_ref(v___y_2886_);
    lean_dec(v___y_2885_);
    lean_dec_ref(v___y_2884_);
    return v_res_2889_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(
    mut v_msg_2891_: *mut LeanObject,
    mut v___y_2892_: *mut LeanObject,
    mut v___y_2893_: *mut LeanObject,
    mut v___y_2894_: *mut LeanObject,
    mut v___y_2895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534__overap_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    v___f_2897_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___closed__0;
    v___x_1534__overap_2898_ = lean_panic_fn_borrowed(v___f_2897_, v_msg_2891_);
    lean_inc(v___y_2895_);
    lean_inc_ref(v___y_2894_);
    lean_inc(v___y_2893_);
    lean_inc_ref(v___y_2892_);
    v___x_2899_ = lean_apply_5(
        v___x_1534__overap_2898_,
        v___y_2892_,
        v___y_2893_,
        v___y_2894_,
        v___y_2895_,
        lean_box(0),
    );
    return v___x_2899_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0___boxed(
    mut v_msg_2900_: *mut LeanObject,
    mut v___y_2901_: *mut LeanObject,
    mut v___y_2902_: *mut LeanObject,
    mut v___y_2903_: *mut LeanObject,
    mut v___y_2904_: *mut LeanObject,
    mut v___y_2905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2906_: *mut LeanObject = core::ptr::null_mut();
    v_res_2906_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v_msg_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
    lean_dec(v___y_2904_);
    lean_dec_ref(v___y_2903_);
    lean_dec(v___y_2902_);
    lean_dec_ref(v___y_2901_);
    return v_res_2906_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_2907_: *mut LeanObject,
    mut v_x_2908_: *mut LeanObject,
    mut v_x_2909_: *mut LeanObject,
    mut v_x_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2911_ = lean_ctor_get(v_x_2907_, 0);
                v_vs_2912_ = lean_ctor_get(v_x_2907_, 1);
                v_isSharedCheck_2936_ = (!lean_is_exclusive(v_x_2907_)) as u8;
                if v_isSharedCheck_2936_ == 0 {
                    v___x_2914_ = v_x_2907_;
                    v_isShared_2915_ = v_isSharedCheck_2936_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2912_);
                    lean_inc(v_ks_2911_);
                    lean_dec(v_x_2907_);
                    v___x_2914_ = lean_box(0);
                    v_isShared_2915_ = v_isSharedCheck_2936_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2916_ = lean_array_get_size(v_ks_2911_);
                v___x_2917_ = lean_nat_dec_lt(v_x_2908_, v___x_2916_);
                if v___x_2917_ == 0 {
                    lean_dec(v_x_2908_);
                    v___x_2918_ = lean_array_push(v_ks_2911_, v_x_2909_);
                    v___x_2919_ = lean_array_push(v_vs_2912_, v_x_2910_);
                    if v_isShared_2915_ == 0 {
                        lean_ctor_set(v___x_2914_, 1, v___x_2919_);
                        lean_ctor_set(v___x_2914_, 0, v___x_2918_);
                        v___x_2921_ = v___x_2914_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2918_);
                        lean_ctor_set(v_reuseFailAlloc_2922_, 1, v___x_2919_);
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
                            v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_ks_2911_);
                            lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_vs_2912_);
                            v___x_2926_ = v_reuseFailAlloc_2930_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2931_ = lean_array_fset(v_ks_2911_, v_x_2908_, v_x_2909_);
                        v___x_2932_ = lean_array_fset(v_vs_2912_, v_x_2908_, v_x_2910_);
                        lean_dec(v_x_2908_);
                        if v_isShared_2915_ == 0 {
                            lean_ctor_set(v___x_2914_, 1, v___x_2932_);
                            lean_ctor_set(v___x_2914_, 0, v___x_2931_);
                            v___x_2934_ = v___x_2914_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2931_);
                            lean_ctor_set(v_reuseFailAlloc_2935_, 1, v___x_2932_);
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
                v___x_2927_ = lean_unsigned_to_nat(1);
                v___x_2928_ = lean_nat_add(v_x_2908_, v___x_2927_);
                lean_dec(v_x_2908_);
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
    mut v_n_2937_: *mut LeanObject,
    mut v_k_2938_: *mut LeanObject,
    mut v_v_2939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    v___x_2940_ = lean_unsigned_to_nat(0);
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
    v___x_2946_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__0);
    v___x_2947_ = lean_usize_sub(v___x_2946_, v___x_2945_);
    return v___x_2947_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    v___x_2948_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2948_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(
    mut v_x_2949_: *mut LeanObject,
    mut v_x_2950_: usize,
    mut v_x_2951_: usize,
    mut v_x_2952_: *mut LeanObject,
    mut v_x_2953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: usize = 0;
    let mut v___x_2956_: usize = 0;
    let mut v___x_2957_: usize = 0;
    let mut v___x_2958_: usize = 0;
    let mut v_j_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: u8 = 0;
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v_v_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2979_: u8 = 0;
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_node_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2989_: u8 = 0;
    let mut v___x_2990_: usize = 0;
    let mut v___x_2991_: usize = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2998_: u8 = 0;
    let mut v_unused_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3004_: u8 = 0;
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3009_: u8 = 0;
    let mut v_ks_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: usize = 0;
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v_reuseFailAlloc_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2949_) == 0 {
                    v_es_2954_ = lean_ctor_get(v_x_2949_, 0);
                    v___x_2955_ = 5usize;
                    v___x_2956_ = 1usize;
                    v___x_2957_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__1);
                    v___x_2958_ = lean_usize_land(v_x_2950_, v___x_2957_);
                    v_j_2959_ = lean_usize_to_nat(v___x_2958_);
                    v___x_2960_ = lean_array_get_size(v_es_2954_);
                    v___x_2961_ = lean_nat_dec_lt(v_j_2959_, v___x_2960_);
                    if v___x_2961_ == 0 {
                        lean_dec(v_j_2959_);
                        lean_dec(v_x_2953_);
                        lean_dec(v_x_2952_);
                        return v_x_2949_;
                    } else {
                        lean_inc_ref(v_es_2954_);
                        v_isSharedCheck_2998_ = (!lean_is_exclusive(v_x_2949_)) as u8;
                        if v_isSharedCheck_2998_ == 0 {
                            v_unused_2999_ = lean_ctor_get(v_x_2949_, 0);
                            lean_dec(v_unused_2999_);
                            v___x_2963_ = v_x_2949_;
                            v_isShared_2964_ = v_isSharedCheck_2998_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2949_);
                            v___x_2963_ = lean_box(0);
                            v_isShared_2964_ = v_isSharedCheck_2998_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3000_ = lean_ctor_get(v_x_2949_, 0);
                    v_vs_3001_ = lean_ctor_get(v_x_2949_, 1);
                    v_isSharedCheck_3021_ = (!lean_is_exclusive(v_x_2949_)) as u8;
                    if v_isSharedCheck_3021_ == 0 {
                        v___x_3003_ = v_x_2949_;
                        v_isShared_3004_ = v_isSharedCheck_3021_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3001_);
                        lean_inc(v_ks_3000_);
                        lean_dec(v_x_2949_);
                        v___x_3003_ = lean_box(0);
                        v_isShared_3004_ = v_isSharedCheck_3021_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2965_ = lean_array_fget(v_es_2954_, v_j_2959_);
                v___x_2966_ = lean_box(0);
                v_xs_x27_2967_ = lean_array_fset(v_es_2954_, v_j_2959_, v___x_2966_);
                match lean_obj_tag(v_v_2965_) {
                    0 => {
                        v_key_2974_ = lean_ctor_get(v_v_2965_, 0);
                        v_val_2975_ = lean_ctor_get(v_v_2965_, 1);
                        v_isSharedCheck_2985_ = (!lean_is_exclusive(v_v_2965_)) as u8;
                        if v_isSharedCheck_2985_ == 0 {
                            v___x_2977_ = v_v_2965_;
                            v_isShared_2978_ = v_isSharedCheck_2985_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2975_);
                            lean_inc(v_key_2974_);
                            lean_dec(v_v_2965_);
                            v___x_2977_ = lean_box(0);
                            v_isShared_2978_ = v_isSharedCheck_2985_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2986_ = lean_ctor_get(v_v_2965_, 0);
                        v_isSharedCheck_2996_ = (!lean_is_exclusive(v_v_2965_)) as u8;
                        if v_isSharedCheck_2996_ == 0 {
                            v___x_2988_ = v_v_2965_;
                            v_isShared_2989_ = v_isSharedCheck_2996_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2986_);
                            lean_dec(v_v_2965_);
                            v___x_2988_ = lean_box(0);
                            v_isShared_2989_ = v_isSharedCheck_2996_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2997_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2997_, 0, v_x_2952_);
                        lean_ctor_set(v___x_2997_, 1, v_x_2953_);
                        v___y_2969_ = v___x_2997_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2970_ = lean_array_fset(v_xs_x27_2967_, v_j_2959_, v___y_2969_);
                lean_dec(v_j_2959_);
                if v_isShared_2964_ == 0 {
                    lean_ctor_set(v___x_2963_, 0, v___x_2970_);
                    v___x_2972_ = v___x_2963_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
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
                    lean_del_object(v___x_2977_);
                    v___x_2980_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2974_,
                        v_val_2975_,
                        v_x_2952_,
                        v_x_2953_,
                    );
                    v___x_2981_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2981_, 0, v___x_2980_);
                    v___y_2969_ = v___x_2981_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2975_);
                    lean_dec(v_key_2974_);
                    if v_isShared_2978_ == 0 {
                        lean_ctor_set(v___x_2977_, 1, v_x_2953_);
                        lean_ctor_set(v___x_2977_, 0, v_x_2952_);
                        v___x_2983_ = v___x_2977_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_x_2952_);
                        lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_x_2953_);
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
                    lean_ctor_set(v___x_2988_, 0, v___x_2992_);
                    v___x_2994_ = v___x_2988_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
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
                    v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_ks_3000_);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_vs_3001_);
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
                    v___x_3018_ = lean_unsigned_to_nat(4);
                    v___x_3019_ = lean_nat_dec_lt(v___x_3017_, v___x_3018_);
                    lean_dec(v___x_3017_);
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
                    v_ks_3010_ = lean_ctor_get(v_newNode_3007_, 0);
                    lean_inc_ref(v_ks_3010_);
                    v_vs_3011_ = lean_ctor_get(v_newNode_3007_, 1);
                    lean_inc_ref(v_vs_3011_);
                    lean_dec_ref(v_newNode_3007_);
                    v___x_3012_ = lean_unsigned_to_nat(0);
                    v___x_3013_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___closed__2);
                    v___x_3014_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_x_2951_, v_ks_3010_, v_vs_3011_, v___x_3012_, v___x_3013_);
                    lean_dec_ref(v_vs_3011_);
                    lean_dec_ref(v_ks_3010_);
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
    mut v_keys_3023_: *mut LeanObject,
    mut v_vals_3024_: *mut LeanObject,
    mut v_i_3025_: *mut LeanObject,
    mut v_entries_3026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v_k_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: u64 = 0;
    let mut v_h_3032_: usize = 0;
    let mut v___x_3033_: usize = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: usize = 0;
    let mut v___x_3036_: usize = 0;
    let mut v___x_3037_: usize = 0;
    let mut v_h_3038_: usize = 0;
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3027_ = lean_array_get_size(v_keys_3023_);
                v___x_3028_ = lean_nat_dec_lt(v_i_3025_, v___x_3027_);
                if v___x_3028_ == 0 {
                    lean_dec(v_i_3025_);
                    return v_entries_3026_;
                } else {
                    v_k_3029_ = lean_array_fget_borrowed(v_keys_3023_, v_i_3025_);
                    v_v_3030_ = lean_array_fget_borrowed(v_vals_3024_, v_i_3025_);
                    v___x_3031_ = l_Lean_instHashableMVarId_hash(v_k_3029_);
                    v_h_3032_ = lean_uint64_to_usize(v___x_3031_);
                    v___x_3033_ = 5usize;
                    v___x_3034_ = lean_unsigned_to_nat(1);
                    v___x_3035_ = 1usize;
                    v___x_3036_ = lean_usize_sub(v_depth_3022_, v___x_3035_);
                    v___x_3037_ = lean_usize_mul(v___x_3033_, v___x_3036_);
                    v_h_3038_ = lean_usize_shift_right(v_h_3032_, v___x_3037_);
                    v___x_3039_ = lean_nat_add(v_i_3025_, v___x_3034_);
                    lean_dec(v_i_3025_);
                    lean_inc(v_v_3030_);
                    lean_inc(v_k_3029_);
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
    mut v_depth_3042_: *mut LeanObject,
    mut v_keys_3043_: *mut LeanObject,
    mut v_vals_3044_: *mut LeanObject,
    mut v_i_3045_: *mut LeanObject,
    mut v_entries_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3047_: usize = 0;
    let mut v_res_3048_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3047_ = lean_unbox_usize(v_depth_3042_);
    lean_dec(v_depth_3042_);
    v_res_3048_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_3047_, v_keys_3043_, v_vals_3044_, v_i_3045_, v_entries_3046_);
    lean_dec_ref(v_vals_3044_);
    lean_dec_ref(v_keys_3043_);
    return v_res_3048_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_x_3049_: *mut LeanObject,
    mut v_x_3050_: *mut LeanObject,
    mut v_x_3051_: *mut LeanObject,
    mut v_x_3052_: *mut LeanObject,
    mut v_x_3053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2123__boxed_3054_: usize = 0;
    let mut v_x_2124__boxed_3055_: usize = 0;
    let mut v_res_3056_: *mut LeanObject = core::ptr::null_mut();
    v_x_2123__boxed_3054_ = lean_unbox_usize(v_x_3050_);
    lean_dec(v_x_3050_);
    v_x_2124__boxed_3055_ = lean_unbox_usize(v_x_3051_);
    lean_dec(v_x_3051_);
    v_res_3056_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_3049_, v_x_2123__boxed_3054_, v_x_2124__boxed_3055_, v_x_3052_, v_x_3053_);
    return v_res_3056_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(
    mut v_x_3057_: *mut LeanObject,
    mut v_x_3058_: *mut LeanObject,
    mut v_x_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3060_: u64 = 0;
    let mut v___x_3061_: usize = 0;
    let mut v___x_3062_: usize = 0;
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    v___x_3060_ = l_Lean_instHashableMVarId_hash(v_x_3058_);
    v___x_3061_ = lean_uint64_to_usize(v___x_3060_);
    v___x_3062_ = 1usize;
    v___x_3063_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_3057_, v___x_3061_, v___x_3062_, v_x_3058_, v_x_3059_);
    return v___x_3063_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(
    mut v_mvarId_3064_: *mut LeanObject,
    mut v_val_3065_: *mut LeanObject,
    mut v___y_3066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v_depth_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3100_: u8 = 0;
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3068_ = lean_st_ref_take(v___y_3066_);
                v_mctx_3069_ = lean_ctor_get(v___x_3068_, 0);
                v_cache_3070_ = lean_ctor_get(v___x_3068_, 1);
                v_zetaDeltaFVarIds_3071_ = lean_ctor_get(v___x_3068_, 2);
                v_postponed_3072_ = lean_ctor_get(v___x_3068_, 3);
                v_diag_3073_ = lean_ctor_get(v___x_3068_, 4);
                v_isSharedCheck_3101_ = (!lean_is_exclusive(v___x_3068_)) as u8;
                if v_isSharedCheck_3101_ == 0 {
                    v___x_3075_ = v___x_3068_;
                    v_isShared_3076_ = v_isSharedCheck_3101_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3073_);
                    lean_inc(v_postponed_3072_);
                    lean_inc(v_zetaDeltaFVarIds_3071_);
                    lean_inc(v_cache_3070_);
                    lean_inc(v_mctx_3069_);
                    lean_dec(v___x_3068_);
                    v___x_3075_ = lean_box(0);
                    v_isShared_3076_ = v_isSharedCheck_3101_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3077_ = lean_ctor_get(v_mctx_3069_, 0);
                v_levelAssignDepth_3078_ = lean_ctor_get(v_mctx_3069_, 1);
                v_lmvarCounter_3079_ = lean_ctor_get(v_mctx_3069_, 2);
                v_mvarCounter_3080_ = lean_ctor_get(v_mctx_3069_, 3);
                v_lDecls_3081_ = lean_ctor_get(v_mctx_3069_, 4);
                v_decls_3082_ = lean_ctor_get(v_mctx_3069_, 5);
                v_userNames_3083_ = lean_ctor_get(v_mctx_3069_, 6);
                v_lAssignment_3084_ = lean_ctor_get(v_mctx_3069_, 7);
                v_eAssignment_3085_ = lean_ctor_get(v_mctx_3069_, 8);
                v_dAssignment_3086_ = lean_ctor_get(v_mctx_3069_, 9);
                v_isSharedCheck_3100_ = (!lean_is_exclusive(v_mctx_3069_)) as u8;
                if v_isSharedCheck_3100_ == 0 {
                    v___x_3088_ = v_mctx_3069_;
                    v_isShared_3089_ = v_isSharedCheck_3100_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_3086_);
                    lean_inc(v_eAssignment_3085_);
                    lean_inc(v_lAssignment_3084_);
                    lean_inc(v_userNames_3083_);
                    lean_inc(v_decls_3082_);
                    lean_inc(v_lDecls_3081_);
                    lean_inc(v_mvarCounter_3080_);
                    lean_inc(v_lmvarCounter_3079_);
                    lean_inc(v_levelAssignDepth_3078_);
                    lean_inc(v_depth_3077_);
                    lean_dec(v_mctx_3069_);
                    v___x_3088_ = lean_box(0);
                    v_isShared_3089_ = v_isSharedCheck_3100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3090_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_eAssignment_3085_, v_mvarId_3064_, v_val_3065_);
                if v_isShared_3089_ == 0 {
                    lean_ctor_set(v___x_3088_, 8, v___x_3090_);
                    v___x_3092_ = v___x_3088_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_depth_3077_);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_levelAssignDepth_3078_);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_lmvarCounter_3079_);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 3, v_mvarCounter_3080_);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 4, v_lDecls_3081_);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 5, v_decls_3082_);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 6, v_userNames_3083_);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 7, v_lAssignment_3084_);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 8, v___x_3090_);
                    lean_ctor_set(v_reuseFailAlloc_3099_, 9, v_dAssignment_3086_);
                    v___x_3092_ = v_reuseFailAlloc_3099_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3076_ == 0 {
                    lean_ctor_set(v___x_3075_, 0, v___x_3092_);
                    v___x_3094_ = v___x_3075_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3092_);
                    lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_cache_3070_);
                    lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_zetaDeltaFVarIds_3071_);
                    lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_postponed_3072_);
                    lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_diag_3073_);
                    v___x_3094_ = v_reuseFailAlloc_3098_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3095_ = lean_st_ref_set(v___y_3066_, v___x_3094_);
                v___x_3096_ = lean_box(0);
                v___x_3097_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3097_, 0, v___x_3096_);
                return v___x_3097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg___boxed(
    mut v_mvarId_3102_: *mut LeanObject,
    mut v_val_3103_: *mut LeanObject,
    mut v___y_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3106_: *mut LeanObject = core::ptr::null_mut();
    v_res_3106_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_3102_, v_val_3103_, v___y_3104_);
    lean_dec(v___y_3104_);
    return v_res_3106_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    v___x_3110_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2;
    v___x_3111_ = lean_unsigned_to_nat(41);
    v___x_3112_ = lean_unsigned_to_nat(70);
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
-> *mut LeanObject {
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    v___x_3116_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2;
    v___x_3117_ = lean_unsigned_to_nat(51);
    v___x_3118_ = lean_unsigned_to_nat(72);
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
    mut v_mvarId_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
    mut v___y_3126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: u8 = 0;
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut v_unused_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3170_: u8 = 0;
    let mut v_a_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3178_: u8 = 0;
    let mut v_a_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3182_: u8 = 0;
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_a_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v_a_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_a_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_3122_);
                v___x_3128_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_3122_,
                    v___y_3123_,
                    v___y_3124_,
                    v___y_3125_,
                    v___y_3126_,
                );
                if lean_obj_tag(v___x_3128_) == 0 {
                    v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
                    lean_inc(v_a_3129_);
                    lean_dec_ref_known(v___x_3128_, 1);
                    v___x_3130_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1;
                    v___x_3131_ = lean_unsigned_to_nat(3);
                    v___x_3132_ = l_Lean_Expr_isAppOfArity(v_a_3129_, v___x_3130_, v___x_3131_);
                    if v___x_3132_ == 0 {
                        lean_dec(v_a_3129_);
                        lean_dec(v_mvarId_3122_);
                        v___x_3133_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
                        v___x_3134_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_3133_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
                        lean_dec(v___y_3126_);
                        lean_dec_ref(v___y_3125_);
                        lean_dec(v___y_3124_);
                        lean_dec_ref(v___y_3123_);
                        return v___x_3134_;
                    } else {
                        v___x_3135_ = l_Lean_Expr_appFn_x21(v_a_3129_);
                        v___x_3136_ = l_Lean_Expr_appArg_x21(v___x_3135_);
                        lean_dec_ref(v___x_3135_);
                        v___x_3137_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder(v___x_3136_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
                        if lean_obj_tag(v___x_3137_) == 0 {
                            v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
                            lean_inc_n(v_a_3138_, 2);
                            lean_dec_ref_known(v___x_3137_, 1);
                            lean_inc(v___y_3126_);
                            lean_inc_ref(v___y_3125_);
                            lean_inc(v___y_3124_);
                            lean_inc_ref(v___y_3123_);
                            v___x_3139_ = lean_infer_type(
                                v_a_3138_,
                                v___y_3123_,
                                v___y_3124_,
                                v___y_3125_,
                                v___y_3126_,
                            );
                            if lean_obj_tag(v___x_3139_) == 0 {
                                v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
                                lean_inc(v_a_3140_);
                                lean_dec_ref_known(v___x_3139_, 1);
                                v___x_3141_ =
                                    l_Lean_Expr_isAppOfArity(v_a_3140_, v___x_3130_, v___x_3131_);
                                if v___x_3141_ == 0 {
                                    lean_dec(v_a_3140_);
                                    lean_dec(v_a_3138_);
                                    lean_dec(v_a_3129_);
                                    lean_dec(v_mvarId_3122_);
                                    v___x_3142_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4);
                                    v___x_3143_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__0(v___x_3142_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
                                    lean_dec(v___y_3126_);
                                    lean_dec_ref(v___y_3125_);
                                    lean_dec(v___y_3124_);
                                    lean_dec_ref(v___y_3123_);
                                    return v___x_3143_;
                                } else {
                                    v___x_3144_ = l_Lean_Expr_appArg_x21(v_a_3129_);
                                    lean_dec(v_a_3129_);
                                    v___x_3145_ = l_Lean_Expr_appArg_x21(v_a_3140_);
                                    lean_dec(v_a_3140_);
                                    v___x_3146_ = l_Lean_Meta_mkEq(
                                        v___x_3145_,
                                        v___x_3144_,
                                        v___y_3123_,
                                        v___y_3124_,
                                        v___y_3125_,
                                        v___y_3126_,
                                    );
                                    if lean_obj_tag(v___x_3146_) == 0 {
                                        v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
                                        lean_inc(v_a_3147_);
                                        lean_dec_ref_known(v___x_3146_, 1);
                                        v___x_3148_ = lean_box(0);
                                        v___x_3149_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                            v_a_3147_,
                                            v___x_3148_,
                                            v___y_3123_,
                                            v___y_3124_,
                                            v___y_3125_,
                                            v___y_3126_,
                                        );
                                        if lean_obj_tag(v___x_3149_) == 0 {
                                            v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
                                            lean_inc_n(v_a_3150_, 2);
                                            lean_dec_ref_known(v___x_3149_, 1);
                                            v___x_3151_ = l_Lean_Meta_mkEqTrans(
                                                v_a_3138_,
                                                v_a_3150_,
                                                v___y_3123_,
                                                v___y_3124_,
                                                v___y_3125_,
                                                v___y_3126_,
                                            );
                                            lean_dec(v___y_3126_);
                                            lean_dec_ref(v___y_3125_);
                                            lean_dec_ref(v___y_3123_);
                                            if lean_obj_tag(v___x_3151_) == 0 {
                                                v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
                                                lean_inc(v_a_3152_);
                                                lean_dec_ref_known(v___x_3151_, 1);
                                                v___x_3153_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_3122_, v_a_3152_, v___y_3124_);
                                                lean_dec(v___y_3124_);
                                                v_isSharedCheck_3161_ =
                                                    (!lean_is_exclusive(v___x_3153_)) as u8;
                                                if v_isSharedCheck_3161_ == 0 {
                                                    v_unused_3162_ = lean_ctor_get(v___x_3153_, 0);
                                                    lean_dec(v_unused_3162_);
                                                    v___x_3155_ = v___x_3153_;
                                                    v_isShared_3156_ = v_isSharedCheck_3161_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec(v___x_3153_);
                                                    v___x_3155_ = lean_box(0);
                                                    v_isShared_3156_ = v_isSharedCheck_3161_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_a_3150_);
                                                lean_dec(v___y_3124_);
                                                lean_dec(v_mvarId_3122_);
                                                v_a_3163_ = lean_ctor_get(v___x_3151_, 0);
                                                v_isSharedCheck_3170_ =
                                                    (!lean_is_exclusive(v___x_3151_)) as u8;
                                                if v_isSharedCheck_3170_ == 0 {
                                                    v___x_3165_ = v___x_3151_;
                                                    v_isShared_3166_ = v_isSharedCheck_3170_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3163_);
                                                    lean_dec(v___x_3151_);
                                                    v___x_3165_ = lean_box(0);
                                                    v_isShared_3166_ = v_isSharedCheck_3170_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_3138_);
                                            lean_dec(v___y_3126_);
                                            lean_dec_ref(v___y_3125_);
                                            lean_dec(v___y_3124_);
                                            lean_dec_ref(v___y_3123_);
                                            lean_dec(v_mvarId_3122_);
                                            v_a_3171_ = lean_ctor_get(v___x_3149_, 0);
                                            v_isSharedCheck_3178_ =
                                                (!lean_is_exclusive(v___x_3149_)) as u8;
                                            if v_isSharedCheck_3178_ == 0 {
                                                v___x_3173_ = v___x_3149_;
                                                v_isShared_3174_ = v_isSharedCheck_3178_;
                                                state = 5;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3171_);
                                                lean_dec(v___x_3149_);
                                                v___x_3173_ = lean_box(0);
                                                v_isShared_3174_ = v_isSharedCheck_3178_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_3138_);
                                        lean_dec(v___y_3126_);
                                        lean_dec_ref(v___y_3125_);
                                        lean_dec(v___y_3124_);
                                        lean_dec_ref(v___y_3123_);
                                        lean_dec(v_mvarId_3122_);
                                        v_a_3179_ = lean_ctor_get(v___x_3146_, 0);
                                        v_isSharedCheck_3186_ =
                                            (!lean_is_exclusive(v___x_3146_)) as u8;
                                        if v_isSharedCheck_3186_ == 0 {
                                            v___x_3181_ = v___x_3146_;
                                            v_isShared_3182_ = v_isSharedCheck_3186_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3179_);
                                            lean_dec(v___x_3146_);
                                            v___x_3181_ = lean_box(0);
                                            v_isShared_3182_ = v_isSharedCheck_3186_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_a_3138_);
                                lean_dec(v_a_3129_);
                                lean_dec(v___y_3126_);
                                lean_dec_ref(v___y_3125_);
                                lean_dec(v___y_3124_);
                                lean_dec_ref(v___y_3123_);
                                lean_dec(v_mvarId_3122_);
                                v_a_3187_ = lean_ctor_get(v___x_3139_, 0);
                                v_isSharedCheck_3194_ = (!lean_is_exclusive(v___x_3139_)) as u8;
                                if v_isSharedCheck_3194_ == 0 {
                                    v___x_3189_ = v___x_3139_;
                                    v_isShared_3190_ = v_isSharedCheck_3194_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_3187_);
                                    lean_dec(v___x_3139_);
                                    v___x_3189_ = lean_box(0);
                                    v_isShared_3190_ = v_isSharedCheck_3194_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3129_);
                            lean_dec(v___y_3126_);
                            lean_dec_ref(v___y_3125_);
                            lean_dec(v___y_3124_);
                            lean_dec_ref(v___y_3123_);
                            lean_dec(v_mvarId_3122_);
                            v_a_3195_ = lean_ctor_get(v___x_3137_, 0);
                            v_isSharedCheck_3202_ = (!lean_is_exclusive(v___x_3137_)) as u8;
                            if v_isSharedCheck_3202_ == 0 {
                                v___x_3197_ = v___x_3137_;
                                v_isShared_3198_ = v_isSharedCheck_3202_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_3195_);
                                lean_dec(v___x_3137_);
                                v___x_3197_ = lean_box(0);
                                v_isShared_3198_ = v_isSharedCheck_3202_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___y_3126_);
                    lean_dec_ref(v___y_3125_);
                    lean_dec(v___y_3124_);
                    lean_dec_ref(v___y_3123_);
                    lean_dec(v_mvarId_3122_);
                    v_a_3203_ = lean_ctor_get(v___x_3128_, 0);
                    v_isSharedCheck_3210_ = (!lean_is_exclusive(v___x_3128_)) as u8;
                    if v_isSharedCheck_3210_ == 0 {
                        v___x_3205_ = v___x_3128_;
                        v_isShared_3206_ = v_isSharedCheck_3210_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3203_);
                        lean_dec(v___x_3128_);
                        v___x_3205_ = lean_box(0);
                        v_isShared_3206_ = v_isSharedCheck_3210_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3157_ = l_Lean_Expr_mvarId_x21(v_a_3150_);
                lean_dec(v_a_3150_);
                if v_isShared_3156_ == 0 {
                    lean_ctor_set(v___x_3155_, 0, v___x_3157_);
                    v___x_3159_ = v___x_3155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
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
                    v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
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
                    v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
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
                    v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
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
                    v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
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
                    v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
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
                    v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
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
    mut v_mvarId_3211_: *mut LeanObject,
    mut v___y_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
    mut v___y_3215_: *mut LeanObject,
    mut v___y_3216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3217_: *mut LeanObject = core::ptr::null_mut();
    v_res_3217_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(v_mvarId_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
    return v_res_3217_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(
    mut v_mvarId_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
    mut v_a_3220_: *mut LeanObject,
    mut v_a_3221_: *mut LeanObject,
    mut v_a_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_3218_);
    v___f_3224_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___boxed as *mut core::ffi::c_void, 6, 1);
    lean_closure_set(v___f_3224_, 0, v_mvarId_3218_);
    v___x_3225_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix_spec__0___redArg(v_mvarId_3218_, v___f_3224_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
    return v___x_3225_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___boxed(
    mut v_mvarId_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
    mut v_a_3228_: *mut LeanObject,
    mut v_a_3229_: *mut LeanObject,
    mut v_a_3230_: *mut LeanObject,
    mut v_a_3231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3232_: *mut LeanObject = core::ptr::null_mut();
    v_res_3232_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(v_mvarId_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
    lean_dec(v_a_3230_);
    lean_dec_ref(v_a_3229_);
    lean_dec(v_a_3228_);
    lean_dec_ref(v_a_3227_);
    return v_res_3232_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(
    mut v_mvarId_3233_: *mut LeanObject,
    mut v_val_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    v___x_3240_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___redArg(v_mvarId_3233_, v_val_3234_, v___y_3236_);
    return v___x_3240_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1___boxed(
    mut v_mvarId_3241_: *mut LeanObject,
    mut v_val_3242_: *mut LeanObject,
    mut v___y_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3248_: *mut LeanObject = core::ptr::null_mut();
    v_res_3248_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1(v_mvarId_3241_, v_val_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
    lean_dec(v___y_3246_);
    lean_dec_ref(v___y_3245_);
    lean_dec(v___y_3244_);
    lean_dec_ref(v___y_3243_);
    return v_res_3248_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1(
    mut v_00_u03b2_3249_: *mut LeanObject,
    mut v_x_3250_: *mut LeanObject,
    mut v_x_3251_: *mut LeanObject,
    mut v_x_3252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    v___x_3253_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1___redArg(v_x_3250_, v_x_3251_, v_x_3252_);
    return v___x_3253_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(
    mut v_00_u03b2_3254_: *mut LeanObject,
    mut v_x_3255_: *mut LeanObject,
    mut v_x_3256_: usize,
    mut v_x_3257_: usize,
    mut v_x_3258_: *mut LeanObject,
    mut v_x_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    v___x_3260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___redArg(v_x_3255_, v_x_3256_, v_x_3257_, v_x_3258_, v_x_3259_);
    return v___x_3260_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_3261_: *mut LeanObject,
    mut v_x_3262_: *mut LeanObject,
    mut v_x_3263_: *mut LeanObject,
    mut v_x_3264_: *mut LeanObject,
    mut v_x_3265_: *mut LeanObject,
    mut v_x_3266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2609__boxed_3267_: usize = 0;
    let mut v_x_2610__boxed_3268_: usize = 0;
    let mut v_res_3269_: *mut LeanObject = core::ptr::null_mut();
    v_x_2609__boxed_3267_ = lean_unbox_usize(v_x_3263_);
    lean_dec(v_x_3263_);
    v_x_2610__boxed_3268_ = lean_unbox_usize(v_x_3264_);
    lean_dec(v_x_3264_);
    v_res_3269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2(v_00_u03b2_3261_, v_x_3262_, v_x_2609__boxed_3267_, v_x_2610__boxed_3268_, v_x_3265_, v_x_3266_);
    return v_res_3269_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3270_: *mut LeanObject,
    mut v_n_3271_: *mut LeanObject,
    mut v_k_3272_: *mut LeanObject,
    mut v_v_3273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    v___x_3274_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3___redArg(v_n_3271_, v_k_3272_, v_v_3273_);
    return v___x_3274_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3275_: *mut LeanObject,
    mut v_depth_3276_: usize,
    mut v_keys_3277_: *mut LeanObject,
    mut v_vals_3278_: *mut LeanObject,
    mut v_heq_3279_: *mut LeanObject,
    mut v_i_3280_: *mut LeanObject,
    mut v_entries_3281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    v___x_3282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_3276_, v_keys_3277_, v_vals_3278_, v_i_3280_, v_entries_3281_);
    return v___x_3282_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3283_: *mut LeanObject,
    mut v_depth_3284_: *mut LeanObject,
    mut v_keys_3285_: *mut LeanObject,
    mut v_vals_3286_: *mut LeanObject,
    mut v_heq_3287_: *mut LeanObject,
    mut v_i_3288_: *mut LeanObject,
    mut v_entries_3289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3290_: usize = 0;
    let mut v_res_3291_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3290_ = lean_unbox_usize(v_depth_3284_);
    lean_dec(v_depth_3284_);
    v_res_3291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_3283_, v_depth_boxed_3290_, v_keys_3285_, v_vals_3286_, v_heq_3287_, v_i_3288_, v_entries_3289_);
    lean_dec_ref(v_vals_3286_);
    lean_dec_ref(v_keys_3285_);
    return v_res_3291_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_3292_: *mut LeanObject,
    mut v_x_3293_: *mut LeanObject,
    mut v_x_3294_: *mut LeanObject,
    mut v_x_3295_: *mut LeanObject,
    mut v_x_3296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    v___x_3297_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_3293_, v_x_3294_, v_x_3295_, v_x_3296_);
    return v___x_3297_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(
    mut v_opts_3298_: *mut LeanObject,
    mut v_opt_3299_: *mut LeanObject,
) -> u8 {
    let mut v_name_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    v_name_3300_ = lean_ctor_get(v_opt_3299_, 0);
    v_defValue_3301_ = lean_ctor_get(v_opt_3299_, 1);
    v_map_3302_ = lean_ctor_get(v_opts_3298_, 0);
    v___x_3303_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3302_,
            v_name_3300_,
        );
    if lean_obj_tag(v___x_3303_) == 0 {
        let mut v___x_3304_: u8 = 0;
        v___x_3304_ = (lean_unbox(v_defValue_3301_) as u8);
        return v___x_3304_;
    } else {
        let mut v_val_3305_: *mut LeanObject = core::ptr::null_mut();
        v_val_3305_ = lean_ctor_get(v___x_3303_, 0);
        lean_inc(v_val_3305_);
        lean_dec_ref_known(v___x_3303_, 1);
        if lean_obj_tag(v_val_3305_) == 1 {
            let mut v_v_3306_: u8 = 0;
            v_v_3306_ = lean_ctor_get_uint8(v_val_3305_, 0 as u32);
            lean_dec_ref_known(v_val_3305_, 0);
            return v_v_3306_;
        } else {
            let mut v___x_3307_: u8 = 0;
            lean_dec(v_val_3305_);
            v___x_3307_ = (lean_unbox(v_defValue_3301_) as u8);
            return v___x_3307_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2___boxed(
    mut v_opts_3308_: *mut LeanObject,
    mut v_opt_3309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3310_: u8 = 0;
    let mut v_r_3311_: *mut LeanObject = core::ptr::null_mut();
    v_res_3310_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v_opts_3308_, v_opt_3309_);
    lean_dec_ref(v_opt_3309_);
    lean_dec_ref(v_opts_3308_);
    v_r_3311_ = lean_box((v_res_3310_) as usize);
    return v_r_3311_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(
    mut v_opts_3312_: *mut LeanObject,
    mut v_opt_3313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    v_name_3314_ = lean_ctor_get(v_opt_3313_, 0);
    v_defValue_3315_ = lean_ctor_get(v_opt_3313_, 1);
    v_map_3316_ = lean_ctor_get(v_opts_3312_, 0);
    v___x_3317_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3316_,
            v_name_3314_,
        );
    if lean_obj_tag(v___x_3317_) == 0 {
        lean_inc(v_defValue_3315_);
        return v_defValue_3315_;
    } else {
        let mut v_val_3318_: *mut LeanObject = core::ptr::null_mut();
        v_val_3318_ = lean_ctor_get(v___x_3317_, 0);
        lean_inc(v_val_3318_);
        lean_dec_ref_known(v___x_3317_, 1);
        if lean_obj_tag(v_val_3318_) == 3 {
            let mut v_v_3319_: *mut LeanObject = core::ptr::null_mut();
            v_v_3319_ = lean_ctor_get(v_val_3318_, 0);
            lean_inc(v_v_3319_);
            lean_dec_ref_known(v_val_3318_, 1);
            return v_v_3319_;
        } else {
            lean_dec(v_val_3318_);
            lean_inc(v_defValue_3315_);
            return v_defValue_3315_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3___boxed(
    mut v_opts_3320_: *mut LeanObject,
    mut v_opt_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3322_: *mut LeanObject = core::ptr::null_mut();
    v_res_3322_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v_opts_3320_, v_opt_3321_);
    lean_dec_ref(v_opt_3321_);
    lean_dec_ref(v_opts_3320_);
    return v_res_3322_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(
    mut v_e_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3326_ = l_Lean_Expr_hasMVar(v_e_3323_);
                if v___x_3326_ == 0 {
                    v___x_3327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3327_, 0, v_e_3323_);
                    return v___x_3327_;
                } else {
                    v___x_3328_ = lean_st_ref_get(v___y_3324_);
                    v_mctx_3329_ = lean_ctor_get(v___x_3328_, 0);
                    lean_inc_ref(v_mctx_3329_);
                    lean_dec(v___x_3328_);
                    v___x_3330_ = l_Lean_instantiateMVarsCore(v_mctx_3329_, v_e_3323_);
                    v_fst_3331_ = lean_ctor_get(v___x_3330_, 0);
                    lean_inc(v_fst_3331_);
                    v_snd_3332_ = lean_ctor_get(v___x_3330_, 1);
                    lean_inc(v_snd_3332_);
                    lean_dec_ref(v___x_3330_);
                    v___x_3333_ = lean_st_ref_take(v___y_3324_);
                    v_cache_3334_ = lean_ctor_get(v___x_3333_, 1);
                    v_zetaDeltaFVarIds_3335_ = lean_ctor_get(v___x_3333_, 2);
                    v_postponed_3336_ = lean_ctor_get(v___x_3333_, 3);
                    v_diag_3337_ = lean_ctor_get(v___x_3333_, 4);
                    v_isSharedCheck_3346_ = (!lean_is_exclusive(v___x_3333_)) as u8;
                    if v_isSharedCheck_3346_ == 0 {
                        v_unused_3347_ = lean_ctor_get(v___x_3333_, 0);
                        lean_dec(v_unused_3347_);
                        v___x_3339_ = v___x_3333_;
                        v_isShared_3340_ = v_isSharedCheck_3346_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_3337_);
                        lean_inc(v_postponed_3336_);
                        lean_inc(v_zetaDeltaFVarIds_3335_);
                        lean_inc(v_cache_3334_);
                        lean_dec(v___x_3333_);
                        v___x_3339_ = lean_box(0);
                        v_isShared_3340_ = v_isSharedCheck_3346_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3340_ == 0 {
                    lean_ctor_set(v___x_3339_, 0, v_snd_3332_);
                    v___x_3342_ = v___x_3339_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_snd_3332_);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_cache_3334_);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 2, v_zetaDeltaFVarIds_3335_);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 3, v_postponed_3336_);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 4, v_diag_3337_);
                    v___x_3342_ = v_reuseFailAlloc_3345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3343_ = lean_st_ref_set(v___y_3324_, v___x_3342_);
                v___x_3344_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3344_, 0, v_fst_3331_);
                return v___x_3344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg___boxed(
    mut v_e_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3351_: *mut LeanObject = core::ptr::null_mut();
    v_res_3351_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_3348_, v___y_3349_);
    lean_dec(v___y_3349_);
    return v_res_3351_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(
    mut v_e_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    v___x_3358_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_e_3352_, v___y_3354_);
    return v___x_3358_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___boxed(
    mut v_e_3359_: *mut LeanObject,
    mut v___y_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3365_: *mut LeanObject = core::ptr::null_mut();
    v_res_3365_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4(v_e_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
    lean_dec(v___y_3363_);
    lean_dec_ref(v___y_3362_);
    lean_dec(v___y_3361_);
    lean_dec_ref(v___y_3360_);
    return v_res_3365_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(
    mut v_k_3366_: *mut LeanObject,
    mut v_allowLevelAssignments_3367_: u8,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3377_: u8 = 0;
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_a_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3385_: u8 = 0;
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    lean_box(0),
                    v_allowLevelAssignments_3367_,
                    v_k_3366_,
                    v___y_3368_,
                    v___y_3369_,
                    v___y_3370_,
                    v___y_3371_,
                );
                if lean_obj_tag(v___x_3373_) == 0 {
                    v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
                    v_isSharedCheck_3381_ = (!lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3381_ == 0 {
                        v___x_3376_ = v___x_3373_;
                        v_isShared_3377_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3374_);
                        lean_dec(v___x_3373_);
                        v___x_3376_ = lean_box(0);
                        v_isShared_3377_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3382_ = lean_ctor_get(v___x_3373_, 0);
                    v_isSharedCheck_3389_ = (!lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3389_ == 0 {
                        v___x_3384_ = v___x_3373_;
                        v_isShared_3385_ = v_isSharedCheck_3389_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3382_);
                        lean_dec(v___x_3373_);
                        v___x_3384_ = lean_box(0);
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
                    v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
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
                    v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
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
    mut v_k_3390_: *mut LeanObject,
    mut v_allowLevelAssignments_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_3397_: u8 = 0;
    let mut v_res_3398_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3397_ = (lean_unbox(v_allowLevelAssignments_3391_) as u8);
    v_res_3398_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_3390_, v_allowLevelAssignments_boxed_3397_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
    lean_dec(v___y_3395_);
    lean_dec_ref(v___y_3394_);
    lean_dec(v___y_3393_);
    lean_dec_ref(v___y_3392_);
    return v_res_3398_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(
    mut v_00_u03b1_3399_: *mut LeanObject,
    mut v_k_3400_: *mut LeanObject,
    mut v_allowLevelAssignments_3401_: u8,
    mut v___y_3402_: *mut LeanObject,
    mut v___y_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v_k_3400_, v_allowLevelAssignments_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
    return v___x_3407_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___boxed(
    mut v_00_u03b1_3408_: *mut LeanObject,
    mut v_k_3409_: *mut LeanObject,
    mut v_allowLevelAssignments_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
    mut v___y_3412_: *mut LeanObject,
    mut v___y_3413_: *mut LeanObject,
    mut v___y_3414_: *mut LeanObject,
    mut v___y_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_3416_: u8 = 0;
    let mut v_res_3417_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3416_ = (lean_unbox(v_allowLevelAssignments_3410_) as u8);
    v_res_3417_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6(v_00_u03b1_3408_, v_k_3409_, v_allowLevelAssignments_boxed_3416_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
    lean_dec(v___y_3414_);
    lean_dec_ref(v___y_3413_);
    lean_dec(v___y_3412_);
    lean_dec_ref(v___y_3411_);
    return v_res_3417_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(
    mut v_thm_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3427_: u8 = 0;
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3421_ = lean_st_ref_get(v___y_3419_);
                v_env_3422_ = lean_ctor_get(v___x_3421_, 0);
                lean_inc_ref_n(v_env_3422_, 2);
                lean_dec(v___x_3421_);
                v_toConstantVal_3423_ = lean_ctor_get(v_thm_3418_, 0);
                v_value_3424_ = lean_ctor_get(v_thm_3418_, 1);
                v_all_3425_ = lean_ctor_get(v_thm_3418_, 2);
                v_type_3435_ = lean_ctor_get(v_toConstantVal_3423_, 2);
                v___x_3436_ = l_Lean_Environment_hasUnsafe(v_env_3422_, v_type_3435_);
                if v___x_3436_ == 0 {
                    v___x_3437_ = l_Lean_Environment_hasUnsafe(v_env_3422_, v_value_3424_);
                    v___y_3427_ = v___x_3437_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_env_3422_);
                    v___y_3427_ = v___x_3436_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3427_ == 0 {
                    v___x_3428_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v___x_3428_, 0, v_thm_3418_);
                    v___x_3429_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3429_, 0, v___x_3428_);
                    return v___x_3429_;
                } else {
                    lean_inc(v_all_3425_);
                    lean_inc_ref(v_value_3424_);
                    lean_inc_ref(v_toConstantVal_3423_);
                    lean_dec_ref(v_thm_3418_);
                    v___x_3430_ = lean_box(0);
                    v___x_3431_ = 0;
                    v___x_3432_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v___x_3432_, 0, v_toConstantVal_3423_);
                    lean_ctor_set(v___x_3432_, 1, v_value_3424_);
                    lean_ctor_set(v___x_3432_, 2, v___x_3430_);
                    lean_ctor_set(v___x_3432_, 3, v_all_3425_);
                    lean_ctor_set_uint8(
                        v___x_3432_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v___x_3431_,
                    );
                    v___x_3433_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3433_, 0, v___x_3432_);
                    v___x_3434_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3434_, 0, v___x_3433_);
                    return v___x_3434_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg___boxed(
    mut v_thm_3438_: *mut LeanObject,
    mut v___y_3439_: *mut LeanObject,
    mut v___y_3440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3441_: *mut LeanObject = core::ptr::null_mut();
    v_res_3441_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_3438_, v___y_3439_);
    lean_dec(v___y_3439_);
    return v_res_3441_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(
    mut v_thm_3442_: *mut LeanObject,
    mut v___y_3443_: *mut LeanObject,
    mut v___y_3444_: *mut LeanObject,
    mut v___y_3445_: *mut LeanObject,
    mut v___y_3446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    v___x_3448_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v_thm_3442_, v___y_3446_);
    return v___x_3448_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___boxed(
    mut v_thm_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
    mut v___y_3452_: *mut LeanObject,
    mut v___y_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3455_: *mut LeanObject = core::ptr::null_mut();
    v_res_3455_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7(v_thm_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
    lean_dec(v___y_3453_);
    lean_dec_ref(v___y_3452_);
    lean_dec(v___y_3451_);
    lean_dec_ref(v___y_3450_);
    return v_res_3455_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(
    mut v_k_3456_: *mut LeanObject,
    mut v_b_3457_: *mut LeanObject,
    mut v_c_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
    mut v___y_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3462_);
    lean_inc_ref(v___y_3461_);
    lean_inc(v___y_3460_);
    lean_inc_ref(v___y_3459_);
    v___x_3464_ = lean_apply_7(
        v_k_3456_,
        v_b_3457_,
        v_c_3458_,
        v___y_3459_,
        v___y_3460_,
        v___y_3461_,
        v___y_3462_,
        lean_box(0),
    );
    return v___x_3464_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed(
    mut v_k_3465_: *mut LeanObject,
    mut v_b_3466_: *mut LeanObject,
    mut v_c_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
    mut v___y_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3473_: *mut LeanObject = core::ptr::null_mut();
    v_res_3473_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0(v_k_3465_, v_b_3466_, v_c_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
    lean_dec(v___y_3471_);
    lean_dec_ref(v___y_3470_);
    lean_dec(v___y_3469_);
    lean_dec_ref(v___y_3468_);
    return v_res_3473_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(
    mut v_e_3474_: *mut LeanObject,
    mut v_k_3475_: *mut LeanObject,
    mut v_cleanupAnnotations_3476_: u8,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: u8 = 0;
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3494_: u8 = 0;
    let mut v_a_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3482_ = lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_3482_, 0, v_k_3475_);
                v___x_3483_ = 1;
                v___x_3484_ = 0;
                v___x_3485_ = lean_box(0);
                v___x_3486_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_3486_) == 0 {
                    v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
                    v_isSharedCheck_3494_ = (!lean_is_exclusive(v___x_3486_)) as u8;
                    if v_isSharedCheck_3494_ == 0 {
                        v___x_3489_ = v___x_3486_;
                        v_isShared_3490_ = v_isSharedCheck_3494_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3487_);
                        lean_dec(v___x_3486_);
                        v___x_3489_ = lean_box(0);
                        v_isShared_3490_ = v_isSharedCheck_3494_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3495_ = lean_ctor_get(v___x_3486_, 0);
                    v_isSharedCheck_3502_ = (!lean_is_exclusive(v___x_3486_)) as u8;
                    if v_isSharedCheck_3502_ == 0 {
                        v___x_3497_ = v___x_3486_;
                        v_isShared_3498_ = v_isSharedCheck_3502_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3495_);
                        lean_dec(v___x_3486_);
                        v___x_3497_ = lean_box(0);
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
                    v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
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
                    v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
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
    mut v_e_3503_: *mut LeanObject,
    mut v_k_3504_: *mut LeanObject,
    mut v_cleanupAnnotations_3505_: *mut LeanObject,
    mut v___y_3506_: *mut LeanObject,
    mut v___y_3507_: *mut LeanObject,
    mut v___y_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
    mut v___y_3510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3511_: u8 = 0;
    let mut v_res_3512_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3511_ = (lean_unbox(v_cleanupAnnotations_3505_) as u8);
    v_res_3512_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_3503_, v_k_3504_, v_cleanupAnnotations_boxed_3511_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
    lean_dec(v___y_3509_);
    lean_dec_ref(v___y_3508_);
    lean_dec(v___y_3507_);
    lean_dec_ref(v___y_3506_);
    return v_res_3512_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(
    mut v_00_u03b1_3513_: *mut LeanObject,
    mut v_e_3514_: *mut LeanObject,
    mut v_k_3515_: *mut LeanObject,
    mut v_cleanupAnnotations_3516_: u8,
    mut v___y_3517_: *mut LeanObject,
    mut v___y_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
    mut v___y_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    v___x_3522_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_e_3514_, v_k_3515_, v_cleanupAnnotations_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
    return v___x_3522_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___boxed(
    mut v_00_u03b1_3523_: *mut LeanObject,
    mut v_e_3524_: *mut LeanObject,
    mut v_k_3525_: *mut LeanObject,
    mut v_cleanupAnnotations_3526_: *mut LeanObject,
    mut v___y_3527_: *mut LeanObject,
    mut v___y_3528_: *mut LeanObject,
    mut v___y_3529_: *mut LeanObject,
    mut v___y_3530_: *mut LeanObject,
    mut v___y_3531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3532_: u8 = 0;
    let mut v_res_3533_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3532_ = (lean_unbox(v_cleanupAnnotations_3526_) as u8);
    v_res_3533_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8(v_00_u03b1_3523_, v_e_3524_, v_k_3525_, v_cleanupAnnotations_boxed_3532_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
    lean_dec(v___y_3530_);
    lean_dec_ref(v___y_3529_);
    lean_dec(v___y_3528_);
    lean_dec_ref(v___y_3527_);
    return v_res_3533_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(
    mut v___x_3537_: *mut LeanObject,
    mut v___y_3538_: *mut LeanObject,
    mut v___y_3539_: *mut LeanObject,
    mut v___y_3540_: *mut LeanObject,
    mut v___y_3541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3544_: u8 = 0;
    v_options_3543_ = lean_ctor_get(v___y_3540_, 2);
    v_hasTrace_3544_ = lean_ctor_get_uint8(
        v_options_3543_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_3544_ == 0 {
        let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_3537_);
        v___x_3545_ = lean_box((v_hasTrace_3544_) as usize);
        v___x_3546_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3546_, 0, v___x_3545_);
        return v___x_3546_;
    } else {
        let mut v_inheritedTraceOptions_3547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3550_: u8 = 0;
        let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_3547_ = lean_ctor_get(v___y_3540_, 13);
        v___x_3548_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
        v___x_3549_ = l_Lean_Name_append(v___x_3548_, v___x_3537_);
        v___x_3550_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_3547_,
            v_options_3543_,
            v___x_3549_,
        );
        lean_dec(v___x_3549_);
        v___x_3551_ = lean_box((v___x_3550_) as usize);
        v___x_3552_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3552_, 0, v___x_3551_);
        return v___x_3552_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(
    mut v___x_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3559_: *mut LeanObject = core::ptr::null_mut();
    v_res_3559_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
    lean_dec(v___y_3557_);
    lean_dec_ref(v___y_3556_);
    lean_dec(v___y_3555_);
    lean_dec_ref(v___y_3554_);
    return v_res_3559_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0()
-> f64 {
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: f64 = 0.0;
    v___x_3560_ = lean_unsigned_to_nat(0);
    v___x_3561_ = lean_float_of_nat(v___x_3560_);
    return v___x_3561_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(
    mut v_cls_3565_: *mut LeanObject,
    mut v_msg_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
    mut v___y_3570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3577_: u8 = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3590_: u8 = 0;
    let mut v_tid_3591_: u64 = 0;
    let mut v_traces_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3595_: u8 = 0;
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: f64 = 0.0;
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3616_: u8 = 0;
    let mut v_isSharedCheck_3617_: u8 = 0;
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3572_ = lean_ctor_get(v___y_3569_, 5);
                v___x_3573_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0_spec__0(v_msg_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
                v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
                v_isSharedCheck_3618_ = (!lean_is_exclusive(v___x_3573_)) as u8;
                if v_isSharedCheck_3618_ == 0 {
                    v___x_3576_ = v___x_3573_;
                    v_isShared_3577_ = v_isSharedCheck_3618_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3574_);
                    lean_dec(v___x_3573_);
                    v___x_3576_ = lean_box(0);
                    v_isShared_3577_ = v_isSharedCheck_3618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3578_ = lean_st_ref_take(v___y_3570_);
                v_traceState_3579_ = lean_ctor_get(v___x_3578_, 4);
                v_env_3580_ = lean_ctor_get(v___x_3578_, 0);
                v_nextMacroScope_3581_ = lean_ctor_get(v___x_3578_, 1);
                v_ngen_3582_ = lean_ctor_get(v___x_3578_, 2);
                v_auxDeclNGen_3583_ = lean_ctor_get(v___x_3578_, 3);
                v_cache_3584_ = lean_ctor_get(v___x_3578_, 5);
                v_messages_3585_ = lean_ctor_get(v___x_3578_, 6);
                v_infoState_3586_ = lean_ctor_get(v___x_3578_, 7);
                v_snapshotTasks_3587_ = lean_ctor_get(v___x_3578_, 8);
                v_isSharedCheck_3617_ = (!lean_is_exclusive(v___x_3578_)) as u8;
                if v_isSharedCheck_3617_ == 0 {
                    v___x_3589_ = v___x_3578_;
                    v_isShared_3590_ = v_isSharedCheck_3617_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3587_);
                    lean_inc(v_infoState_3586_);
                    lean_inc(v_messages_3585_);
                    lean_inc(v_cache_3584_);
                    lean_inc(v_traceState_3579_);
                    lean_inc(v_auxDeclNGen_3583_);
                    lean_inc(v_ngen_3582_);
                    lean_inc(v_nextMacroScope_3581_);
                    lean_inc(v_env_3580_);
                    lean_dec(v___x_3578_);
                    v___x_3589_ = lean_box(0);
                    v_isShared_3590_ = v_isSharedCheck_3617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3591_ = lean_ctor_get_uint64(
                    v_traceState_3579_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3592_ = lean_ctor_get(v_traceState_3579_, 0);
                v_isSharedCheck_3616_ = (!lean_is_exclusive(v_traceState_3579_)) as u8;
                if v_isSharedCheck_3616_ == 0 {
                    v___x_3594_ = v_traceState_3579_;
                    v_isShared_3595_ = v_isSharedCheck_3616_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3592_);
                    lean_dec(v_traceState_3579_);
                    v___x_3594_ = lean_box(0);
                    v_isShared_3595_ = v_isSharedCheck_3616_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3596_ = lean_box(0);
                v___x_3597_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__0);
                v___x_3598_ = 0;
                v___x_3599_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__1;
                v___x_3600_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3600_, 0, v_cls_3565_);
                lean_ctor_set(v___x_3600_, 1, v___x_3596_);
                lean_ctor_set(v___x_3600_, 2, v___x_3599_);
                lean_ctor_set_float(
                    v___x_3600_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3597_,
                );
                lean_ctor_set_float(
                    v___x_3600_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3597_,
                );
                lean_ctor_set_uint8(
                    v___x_3600_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3598_,
                );
                v___x_3601_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5___closed__2;
                v___x_3602_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3602_, 0, v___x_3600_);
                lean_ctor_set(v___x_3602_, 1, v_a_3574_);
                lean_ctor_set(v___x_3602_, 2, v___x_3601_);
                lean_inc(v_ref_3572_);
                v___x_3603_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3603_, 0, v_ref_3572_);
                lean_ctor_set(v___x_3603_, 1, v___x_3602_);
                v___x_3604_ = l_Lean_PersistentArray_push___redArg(v_traces_3592_, v___x_3603_);
                if v_isShared_3595_ == 0 {
                    lean_ctor_set(v___x_3594_, 0, v___x_3604_);
                    v___x_3606_ = v___x_3594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3604_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3615_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3591_,
                    );
                    v___x_3606_ = v_reuseFailAlloc_3615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3590_ == 0 {
                    lean_ctor_set(v___x_3589_, 4, v___x_3606_);
                    v___x_3608_ = v___x_3589_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_env_3580_);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_nextMacroScope_3581_);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 2, v_ngen_3582_);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 3, v_auxDeclNGen_3583_);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 4, v___x_3606_);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 5, v_cache_3584_);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 6, v_messages_3585_);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 7, v_infoState_3586_);
                    lean_ctor_set(v_reuseFailAlloc_3614_, 8, v_snapshotTasks_3587_);
                    v___x_3608_ = v_reuseFailAlloc_3614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3609_ = lean_st_ref_set(v___y_3570_, v___x_3608_);
                v___x_3610_ = lean_box(0);
                if v_isShared_3577_ == 0 {
                    lean_ctor_set(v___x_3576_, 0, v___x_3610_);
                    v___x_3612_ = v___x_3576_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
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
    mut v_cls_3619_: *mut LeanObject,
    mut v_msg_3620_: *mut LeanObject,
    mut v___y_3621_: *mut LeanObject,
    mut v___y_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
    mut v___y_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3626_: *mut LeanObject = core::ptr::null_mut();
    v_res_3626_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v_cls_3619_, v_msg_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
    lean_dec(v___y_3624_);
    lean_dec_ref(v___y_3623_);
    lean_dec(v___y_3622_);
    lean_dec_ref(v___y_3621_);
    return v_res_3626_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(
    mut v_o_3627_: *mut LeanObject,
    mut v_k_3628_: *mut LeanObject,
    mut v_v_3629_: u8,
) -> *mut LeanObject {
    let mut v_map_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3631_: u8 = 0;
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3630_ = lean_ctor_get(v_o_3627_, 0);
                v_hasTrace_3631_ = lean_ctor_get_uint8(
                    v_o_3627_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3645_ = (!lean_is_exclusive(v_o_3627_)) as u8;
                if v_isSharedCheck_3645_ == 0 {
                    v___x_3633_ = v_o_3627_;
                    v_isShared_3634_ = v_isSharedCheck_3645_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_3630_);
                    lean_dec(v_o_3627_);
                    v___x_3633_ = lean_box(0);
                    v_isShared_3634_ = v_isSharedCheck_3645_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3635_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_3635_, 0 as u32, v_v_3629_);
                lean_inc(v_k_3628_);
                v___x_3636_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3628_, v___x_3635_, v_map_3630_);
                if v_hasTrace_3631_ == 0 {
                    v___x_3637_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
                    v___x_3638_ = l_Lean_Name_isPrefixOf(v___x_3637_, v_k_3628_);
                    lean_dec(v_k_3628_);
                    if v_isShared_3634_ == 0 {
                        lean_ctor_set(v___x_3633_, 0, v___x_3636_);
                        v___x_3640_ = v___x_3633_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3636_);
                        v___x_3640_ = v_reuseFailAlloc_3641_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_3628_);
                    if v_isShared_3634_ == 0 {
                        lean_ctor_set(v___x_3633_, 0, v___x_3636_);
                        v___x_3643_ = v___x_3633_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3636_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_3644_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_3631_,
                        );
                        v___x_3643_ = v_reuseFailAlloc_3644_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_3640_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_o_3646_: *mut LeanObject,
    mut v_k_3647_: *mut LeanObject,
    mut v_v_3648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_3649_: u8 = 0;
    let mut v_res_3650_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_3649_ = (lean_unbox(v_v_3648_) as u8);
    v_res_3650_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_o_3646_, v_k_3647_, v_v_boxed_3649_);
    return v_res_3650_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(
    mut v_opts_3651_: *mut LeanObject,
    mut v_opt_3652_: *mut LeanObject,
    mut v_val_3653_: u8,
) -> *mut LeanObject {
    let mut v_name_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    v_name_3654_ = lean_ctor_get(v_opt_3652_, 0);
    lean_inc(v_name_3654_);
    lean_dec_ref(v_opt_3652_);
    v___x_3655_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1_spec__1(v_opts_3651_, v_name_3654_, v_val_3653_);
    return v___x_3655_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1___boxed(
    mut v_opts_3656_: *mut LeanObject,
    mut v_opt_3657_: *mut LeanObject,
    mut v_val_3658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_3659_: u8 = 0;
    let mut v_res_3660_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_3659_ = (lean_unbox(v_val_3658_) as u8);
    v_res_3660_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_opts_3656_, v_opt_3657_, v_val_boxed_3659_);
    return v_res_3660_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    v___x_3662_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0;
    v___x_3663_ = l_Lean_stringToMessageData(v___x_3662_);
    return v___x_3663_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3()
-> *mut LeanObject {
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    v___x_3665_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2;
    v___x_3666_ = l_Lean_stringToMessageData(v___x_3665_);
    return v___x_3666_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5()
-> *mut LeanObject {
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    v___x_3668_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4;
    v___x_3669_ = l_Lean_stringToMessageData(v___x_3668_);
    return v___x_3669_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(
    mut v_declName_3670_: *mut LeanObject,
    mut v_declNameNonRec_3671_: *mut LeanObject,
    mut v___x_3672_: *mut LeanObject,
    mut v___f_3673_: *mut LeanObject,
    mut v_a_3674_: *mut LeanObject,
    mut v___x_3675_: *mut LeanObject,
    mut v_____r_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3691_: u8 = 0;
    let mut v___y_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: u8 = 0;
    let mut v_fileName_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3705_: u8 = 0;
    let mut v_inheritedTraceOptions_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3712_: u8 = 0;
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: u8 = 0;
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v_a_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3732_: u8 = 0;
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut v___y_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: u8 = 0;
    let mut v___y_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: u8 = 0;
    let mut v___y_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3762_: u8 = 0;
    let mut v_inheritedTraceOptions_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: u8 = 0;
    let mut v___y_3774_: u8 = 0;
    let mut v___y_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: u8 = 0;
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3788_: u8 = 0;
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v_unused_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3802_: u8 = 0;
    let mut v___y_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3804_: u8 = 0;
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v_trackZetaDelta_3828_: u8 = 0;
    let mut v_zetaDeltaSet_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3835_: u8 = 0;
    let mut v_inTypeClassResolution_3836_: u8 = 0;
    let mut v_cacheInferType_3837_: u8 = 0;
    let mut v_fileName_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3850_: u8 = 0;
    let mut v_inheritedTraceOptions_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: u64 = 0;
    let mut v___x_3856_: u64 = 0;
    let mut v___x_3857_: u64 = 0;
    let mut v___x_3858_: u64 = 0;
    let mut v___x_3859_: u64 = 0;
    let mut v_key_3860_: u64 = 0;
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: u8 = 0;
    let mut v_reuseFailAlloc_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut v___y_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_3878_: u8 = 0;
    let mut v___x_3879_: u8 = 0;
    let mut v___x_3880_: u8 = 0;
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: u8 = 0;
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_a_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_a_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3917_: u8 = 0;
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3932_: u8 = 0;
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_a_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3944_: u8 = 0;
    let mut v_a_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3948_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3882_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(v_declName_3670_, v_declNameNonRec_3671_, v___x_3672_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
                if lean_obj_tag(v___x_3882_) == 0 {
                    v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
                    lean_inc(v_a_3883_);
                    lean_dec_ref_known(v___x_3882_, 1);
                    lean_inc_ref(v___f_3673_);
                    lean_inc(v___y_3680_);
                    lean_inc_ref(v___y_3679_);
                    lean_inc(v___y_3678_);
                    lean_inc_ref(v___y_3677_);
                    v___x_3922_ = lean_apply_5(
                        v___f_3673_,
                        v___y_3677_,
                        v___y_3678_,
                        v___y_3679_,
                        v___y_3680_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3922_) == 0 {
                        v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
                        lean_inc(v_a_3923_);
                        lean_dec_ref_known(v___x_3922_, 1);
                        v___x_3924_ = (lean_unbox(v_a_3923_) as u8);
                        lean_dec(v_a_3923_);
                        if v___x_3924_ == 0 {
                            v___y_3885_ = v___y_3677_;
                            v___y_3886_ = v___y_3678_;
                            v___y_3887_ = v___y_3679_;
                            v___y_3888_ = v___y_3680_;
                            state = 14;
                            continue;
                        } else {
                            v___x_3925_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5);
                            lean_inc(v_a_3883_);
                            v___x_3926_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3926_, 0, v_a_3883_);
                            v___x_3927_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3927_, 0, v___x_3925_);
                            lean_ctor_set(v___x_3927_, 1, v___x_3926_);
                            lean_inc(v___x_3675_);
                            v___x_3928_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_3675_, v___x_3927_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
                            if lean_obj_tag(v___x_3928_) == 0 {
                                lean_dec_ref_known(v___x_3928_, 1);
                                v___y_3885_ = v___y_3677_;
                                v___y_3886_ = v___y_3678_;
                                v___y_3887_ = v___y_3679_;
                                v___y_3888_ = v___y_3680_;
                                state = 14;
                                continue;
                            } else {
                                lean_dec(v_a_3883_);
                                lean_dec(v___x_3675_);
                                lean_dec_ref(v_a_3674_);
                                lean_dec_ref(v___f_3673_);
                                v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
                                v_isSharedCheck_3936_ = (!lean_is_exclusive(v___x_3928_)) as u8;
                                if v_isSharedCheck_3936_ == 0 {
                                    v___x_3931_ = v___x_3928_;
                                    v_isShared_3932_ = v_isSharedCheck_3936_;
                                    state = 21;
                                    continue;
                                } else {
                                    lean_inc(v_a_3929_);
                                    lean_dec(v___x_3928_);
                                    v___x_3931_ = lean_box(0);
                                    v_isShared_3932_ = v_isSharedCheck_3936_;
                                    state = 21;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_3883_);
                        lean_dec(v___x_3675_);
                        lean_dec_ref(v_a_3674_);
                        lean_dec_ref(v___f_3673_);
                        v_a_3937_ = lean_ctor_get(v___x_3922_, 0);
                        v_isSharedCheck_3944_ = (!lean_is_exclusive(v___x_3922_)) as u8;
                        if v_isSharedCheck_3944_ == 0 {
                            v___x_3939_ = v___x_3922_;
                            v_isShared_3940_ = v_isSharedCheck_3944_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_3937_);
                            lean_dec(v___x_3922_);
                            v___x_3939_ = lean_box(0);
                            v_isShared_3940_ = v_isSharedCheck_3944_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3675_);
                    lean_dec_ref(v_a_3674_);
                    lean_dec_ref(v___f_3673_);
                    v_a_3945_ = lean_ctor_get(v___x_3882_, 0);
                    v_isSharedCheck_3952_ = (!lean_is_exclusive(v___x_3882_)) as u8;
                    if v_isSharedCheck_3952_ == 0 {
                        v___x_3947_ = v___x_3882_;
                        v_isShared_3948_ = v_isSharedCheck_3952_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_3945_);
                        lean_dec(v___x_3882_);
                        v___x_3947_ = lean_box(0);
                        v_isShared_3948_ = v_isSharedCheck_3952_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3708_ = l_Lean_maxRecDepth;
                v___x_3709_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__3(v___y_3688_, v___x_3708_);
                lean_inc_ref(v_inheritedTraceOptions_3706_);
                lean_inc(v_cancelTk_x3f_3704_);
                lean_inc(v_currMacroScope_3703_);
                lean_inc(v_quotContext_3702_);
                lean_inc(v_maxHeartbeats_3701_);
                lean_inc(v_initHeartbeats_3700_);
                lean_inc(v_openDecls_3699_);
                lean_inc(v_currNamespace_3698_);
                lean_inc(v_ref_3697_);
                lean_inc(v_currRecDepth_3696_);
                lean_inc_ref(v_fileMap_3695_);
                lean_inc_ref(v_fileName_3694_);
                v___x_3710_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_3710_, 0, v_fileName_3694_);
                lean_ctor_set(v___x_3710_, 1, v_fileMap_3695_);
                lean_ctor_set(v___x_3710_, 2, v___y_3688_);
                lean_ctor_set(v___x_3710_, 3, v_currRecDepth_3696_);
                lean_ctor_set(v___x_3710_, 4, v___x_3709_);
                lean_ctor_set(v___x_3710_, 5, v_ref_3697_);
                lean_ctor_set(v___x_3710_, 6, v_currNamespace_3698_);
                lean_ctor_set(v___x_3710_, 7, v_openDecls_3699_);
                lean_ctor_set(v___x_3710_, 8, v_initHeartbeats_3700_);
                lean_ctor_set(v___x_3710_, 9, v_maxHeartbeats_3701_);
                lean_ctor_set(v___x_3710_, 10, v_quotContext_3702_);
                lean_ctor_set(v___x_3710_, 11, v_currMacroScope_3703_);
                lean_ctor_set(v___x_3710_, 12, v_cancelTk_x3f_3704_);
                lean_ctor_set(v___x_3710_, 13, v_inheritedTraceOptions_3706_);
                lean_ctor_set_uint8(
                    v___x_3710_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_3691_,
                );
                lean_ctor_set_uint8(
                    v___x_3710_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
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
                lean_dec_ref_known(v___x_3710_, 14);
                lean_dec_ref(v___y_3686_);
                if lean_obj_tag(v___x_3711_) == 0 {
                    lean_dec_ref_known(v___x_3711_, 1);
                    v_hasTrace_3712_ = lean_ctor_get_uint8(
                        v___y_3685_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3712_ == 0 {
                        lean_dec_ref(v___y_3685_);
                        lean_dec(v___x_3675_);
                        v___x_3713_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_3674_, v___y_3689_);
                        return v___x_3713_;
                    } else {
                        v___x_3714_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
                        lean_inc(v___x_3675_);
                        v___x_3715_ = l_Lean_Name_append(v___x_3714_, v___x_3675_);
                        v___x_3716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___y_3690_,
                            v___y_3685_,
                            v___x_3715_,
                        );
                        lean_dec(v___x_3715_);
                        lean_dec_ref(v___y_3685_);
                        if v___x_3716_ == 0 {
                            lean_dec(v___x_3675_);
                            v___x_3717_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_3674_, v___y_3689_);
                            return v___x_3717_;
                        } else {
                            v___x_3718_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1);
                            v___x_3719_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_3675_, v___x_3718_, v___y_3684_, v___y_3689_, v___y_3692_, v___y_3683_);
                            if lean_obj_tag(v___x_3719_) == 0 {
                                lean_dec_ref_known(v___x_3719_, 1);
                                v___x_3720_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__4___redArg(v_a_3674_, v___y_3689_);
                                return v___x_3720_;
                            } else {
                                lean_dec_ref(v_a_3674_);
                                v_a_3721_ = lean_ctor_get(v___x_3719_, 0);
                                v_isSharedCheck_3728_ = (!lean_is_exclusive(v___x_3719_)) as u8;
                                if v_isSharedCheck_3728_ == 0 {
                                    v___x_3723_ = v___x_3719_;
                                    v_isShared_3724_ = v_isSharedCheck_3728_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_3721_);
                                    lean_dec(v___x_3719_);
                                    v___x_3723_ = lean_box(0);
                                    v_isShared_3724_ = v_isSharedCheck_3728_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3685_);
                    lean_dec(v___x_3675_);
                    lean_dec_ref(v_a_3674_);
                    v_a_3729_ = lean_ctor_get(v___x_3711_, 0);
                    v_isSharedCheck_3736_ = (!lean_is_exclusive(v___x_3711_)) as u8;
                    if v_isSharedCheck_3736_ == 0 {
                        v___x_3731_ = v___x_3711_;
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3729_);
                        lean_dec(v___x_3711_);
                        v___x_3731_ = lean_box(0);
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
                    v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
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
                    v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
                    v___x_3734_ = v_reuseFailAlloc_3735_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3734_;
            }
            6 => {
                v_fileName_3751_ = lean_ctor_get(v___y_3749_, 0);
                v_fileMap_3752_ = lean_ctor_get(v___y_3749_, 1);
                v_currRecDepth_3753_ = lean_ctor_get(v___y_3749_, 3);
                v_ref_3754_ = lean_ctor_get(v___y_3749_, 5);
                v_currNamespace_3755_ = lean_ctor_get(v___y_3749_, 6);
                v_openDecls_3756_ = lean_ctor_get(v___y_3749_, 7);
                v_initHeartbeats_3757_ = lean_ctor_get(v___y_3749_, 8);
                v_maxHeartbeats_3758_ = lean_ctor_get(v___y_3749_, 9);
                v_quotContext_3759_ = lean_ctor_get(v___y_3749_, 10);
                v_currMacroScope_3760_ = lean_ctor_get(v___y_3749_, 11);
                v_cancelTk_x3f_3761_ = lean_ctor_get(v___y_3749_, 12);
                v_suppressElabErrors_3762_ = lean_ctor_get_uint8(
                    v___y_3749_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3763_ = lean_ctor_get(v___y_3749_, 13);
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
                    v_env_3778_ = lean_ctor_get(v___x_3777_, 0);
                    v_nextMacroScope_3779_ = lean_ctor_get(v___x_3777_, 1);
                    v_ngen_3780_ = lean_ctor_get(v___x_3777_, 2);
                    v_auxDeclNGen_3781_ = lean_ctor_get(v___x_3777_, 3);
                    v_traceState_3782_ = lean_ctor_get(v___x_3777_, 4);
                    v_messages_3783_ = lean_ctor_get(v___x_3777_, 6);
                    v_infoState_3784_ = lean_ctor_get(v___x_3777_, 7);
                    v_snapshotTasks_3785_ = lean_ctor_get(v___x_3777_, 8);
                    v_isSharedCheck_3795_ = (!lean_is_exclusive(v___x_3777_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v_unused_3796_ = lean_ctor_get(v___x_3777_, 5);
                        lean_dec(v_unused_3796_);
                        v___x_3787_ = v___x_3777_;
                        v_isShared_3788_ = v_isSharedCheck_3795_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_3785_);
                        lean_inc(v_infoState_3784_);
                        lean_inc(v_messages_3783_);
                        lean_inc(v_traceState_3782_);
                        lean_inc(v_auxDeclNGen_3781_);
                        lean_inc(v_ngen_3780_);
                        lean_inc(v_nextMacroScope_3779_);
                        lean_inc(v_env_3778_);
                        lean_dec(v___x_3777_);
                        v___x_3787_ = lean_box(0);
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
                v___x_3790_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once
                    ),
                    _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2,
                );
                if v_isShared_3788_ == 0 {
                    lean_ctor_set(v___x_3787_, 5, v___x_3790_);
                    lean_ctor_set(v___x_3787_, 0, v___x_3789_);
                    v___x_3792_ = v___x_3787_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3789_);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_nextMacroScope_3779_);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_ngen_3780_);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 3, v_auxDeclNGen_3781_);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 4, v_traceState_3782_);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 5, v___x_3790_);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 6, v_messages_3783_);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 7, v_infoState_3784_);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 8, v_snapshotTasks_3785_);
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
                v_foApprox_3807_ = lean_ctor_get_uint8(v___x_3806_, 0 as u32);
                v_ctxApprox_3808_ = lean_ctor_get_uint8(v___x_3806_, 1 as u32);
                v_quasiPatternApprox_3809_ = lean_ctor_get_uint8(v___x_3806_, 2 as u32);
                v_constApprox_3810_ = lean_ctor_get_uint8(v___x_3806_, 3 as u32);
                v_isDefEqStuckEx_3811_ = lean_ctor_get_uint8(v___x_3806_, 4 as u32);
                v_unificationHints_3812_ = lean_ctor_get_uint8(v___x_3806_, 5 as u32);
                v_proofIrrelevance_3813_ = lean_ctor_get_uint8(v___x_3806_, 6 as u32);
                v_assignSyntheticOpaque_3814_ = lean_ctor_get_uint8(v___x_3806_, 7 as u32);
                v_offsetCnstrs_3815_ = lean_ctor_get_uint8(v___x_3806_, 8 as u32);
                v_etaStruct_3816_ = lean_ctor_get_uint8(v___x_3806_, 10 as u32);
                v_univApprox_3817_ = lean_ctor_get_uint8(v___x_3806_, 11 as u32);
                v_iota_3818_ = lean_ctor_get_uint8(v___x_3806_, 12 as u32);
                v_beta_3819_ = lean_ctor_get_uint8(v___x_3806_, 13 as u32);
                v_proj_3820_ = lean_ctor_get_uint8(v___x_3806_, 14 as u32);
                v_zeta_3821_ = lean_ctor_get_uint8(v___x_3806_, 15 as u32);
                v_zetaDelta_3822_ = lean_ctor_get_uint8(v___x_3806_, 16 as u32);
                v_zetaUnused_3823_ = lean_ctor_get_uint8(v___x_3806_, 17 as u32);
                v_zetaHave_3824_ = lean_ctor_get_uint8(v___x_3806_, 18 as u32);
                v_isSharedCheck_3870_ = (!lean_is_exclusive(v___x_3806_)) as u8;
                if v_isSharedCheck_3870_ == 0 {
                    v___x_3826_ = v___x_3806_;
                    v_isShared_3827_ = v_isSharedCheck_3870_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v___x_3806_);
                    v___x_3826_ = lean_box(0);
                    v_isShared_3827_ = v_isSharedCheck_3870_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_trackZetaDelta_3828_ = lean_ctor_get_uint8(
                    v___y_3799_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3829_ = lean_ctor_get(v___y_3799_, 1);
                v_lctx_3830_ = lean_ctor_get(v___y_3799_, 2);
                v_localInstances_3831_ = lean_ctor_get(v___y_3799_, 3);
                v_defEqCtx_x3f_3832_ = lean_ctor_get(v___y_3799_, 4);
                v_synthPendingDepth_3833_ = lean_ctor_get(v___y_3799_, 5);
                v_canUnfold_x3f_3834_ = lean_ctor_get(v___y_3799_, 6);
                v_univApprox_3835_ = lean_ctor_get_uint8(
                    v___y_3799_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3836_ = lean_ctor_get_uint8(
                    v___y_3799_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3837_ = lean_ctor_get_uint8(
                    v___y_3799_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v_fileName_3838_ = lean_ctor_get(v___y_3803_, 0);
                v_fileMap_3839_ = lean_ctor_get(v___y_3803_, 1);
                v_options_3840_ = lean_ctor_get(v___y_3803_, 2);
                v_currRecDepth_3841_ = lean_ctor_get(v___y_3803_, 3);
                v_ref_3842_ = lean_ctor_get(v___y_3803_, 5);
                v_currNamespace_3843_ = lean_ctor_get(v___y_3803_, 6);
                v_openDecls_3844_ = lean_ctor_get(v___y_3803_, 7);
                v_initHeartbeats_3845_ = lean_ctor_get(v___y_3803_, 8);
                v_maxHeartbeats_3846_ = lean_ctor_get(v___y_3803_, 9);
                v_quotContext_3847_ = lean_ctor_get(v___y_3803_, 10);
                v_currMacroScope_3848_ = lean_ctor_get(v___y_3803_, 11);
                v_cancelTk_x3f_3849_ = lean_ctor_get(v___y_3803_, 12);
                v_suppressElabErrors_3850_ = lean_ctor_get_uint8(
                    v___y_3803_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3851_ = lean_ctor_get(v___y_3803_, 13);
                v_env_3852_ = lean_ctor_get(v___x_3805_, 0);
                lean_inc_ref(v_env_3852_);
                lean_dec(v___x_3805_);
                if v_isShared_3827_ == 0 {
                    v_config_3854_ = v___x_3826_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 0 as u32, v_foApprox_3807_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 1 as u32, v_ctxApprox_3808_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        2 as u32,
                        v_quasiPatternApprox_3809_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 3 as u32, v_constApprox_3810_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 4 as u32, v_isDefEqStuckEx_3811_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 5 as u32, v_unificationHints_3812_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 6 as u32, v_proofIrrelevance_3813_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3869_,
                        7 as u32,
                        v_assignSyntheticOpaque_3814_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 8 as u32, v_offsetCnstrs_3815_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 10 as u32, v_etaStruct_3816_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 11 as u32, v_univApprox_3817_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 12 as u32, v_iota_3818_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 13 as u32, v_beta_3819_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 14 as u32, v_proj_3820_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 15 as u32, v_zeta_3821_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 16 as u32, v_zetaDelta_3822_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 17 as u32, v_zetaUnused_3823_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3869_, 18 as u32, v_zetaHave_3824_);
                    v_config_3854_ = v_reuseFailAlloc_3869_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                lean_ctor_set_uint8(v_config_3854_, 9 as u32, v___y_3804_);
                v___x_3855_ = l_Lean_Meta_Context_configKey(v___y_3799_);
                v___x_3856_ = 3u64;
                v___x_3857_ = lean_uint64_shift_right(v___x_3855_, v___x_3856_);
                v___x_3858_ = lean_uint64_shift_left(v___x_3857_, v___x_3856_);
                v___x_3859_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3804_);
                v_key_3860_ = lean_uint64_lor(v___x_3858_, v___x_3859_);
                v___x_3861_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_3861_, 0, v_config_3854_);
                lean_ctor_set_uint64(
                    v___x_3861_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_3860_,
                );
                lean_inc(v_canUnfold_x3f_3834_);
                lean_inc(v_synthPendingDepth_3833_);
                lean_inc(v_defEqCtx_x3f_3832_);
                lean_inc_ref(v_localInstances_3831_);
                lean_inc_ref(v_lctx_3830_);
                lean_inc(v_zetaDeltaSet_3829_);
                v___x_3862_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_3862_, 0, v___x_3861_);
                lean_ctor_set(v___x_3862_, 1, v_zetaDeltaSet_3829_);
                lean_ctor_set(v___x_3862_, 2, v_lctx_3830_);
                lean_ctor_set(v___x_3862_, 3, v_localInstances_3831_);
                lean_ctor_set(v___x_3862_, 4, v_defEqCtx_x3f_3832_);
                lean_ctor_set(v___x_3862_, 5, v_synthPendingDepth_3833_);
                lean_ctor_set(v___x_3862_, 6, v_canUnfold_x3f_3834_);
                lean_ctor_set_uint8(
                    v___x_3862_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3828_,
                );
                lean_ctor_set_uint8(
                    v___x_3862_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3835_,
                );
                lean_ctor_set_uint8(
                    v___x_3862_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3836_,
                );
                lean_ctor_set_uint8(
                    v___x_3862_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3837_,
                );
                v___x_3863_ = l_Lean_Meta_smartUnfolding;
                v___x_3864_ = 0;
                lean_inc_ref(v_options_3840_);
                v___x_3865_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_3840_, v___x_3863_, v___x_3864_);
                v___x_3866_ = l_Lean_diagnostics;
                v___x_3867_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_3865_, v___x_3866_);
                v___x_3868_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3852_);
                lean_dec_ref(v_env_3852_);
                if v___x_3868_ == 0 {
                    if v___x_3867_ == 0 {
                        lean_inc_ref(v_options_3840_);
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
                        lean_inc_ref(v_options_3840_);
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
                    lean_inc_ref(v_options_3840_);
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
                v_transparency_3878_ = lean_ctor_get_uint8(v___x_3877_, 9 as u32);
                lean_dec_ref(v___x_3877_);
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
                if lean_obj_tag(v___x_3889_) == 0 {
                    v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
                    lean_inc(v_a_3890_);
                    lean_dec_ref_known(v___x_3889_, 1);
                    lean_inc(v___y_3888_);
                    lean_inc_ref(v___y_3887_);
                    lean_inc(v___y_3886_);
                    lean_inc_ref(v___y_3885_);
                    v___x_3891_ = lean_apply_5(
                        v___f_3673_,
                        v___y_3885_,
                        v___y_3886_,
                        v___y_3887_,
                        v___y_3888_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3891_) == 0 {
                        v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
                        lean_inc(v_a_3892_);
                        lean_dec_ref_known(v___x_3891_, 1);
                        v___x_3893_ = (lean_unbox(v_a_3892_) as u8);
                        lean_dec(v_a_3892_);
                        if v___x_3893_ == 0 {
                            v___y_3872_ = v_a_3890_;
                            v___y_3873_ = v___y_3885_;
                            v___y_3874_ = v___y_3886_;
                            v___y_3875_ = v___y_3887_;
                            v___y_3876_ = v___y_3888_;
                            state = 13;
                            continue;
                        } else {
                            v___x_3894_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3);
                            lean_inc(v_a_3890_);
                            v___x_3895_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3895_, 0, v_a_3890_);
                            v___x_3896_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3896_, 0, v___x_3894_);
                            lean_ctor_set(v___x_3896_, 1, v___x_3895_);
                            lean_inc(v___x_3675_);
                            v___x_3897_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_3675_, v___x_3896_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
                            if lean_obj_tag(v___x_3897_) == 0 {
                                lean_dec_ref_known(v___x_3897_, 1);
                                v___y_3872_ = v_a_3890_;
                                v___y_3873_ = v___y_3885_;
                                v___y_3874_ = v___y_3886_;
                                v___y_3875_ = v___y_3887_;
                                v___y_3876_ = v___y_3888_;
                                state = 13;
                                continue;
                            } else {
                                lean_dec(v_a_3890_);
                                lean_dec(v___x_3675_);
                                lean_dec_ref(v_a_3674_);
                                v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
                                v_isSharedCheck_3905_ = (!lean_is_exclusive(v___x_3897_)) as u8;
                                if v_isSharedCheck_3905_ == 0 {
                                    v___x_3900_ = v___x_3897_;
                                    v_isShared_3901_ = v_isSharedCheck_3905_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_3898_);
                                    lean_dec(v___x_3897_);
                                    v___x_3900_ = lean_box(0);
                                    v_isShared_3901_ = v_isSharedCheck_3905_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_3890_);
                        lean_dec(v___x_3675_);
                        lean_dec_ref(v_a_3674_);
                        v_a_3906_ = lean_ctor_get(v___x_3891_, 0);
                        v_isSharedCheck_3913_ = (!lean_is_exclusive(v___x_3891_)) as u8;
                        if v_isSharedCheck_3913_ == 0 {
                            v___x_3908_ = v___x_3891_;
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3906_);
                            lean_dec(v___x_3891_);
                            v___x_3908_ = lean_box(0);
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3675_);
                    lean_dec_ref(v_a_3674_);
                    lean_dec_ref(v___f_3673_);
                    v_a_3914_ = lean_ctor_get(v___x_3889_, 0);
                    v_isSharedCheck_3921_ = (!lean_is_exclusive(v___x_3889_)) as u8;
                    if v_isSharedCheck_3921_ == 0 {
                        v___x_3916_ = v___x_3889_;
                        v_isShared_3917_ = v_isSharedCheck_3921_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_3914_);
                        lean_dec(v___x_3889_);
                        v___x_3916_ = lean_box(0);
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
                    v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
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
                    v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
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
                    v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
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
                    v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
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
                    v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
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
                    v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
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
    mut v_declName_3953_: *mut LeanObject,
    mut v_declNameNonRec_3954_: *mut LeanObject,
    mut v___x_3955_: *mut LeanObject,
    mut v___f_3956_: *mut LeanObject,
    mut v_a_3957_: *mut LeanObject,
    mut v___x_3958_: *mut LeanObject,
    mut v_____r_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
    mut v___y_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
    mut v___y_3963_: *mut LeanObject,
    mut v___y_3964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3965_: *mut LeanObject = core::ptr::null_mut();
    v_res_3965_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_3953_, v_declNameNonRec_3954_, v___x_3955_, v___f_3956_, v_a_3957_, v___x_3958_, v_____r_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
    lean_dec(v___y_3963_);
    lean_dec_ref(v___y_3962_);
    lean_dec(v___y_3961_);
    lean_dec_ref(v___y_3960_);
    return v_res_3965_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1()
-> *mut LeanObject {
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    v___x_3967_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__0;
    v___x_3968_ = l_Lean_stringToMessageData(v___x_3967_);
    return v___x_3968_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3()
-> *mut LeanObject {
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    v___x_3970_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__2;
    v___x_3971_ = l_Lean_stringToMessageData(v___x_3970_);
    return v___x_3971_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9()
-> *mut LeanObject {
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    v___x_3981_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__8;
    v___x_3982_ = l_Lean_stringToMessageData(v___x_3981_);
    return v___x_3982_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(
    mut v_declName_3983_: *mut LeanObject,
    mut v_a_3984_: *mut LeanObject,
    mut v___x_3985_: *mut LeanObject,
    mut v_declNameNonRec_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3995_: u8 = 0;
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: u8 = 0;
    let mut v___y_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4020_: u8 = 0;
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4039_: u8 = 0;
    let mut v_reuseFailAlloc_4040_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4012_) == 0 {
                    v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
                    lean_inc(v_a_4013_);
                    lean_dec_ref_known(v___x_4012_, 1);
                    v___x_4014_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__6;
                    v___f_4015_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__7;
                    v___x_4016_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(v___x_4014_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                    v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
                    v_isSharedCheck_4041_ = (!lean_is_exclusive(v___x_4016_)) as u8;
                    if v_isSharedCheck_4041_ == 0 {
                        v___x_4019_ = v___x_4016_;
                        v_isShared_4020_ = v_isSharedCheck_4041_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4017_);
                        lean_dec(v___x_4016_);
                        v___x_4019_ = lean_box(0);
                        v_isShared_4020_ = v_isSharedCheck_4041_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_declNameNonRec_3986_);
                    v___y_4010_ = v___x_4012_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_3995_ == 0 {
                    lean_dec_ref(v___y_3993_);
                    v___x_3996_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__1);
                    v___x_3997_ = l_Lean_MessageData_ofConstName(v_declName_3983_, v___y_3995_);
                    v___x_3998_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3998_, 0, v___x_3996_);
                    lean_ctor_set(v___x_3998_, 1, v___x_3997_);
                    v___x_3999_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__3);
                    v___x_4000_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4000_, 0, v___x_3998_);
                    lean_ctor_set(v___x_4000_, 1, v___x_3999_);
                    v___x_4001_ = l_Lean_Exception_toMessageData(v___y_3994_);
                    v___x_4002_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4002_, 0, v___x_4000_);
                    lean_ctor_set(v___x_4002_, 1, v___x_4001_);
                    v___x_4003_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixUnder_spec__0___redArg(v___x_4002_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                    return v___x_4003_;
                } else {
                    lean_dec_ref(v___y_3994_);
                    lean_dec(v_declName_3983_);
                    return v___y_3993_;
                }
            }
            2 => {
                v___x_4007_ = l_Lean_Exception_isInterrupt(v_a_4006_);
                if v___x_4007_ == 0 {
                    lean_inc_ref(v_a_4006_);
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
                if lean_obj_tag(v___y_4010_) == 0 {
                    lean_dec(v_declName_3983_);
                    return v___y_4010_;
                } else {
                    v_a_4011_ = lean_ctor_get(v___y_4010_, 0);
                    lean_inc(v_a_4011_);
                    v___y_4005_ = v___y_4010_;
                    v_a_4006_ = v_a_4011_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_4021_ = l_Lean_Expr_mvarId_x21(v_a_4013_);
                v___x_4022_ = (lean_unbox(v_a_4017_) as u8);
                lean_dec(v_a_4017_);
                if v___x_4022_ == 0 {
                    lean_del_object(v___x_4019_);
                    v___x_4023_ = lean_box(0);
                    lean_inc(v_declName_3983_);
                    v___x_4024_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_3983_, v_declNameNonRec_3986_, v___x_4021_, v___f_4015_, v_a_4013_, v___x_4014_, v___x_4023_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                    v___y_4010_ = v___x_4024_;
                    state = 3;
                    continue;
                } else {
                    v___x_4025_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___closed__9);
                    lean_inc(v___x_4021_);
                    if v_isShared_4020_ == 0 {
                        lean_ctor_set_tag(v___x_4019_, 1);
                        lean_ctor_set(v___x_4019_, 0, v___x_4021_);
                        v___x_4027_ = v___x_4019_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4021_);
                        v___x_4027_ = v_reuseFailAlloc_4040_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4028_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4028_, 0, v___x_4025_);
                lean_ctor_set(v___x_4028_, 1, v___x_4027_);
                v___x_4029_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__5(v___x_4014_, v___x_4028_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                if lean_obj_tag(v___x_4029_) == 0 {
                    v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
                    lean_inc(v_a_4030_);
                    lean_dec_ref_known(v___x_4029_, 1);
                    lean_inc(v_declName_3983_);
                    v___x_4031_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(v_declName_3983_, v_declNameNonRec_3986_, v___x_4021_, v___f_4015_, v_a_4013_, v___x_4014_, v_a_4030_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
                    v___y_4010_ = v___x_4031_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_4021_);
                    lean_dec(v_a_4013_);
                    lean_dec(v_declNameNonRec_3986_);
                    v_a_4032_ = lean_ctor_get(v___x_4029_, 0);
                    v_isSharedCheck_4039_ = (!lean_is_exclusive(v___x_4029_)) as u8;
                    if v_isSharedCheck_4039_ == 0 {
                        v___x_4034_ = v___x_4029_;
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4032_);
                        lean_dec(v___x_4029_);
                        v___x_4034_ = lean_box(0);
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                lean_inc(v_a_4032_);
                if v_isShared_4035_ == 0 {
                    v___x_4037_ = v___x_4034_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
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
    mut v_declName_4042_: *mut LeanObject,
    mut v_a_4043_: *mut LeanObject,
    mut v___x_4044_: *mut LeanObject,
    mut v_declNameNonRec_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
    mut v___y_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
    mut v___y_4050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4051_: *mut LeanObject = core::ptr::null_mut();
    v_res_4051_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(v_declName_4042_, v_a_4043_, v___x_4044_, v_declNameNonRec_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
    lean_dec(v___y_4049_);
    lean_dec_ref(v___y_4048_);
    lean_dec(v___y_4047_);
    lean_dec_ref(v___y_4046_);
    return v_res_4051_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(
    mut v_a_4052_: *mut LeanObject,
    mut v_a_4053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4052_) == 0 {
                    v___x_4054_ = l_List_reverse___redArg(v_a_4053_);
                    return v___x_4054_;
                } else {
                    v_head_4055_ = lean_ctor_get(v_a_4052_, 0);
                    v_tail_4056_ = lean_ctor_get(v_a_4052_, 1);
                    v_isSharedCheck_4065_ = (!lean_is_exclusive(v_a_4052_)) as u8;
                    if v_isSharedCheck_4065_ == 0 {
                        v___x_4058_ = v_a_4052_;
                        v_isShared_4059_ = v_isSharedCheck_4065_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4056_);
                        lean_inc(v_head_4055_);
                        lean_dec(v_a_4052_);
                        v___x_4058_ = lean_box(0);
                        v_isShared_4059_ = v_isSharedCheck_4065_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4060_ = l_Lean_mkLevelParam(v_head_4055_);
                if v_isShared_4059_ == 0 {
                    lean_ctor_set(v___x_4058_, 1, v_a_4053_);
                    lean_ctor_set(v___x_4058_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4058_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4060_);
                    lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_a_4053_);
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
    mut v_levelParams_4066_: *mut LeanObject,
    mut v_declName_4067_: *mut LeanObject,
    mut v_declNameNonRec_4068_: *mut LeanObject,
    mut v_name_4069_: *mut LeanObject,
    mut v_xs_4070_: *mut LeanObject,
    mut v_body_4071_: *mut LeanObject,
    mut v___y_4072_: *mut LeanObject,
    mut v___y_4073_: *mut LeanObject,
    mut v___y_4074_: *mut LeanObject,
    mut v___y_4075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u8 = 0;
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4105_: u8 = 0;
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4109_: u8 = 0;
    let mut v_a_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4113_: u8 = 0;
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v_a_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4125_: u8 = 0;
    let mut v_a_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4129_: u8 = 0;
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut v_a_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4077_ = lean_box(0);
                lean_inc(v_levelParams_4066_);
                v_us_4078_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__0(v_levelParams_4066_, v___x_4077_);
                lean_inc(v_declName_4067_);
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
                if lean_obj_tag(v___x_4081_) == 0 {
                    v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
                    lean_inc_n(v_a_4082_, 2);
                    lean_dec_ref_known(v___x_4081_, 1);
                    v___x_4083_ = lean_box(0);
                    v___f_4084_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2___boxed as *mut core::ffi::c_void, 9, 4);
                    lean_closure_set(v___f_4084_, 0, v_declName_4067_);
                    lean_closure_set(v___f_4084_, 1, v_a_4082_);
                    lean_closure_set(v___f_4084_, 2, v___x_4083_);
                    lean_closure_set(v___f_4084_, 3, v_declNameNonRec_4068_);
                    v___x_4085_ = 0;
                    v___x_4086_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__6___redArg(v___f_4084_, v___x_4085_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
                    if lean_obj_tag(v___x_4086_) == 0 {
                        v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
                        lean_inc(v_a_4087_);
                        lean_dec_ref_known(v___x_4086_, 1);
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
                        if lean_obj_tag(v___x_4090_) == 0 {
                            v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
                            lean_inc(v_a_4091_);
                            lean_dec_ref_known(v___x_4090_, 1);
                            v___x_4092_ = l_Lean_Meta_letToHave(
                                v_a_4091_,
                                v___y_4072_,
                                v___y_4073_,
                                v___y_4074_,
                                v___y_4075_,
                            );
                            if lean_obj_tag(v___x_4092_) == 0 {
                                v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
                                lean_inc(v_a_4093_);
                                lean_dec_ref_known(v___x_4092_, 1);
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
                                if lean_obj_tag(v___x_4094_) == 0 {
                                    v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
                                    lean_inc(v_a_4095_);
                                    lean_dec_ref_known(v___x_4094_, 1);
                                    lean_inc(v_name_4069_);
                                    v___x_4096_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_4096_, 0, v_name_4069_);
                                    lean_ctor_set(v___x_4096_, 1, v_levelParams_4066_);
                                    lean_ctor_set(v___x_4096_, 2, v_a_4093_);
                                    v___x_4097_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_4097_, 0, v_name_4069_);
                                    lean_ctor_set(v___x_4097_, 1, v___x_4077_);
                                    v___x_4098_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_4098_, 0, v___x_4096_);
                                    lean_ctor_set(v___x_4098_, 1, v_a_4095_);
                                    lean_ctor_set(v___x_4098_, 2, v___x_4097_);
                                    v___x_4099_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__7___redArg(v___x_4098_, v___y_4075_);
                                    v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
                                    lean_inc(v_a_4100_);
                                    lean_dec_ref(v___x_4099_);
                                    v___x_4101_ = l_Lean_addDecl(
                                        v_a_4100_,
                                        v___x_4085_,
                                        v___y_4074_,
                                        v___y_4075_,
                                    );
                                    return v___x_4101_;
                                } else {
                                    lean_dec(v_a_4093_);
                                    lean_dec(v_name_4069_);
                                    lean_dec(v_levelParams_4066_);
                                    v_a_4102_ = lean_ctor_get(v___x_4094_, 0);
                                    v_isSharedCheck_4109_ = (!lean_is_exclusive(v___x_4094_)) as u8;
                                    if v_isSharedCheck_4109_ == 0 {
                                        v___x_4104_ = v___x_4094_;
                                        v_isShared_4105_ = v_isSharedCheck_4109_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4102_);
                                        lean_dec(v___x_4094_);
                                        v___x_4104_ = lean_box(0);
                                        v_isShared_4105_ = v_isSharedCheck_4109_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4087_);
                                lean_dec(v_name_4069_);
                                lean_dec(v_levelParams_4066_);
                                v_a_4110_ = lean_ctor_get(v___x_4092_, 0);
                                v_isSharedCheck_4117_ = (!lean_is_exclusive(v___x_4092_)) as u8;
                                if v_isSharedCheck_4117_ == 0 {
                                    v___x_4112_ = v___x_4092_;
                                    v_isShared_4113_ = v_isSharedCheck_4117_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_4110_);
                                    lean_dec(v___x_4092_);
                                    v___x_4112_ = lean_box(0);
                                    v_isShared_4113_ = v_isSharedCheck_4117_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4087_);
                            lean_dec(v_name_4069_);
                            lean_dec(v_levelParams_4066_);
                            v_a_4118_ = lean_ctor_get(v___x_4090_, 0);
                            v_isSharedCheck_4125_ = (!lean_is_exclusive(v___x_4090_)) as u8;
                            if v_isSharedCheck_4125_ == 0 {
                                v___x_4120_ = v___x_4090_;
                                v_isShared_4121_ = v_isSharedCheck_4125_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4118_);
                                lean_dec(v___x_4090_);
                                v___x_4120_ = lean_box(0);
                                v_isShared_4121_ = v_isSharedCheck_4125_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4082_);
                        lean_dec(v_name_4069_);
                        lean_dec(v_levelParams_4066_);
                        v_a_4126_ = lean_ctor_get(v___x_4086_, 0);
                        v_isSharedCheck_4133_ = (!lean_is_exclusive(v___x_4086_)) as u8;
                        if v_isSharedCheck_4133_ == 0 {
                            v___x_4128_ = v___x_4086_;
                            v_isShared_4129_ = v_isSharedCheck_4133_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_4126_);
                            lean_dec(v___x_4086_);
                            v___x_4128_ = lean_box(0);
                            v_isShared_4129_ = v_isSharedCheck_4133_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_name_4069_);
                    lean_dec(v_declNameNonRec_4068_);
                    lean_dec(v_declName_4067_);
                    lean_dec(v_levelParams_4066_);
                    v_a_4134_ = lean_ctor_get(v___x_4081_, 0);
                    v_isSharedCheck_4141_ = (!lean_is_exclusive(v___x_4081_)) as u8;
                    if v_isSharedCheck_4141_ == 0 {
                        v___x_4136_ = v___x_4081_;
                        v_isShared_4137_ = v_isSharedCheck_4141_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4134_);
                        lean_dec(v___x_4081_);
                        v___x_4136_ = lean_box(0);
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
                    v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
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
                    v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
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
                    v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
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
                    v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
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
                    v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
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
    mut v_levelParams_4142_: *mut LeanObject,
    mut v_declName_4143_: *mut LeanObject,
    mut v_declNameNonRec_4144_: *mut LeanObject,
    mut v_name_4145_: *mut LeanObject,
    mut v_xs_4146_: *mut LeanObject,
    mut v_body_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4153_: *mut LeanObject = core::ptr::null_mut();
    v_res_4153_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3(v_levelParams_4142_, v_declName_4143_, v_declNameNonRec_4144_, v_name_4145_, v_xs_4146_, v_body_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
    lean_dec(v___y_4151_);
    lean_dec_ref(v___y_4150_);
    lean_dec(v___y_4149_);
    lean_dec_ref(v___y_4148_);
    lean_dec_ref(v_xs_4146_);
    return v_res_4153_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(
    mut v_declName_4154_: *mut LeanObject,
    mut v_info_4155_: *mut LeanObject,
    mut v_name_4156_: *mut LeanObject,
    mut v_a_4157_: *mut LeanObject,
    mut v_a_4158_: *mut LeanObject,
    mut v_a_4159_: *mut LeanObject,
    mut v_a_4160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declNameNonRec_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4178_: u8 = 0;
    let mut v_inheritedTraceOptions_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: u8 = 0;
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    let mut v_fileName_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4199_: u8 = 0;
    let mut v_inheritedTraceOptions_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4207_: u8 = 0;
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4219_: u8 = 0;
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4226_: u8 = 0;
    let mut v_unused_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4162_ = lean_st_ref_get(v_a_4160_);
                v_levelParams_4163_ = lean_ctor_get(v_info_4155_, 1);
                lean_inc(v_levelParams_4163_);
                v_value_4164_ = lean_ctor_get(v_info_4155_, 3);
                lean_inc_ref(v_value_4164_);
                v_declNameNonRec_4165_ = lean_ctor_get(v_info_4155_, 5);
                lean_inc(v_declNameNonRec_4165_);
                lean_dec_ref(v_info_4155_);
                v_fileName_4166_ = lean_ctor_get(v_a_4159_, 0);
                v_fileMap_4167_ = lean_ctor_get(v_a_4159_, 1);
                v_options_4168_ = lean_ctor_get(v_a_4159_, 2);
                v_currRecDepth_4169_ = lean_ctor_get(v_a_4159_, 3);
                v_ref_4170_ = lean_ctor_get(v_a_4159_, 5);
                v_currNamespace_4171_ = lean_ctor_get(v_a_4159_, 6);
                v_openDecls_4172_ = lean_ctor_get(v_a_4159_, 7);
                v_initHeartbeats_4173_ = lean_ctor_get(v_a_4159_, 8);
                v_maxHeartbeats_4174_ = lean_ctor_get(v_a_4159_, 9);
                v_quotContext_4175_ = lean_ctor_get(v_a_4159_, 10);
                v_currMacroScope_4176_ = lean_ctor_get(v_a_4159_, 11);
                v_cancelTk_x3f_4177_ = lean_ctor_get(v_a_4159_, 12);
                v_suppressElabErrors_4178_ = lean_ctor_get_uint8(
                    v_a_4159_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4179_ = lean_ctor_get(v_a_4159_, 13);
                v_env_4180_ = lean_ctor_get(v___x_4162_, 0);
                lean_inc_ref(v_env_4180_);
                lean_dec(v___x_4162_);
                v___f_4181_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__3___boxed as *mut core::ffi::c_void, 11, 4);
                lean_closure_set(v___f_4181_, 0, v_levelParams_4163_);
                lean_closure_set(v___f_4181_, 1, v_declName_4154_);
                lean_closure_set(v___f_4181_, 2, v_declNameNonRec_4165_);
                lean_closure_set(v___f_4181_, 3, v_name_4156_);
                v___x_4182_ = 0;
                v___x_4183_ = l_Lean_Meta_tactic_hygienic;
                lean_inc_ref(v_options_4168_);
                v___x_4184_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__1(v_options_4168_, v___x_4183_, v___x_4182_);
                v___x_4185_ = l_Lean_diagnostics;
                v___x_4186_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__2(v___x_4184_, v___x_4185_);
                v___x_4228_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4180_);
                lean_dec_ref(v_env_4180_);
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
                lean_inc_ref(v_inheritedTraceOptions_4200_);
                lean_inc(v_cancelTk_x3f_4198_);
                lean_inc(v_currMacroScope_4197_);
                lean_inc(v_quotContext_4196_);
                lean_inc(v_maxHeartbeats_4195_);
                lean_inc(v_initHeartbeats_4194_);
                lean_inc(v_openDecls_4193_);
                lean_inc(v_currNamespace_4192_);
                lean_inc(v_ref_4191_);
                lean_inc(v_currRecDepth_4190_);
                lean_inc_ref(v_fileMap_4189_);
                lean_inc_ref(v_fileName_4188_);
                v___x_4204_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4204_, 0, v_fileName_4188_);
                lean_ctor_set(v___x_4204_, 1, v_fileMap_4189_);
                lean_ctor_set(v___x_4204_, 2, v___x_4184_);
                lean_ctor_set(v___x_4204_, 3, v_currRecDepth_4190_);
                lean_ctor_set(v___x_4204_, 4, v___x_4203_);
                lean_ctor_set(v___x_4204_, 5, v_ref_4191_);
                lean_ctor_set(v___x_4204_, 6, v_currNamespace_4192_);
                lean_ctor_set(v___x_4204_, 7, v_openDecls_4193_);
                lean_ctor_set(v___x_4204_, 8, v_initHeartbeats_4194_);
                lean_ctor_set(v___x_4204_, 9, v_maxHeartbeats_4195_);
                lean_ctor_set(v___x_4204_, 10, v_quotContext_4196_);
                lean_ctor_set(v___x_4204_, 11, v_currMacroScope_4197_);
                lean_ctor_set(v___x_4204_, 12, v_cancelTk_x3f_4198_);
                lean_ctor_set(v___x_4204_, 13, v_inheritedTraceOptions_4200_);
                lean_ctor_set_uint8(
                    v___x_4204_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_4186_,
                );
                lean_ctor_set_uint8(
                    v___x_4204_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4199_,
                );
                v___x_4205_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize_spec__8___redArg(v_value_4164_, v___f_4181_, v___x_4182_, v_a_4157_, v_a_4158_, v___x_4204_, v___y_4201_);
                lean_dec_ref_known(v___x_4204_, 14);
                return v___x_4205_;
            }
            2 => {
                if v___y_4207_ == 0 {
                    v___x_4208_ = lean_st_ref_take(v_a_4160_);
                    v_env_4209_ = lean_ctor_get(v___x_4208_, 0);
                    v_nextMacroScope_4210_ = lean_ctor_get(v___x_4208_, 1);
                    v_ngen_4211_ = lean_ctor_get(v___x_4208_, 2);
                    v_auxDeclNGen_4212_ = lean_ctor_get(v___x_4208_, 3);
                    v_traceState_4213_ = lean_ctor_get(v___x_4208_, 4);
                    v_messages_4214_ = lean_ctor_get(v___x_4208_, 6);
                    v_infoState_4215_ = lean_ctor_get(v___x_4208_, 7);
                    v_snapshotTasks_4216_ = lean_ctor_get(v___x_4208_, 8);
                    v_isSharedCheck_4226_ = (!lean_is_exclusive(v___x_4208_)) as u8;
                    if v_isSharedCheck_4226_ == 0 {
                        v_unused_4227_ = lean_ctor_get(v___x_4208_, 5);
                        lean_dec(v_unused_4227_);
                        v___x_4218_ = v___x_4208_;
                        v_isShared_4219_ = v_isSharedCheck_4226_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_4216_);
                        lean_inc(v_infoState_4215_);
                        lean_inc(v_messages_4214_);
                        lean_inc(v_traceState_4213_);
                        lean_inc(v_auxDeclNGen_4212_);
                        lean_inc(v_ngen_4211_);
                        lean_inc(v_nextMacroScope_4210_);
                        lean_inc(v_env_4209_);
                        lean_dec(v___x_4208_);
                        v___x_4218_ = lean_box(0);
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
                v___x_4221_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2_once
                    ),
                    _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2,
                );
                if v_isShared_4219_ == 0 {
                    lean_ctor_set(v___x_4218_, 5, v___x_4221_);
                    lean_ctor_set(v___x_4218_, 0, v___x_4220_);
                    v___x_4223_ = v___x_4218_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4220_);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_nextMacroScope_4210_);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 2, v_ngen_4211_);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 3, v_auxDeclNGen_4212_);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 4, v_traceState_4213_);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 5, v___x_4221_);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 6, v_messages_4214_);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 7, v_infoState_4215_);
                    lean_ctor_set(v_reuseFailAlloc_4225_, 8, v_snapshotTasks_4216_);
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
    mut v_declName_4229_: *mut LeanObject,
    mut v_info_4230_: *mut LeanObject,
    mut v_name_4231_: *mut LeanObject,
    mut v_a_4232_: *mut LeanObject,
    mut v_a_4233_: *mut LeanObject,
    mut v_a_4234_: *mut LeanObject,
    mut v_a_4235_: *mut LeanObject,
    mut v_a_4236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4237_: *mut LeanObject = core::ptr::null_mut();
    v_res_4237_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(v_declName_4229_, v_info_4230_, v_name_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_);
    lean_dec(v_a_4235_);
    lean_dec_ref(v_a_4234_);
    lean_dec(v_a_4233_);
    lean_dec_ref(v_a_4232_);
    return v_res_4237_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(
    mut v_declName_4238_: *mut LeanObject,
    mut v_info_4239_: *mut LeanObject,
    mut v_a_4240_: *mut LeanObject,
    mut v_a_4241_: *mut LeanObject,
    mut v_a_4242_: *mut LeanObject,
    mut v_a_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4253_: u8 = 0;
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut v_unused_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4245_ = lean_st_ref_get(v_a_4243_);
                v_env_4246_ = lean_ctor_get(v___x_4245_, 0);
                lean_inc_ref(v_env_4246_);
                lean_dec(v___x_4245_);
                v___x_4247_ = l_Lean_Meta_unfoldThmSuffix;
                lean_inc_n(v_declName_4238_, 2);
                v___x_4248_ =
                    l_Lean_Meta_mkEqLikeNameFor(v_env_4246_, v_declName_4238_, v___x_4247_);
                lean_inc_n(v___x_4248_, 2);
                v___x_4249_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___boxed as *mut core::ffi::c_void, 8, 3);
                lean_closure_set(v___x_4249_, 0, v_declName_4238_);
                lean_closure_set(v___x_4249_, 1, v_info_4239_);
                lean_closure_set(v___x_4249_, 2, v___x_4248_);
                v___x_4250_ = l_Lean_Meta_realizeConst(
                    v_declName_4238_,
                    v___x_4248_,
                    v___x_4249_,
                    v_a_4240_,
                    v_a_4241_,
                    v_a_4242_,
                    v_a_4243_,
                );
                if lean_obj_tag(v___x_4250_) == 0 {
                    v_isSharedCheck_4257_ = (!lean_is_exclusive(v___x_4250_)) as u8;
                    if v_isSharedCheck_4257_ == 0 {
                        v_unused_4258_ = lean_ctor_get(v___x_4250_, 0);
                        lean_dec(v_unused_4258_);
                        v___x_4252_ = v___x_4250_;
                        v_isShared_4253_ = v_isSharedCheck_4257_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4250_);
                        v___x_4252_ = lean_box(0);
                        v_isShared_4253_ = v_isSharedCheck_4257_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4248_);
                    v_a_4259_ = lean_ctor_get(v___x_4250_, 0);
                    v_isSharedCheck_4266_ = (!lean_is_exclusive(v___x_4250_)) as u8;
                    if v_isSharedCheck_4266_ == 0 {
                        v___x_4261_ = v___x_4250_;
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4259_);
                        lean_dec(v___x_4250_);
                        v___x_4261_ = lean_box(0);
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4253_ == 0 {
                    lean_ctor_set(v___x_4252_, 0, v___x_4248_);
                    v___x_4255_ = v___x_4252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4248_);
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
                    v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
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
    mut v_declName_4267_: *mut LeanObject,
    mut v_info_4268_: *mut LeanObject,
    mut v_a_4269_: *mut LeanObject,
    mut v_a_4270_: *mut LeanObject,
    mut v_a_4271_: *mut LeanObject,
    mut v_a_4272_: *mut LeanObject,
    mut v_a_4273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4274_: *mut LeanObject = core::ptr::null_mut();
    v_res_4274_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_4267_, v_info_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
    lean_dec(v_a_4272_);
    lean_dec_ref(v_a_4271_);
    lean_dec(v_a_4270_);
    lean_dec_ref(v_a_4269_);
    return v_res_4274_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(
    mut v_declName_4275_: *mut LeanObject,
    mut v_a_4276_: *mut LeanObject,
    mut v_a_4277_: *mut LeanObject,
    mut v_a_4278_: *mut LeanObject,
    mut v_a_4279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___x_4288_: u8 = 0;
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4298_: u8 = 0;
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4303_: u8 = 0;
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v_a_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4318_: u8 = 0;
    let mut v_isSharedCheck_4319_: u8 = 0;
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4281_ = lean_st_ref_get(v_a_4279_);
                v___x_4282_ = lean_st_ref_get(v_a_4279_);
                v_env_4283_ = lean_ctor_get(v___x_4281_, 0);
                lean_inc_ref(v_env_4283_);
                lean_dec(v___x_4281_);
                v_env_4284_ = lean_ctor_get(v___x_4282_, 0);
                lean_inc_ref_n(v_env_4284_, 2);
                lean_dec(v___x_4282_);
                v___x_4285_ = l_Lean_Meta_unfoldThmSuffix;
                lean_inc(v_declName_4275_);
                v___x_4286_ =
                    l_Lean_Meta_mkEqLikeNameFor(v_env_4283_, v_declName_4275_, v___x_4285_);
                v___x_4287_ = 1;
                lean_inc(v___x_4286_);
                v___x_4288_ = l_Lean_Environment_contains(v_env_4284_, v___x_4286_, v___x_4287_);
                if v___x_4288_ == 0 {
                    lean_dec(v___x_4286_);
                    v___x_4289_ = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
                    v_toEnvExtension_4290_ = lean_ctor_get(v___x_4289_, 0);
                    v_asyncMode_4291_ = lean_ctor_get(v_toEnvExtension_4290_, 2);
                    v___x_4292_ = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
                    v___x_4293_ = 0;
                    lean_inc(v_declName_4275_);
                    v___x_4294_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                        v___x_4292_,
                        v___x_4289_,
                        v_env_4284_,
                        v_declName_4275_,
                        v_asyncMode_4291_,
                        v___x_4293_,
                    );
                    if lean_obj_tag(v___x_4294_) == 1 {
                        v_val_4295_ = lean_ctor_get(v___x_4294_, 0);
                        v_isSharedCheck_4319_ = (!lean_is_exclusive(v___x_4294_)) as u8;
                        if v_isSharedCheck_4319_ == 0 {
                            v___x_4297_ = v___x_4294_;
                            v_isShared_4298_ = v_isSharedCheck_4319_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_4295_);
                            lean_dec(v___x_4294_);
                            v___x_4297_ = lean_box(0);
                            v_isShared_4298_ = v_isSharedCheck_4319_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4294_);
                        lean_dec(v_declName_4275_);
                        v___x_4320_ = lean_box(0);
                        v___x_4321_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4321_, 0, v___x_4320_);
                        return v___x_4321_;
                    }
                } else {
                    lean_dec_ref(v_env_4284_);
                    lean_dec(v_declName_4275_);
                    v___x_4322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4322_, 0, v___x_4286_);
                    v___x_4323_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4323_, 0, v___x_4322_);
                    return v___x_4323_;
                }
            }
            1 => {
                v___x_4299_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkUnfoldEq(v_declName_4275_, v_val_4295_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_);
                if lean_obj_tag(v___x_4299_) == 0 {
                    v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
                    v_isSharedCheck_4310_ = (!lean_is_exclusive(v___x_4299_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4302_ = v___x_4299_;
                        v_isShared_4303_ = v_isSharedCheck_4310_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4300_);
                        lean_dec(v___x_4299_);
                        v___x_4302_ = lean_box(0);
                        v_isShared_4303_ = v_isSharedCheck_4310_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4297_);
                    v_a_4311_ = lean_ctor_get(v___x_4299_, 0);
                    v_isSharedCheck_4318_ = (!lean_is_exclusive(v___x_4299_)) as u8;
                    if v_isSharedCheck_4318_ == 0 {
                        v___x_4313_ = v___x_4299_;
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4311_);
                        lean_dec(v___x_4299_);
                        v___x_4313_ = lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4298_ == 0 {
                    lean_ctor_set(v___x_4297_, 0, v_a_4300_);
                    v___x_4305_ = v___x_4297_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4300_);
                    v___x_4305_ = v_reuseFailAlloc_4309_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4303_ == 0 {
                    lean_ctor_set(v___x_4302_, 0, v___x_4305_);
                    v___x_4307_ = v___x_4302_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
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
                    v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
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
    mut v_declName_4324_: *mut LeanObject,
    mut v_a_4325_: *mut LeanObject,
    mut v_a_4326_: *mut LeanObject,
    mut v_a_4327_: *mut LeanObject,
    mut v_a_4328_: *mut LeanObject,
    mut v_a_4329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4330_: *mut LeanObject = core::ptr::null_mut();
    v_res_4330_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(v_declName_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_);
    lean_dec(v_a_4328_);
    lean_dec_ref(v_a_4327_);
    lean_dec(v_a_4326_);
    lean_dec_ref(v_a_4325_);
    return v_res_4330_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    v___x_4333_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_;
    v___x_4334_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_4333_);
    return v___x_4334_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2____boxed(
    mut v_a_4335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4336_: *mut LeanObject = core::ptr::null_mut();
    v_res_4336_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
    return v_res_4336_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default =
        _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default();
    lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default);
    l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo =
        _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo();
    lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo);
    res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1195399529____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_PartialFixpoint_eqnInfoExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_PartialFixpoint_eqnInfoExt);
    lean_dec_ref(res);
    res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_1741434721____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
}
