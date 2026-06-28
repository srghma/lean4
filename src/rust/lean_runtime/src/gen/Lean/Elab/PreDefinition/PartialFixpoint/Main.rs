// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Main
// Imports: Lean.Elab.PreDefinition.MkInhabitant Lean.Elab.PreDefinition.Mutual Lean.Elab.PreDefinition.PartialFixpoint.Eqns Lean.Elab.Tactic.Monotonicity Lean.Meta.Order
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{l_Lean_Core_mkFreshUserName, l_Lean_Exception_isRuntime};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::PreDefinition::Basic::{
    l_Lean_Elab_addAndCompilePartialRec, l_Lean_Elab_addAsAxiom___redArg,
    l_Lean_Elab_instInhabitedPreDefinition_default,
};
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::{
    l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl,
    l_Lean_Elab_FixedParamPerm_buildArgs___redArg, l_Lean_Elab_FixedParamPerm_instantiateForall,
    l_Lean_Elab_FixedParamPerm_instantiateLambda, l_Lean_Elab_FixedParamPerm_pickFixed___redArg,
    l_Lean_Elab_FixedParamPerm_pickVarying___redArg, l_Lean_Elab_FixedParamPerms_fixedArePrefix,
    l_Lean_Elab_getFixedParamPerms,
};
use crate::r#gen::Lean::Elab::PreDefinition::MkInhabitant::{
    initialize_Lean_Elab_PreDefinition_MkInhabitant, l_Lean_Elab_mkInhabitantFor,
    runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant,
};
use crate::r#gen::Lean::Elab::PreDefinition::Mutual::{
    initialize_Lean_Elab_PreDefinition_Mutual, l_Lean_Elab_Mutual_addPreDefAttributes,
    l_Lean_Elab_Mutual_addPreDefsFromUnary, l_Lean_Elab_Mutual_cleanPreDef,
    runtime_initialize_Lean_Elab_PreDefinition_Mutual,
};
use crate::r#gen::Lean::Elab::PreDefinition::PartialFixpoint::Eqns::{
    initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns,
    l_Lean_Elab_PartialFixpoint_registerEqnsInfo,
    runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns,
};
use crate::r#gen::Lean::Elab::PreDefinition::TerminationHint::{
    l_Lean_Elab_instInhabitedPartialFixpoint_default, l_Lean_Elab_isLatticeTheoretic,
};
use crate::r#gen::Lean::Elab::RecAppSyntax::{
    l_Lean_getRecAppSyntax_x3f, l_Lean_hasRecAppSyntax___boxed,
};
use crate::r#gen::Lean::Elab::SyntheticMVars::l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp;
use crate::r#gen::Lean::Elab::Tactic::Monotonicity::{
    initialize_Lean_Elab_Tactic_Monotonicity, l_Lean_Meta_Monotonicity_solveMono,
    runtime_initialize_Lean_Elab_Tactic_Monotonicity,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType___boxed, l_Lean_Elab_Term_instInhabitedTermElabM,
    l_Lean_Elab_Term_logUnassignedUsingErrorInfos,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_setExporting, l_Lean_Environment_unlockAsync,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_const___override, l_Lean_Expr_constName_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar, l_Lean_Expr_isApp,
    l_Lean_Expr_isConst, l_Lean_Expr_isConstOf, l_Lean_Expr_isLambda, l_Lean_Expr_isProp,
    l_Lean_Expr_mvarId_x21, l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr, l_Lean_mkAppN,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_mkLevelParam};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_andList, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkAppM, l_Lean_Meta_mkAppOptM};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instantiateForall,
    l_Lean_Meta_mapErrorImp___redArg, l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Order::{
    initialize_Lean_Meta_Order, l_Lean_Meta_mkFixOfMonFun, l_Lean_Meta_mkInstPiOfInstsForall,
    l_Lean_Meta_mkPackedPPRodInstance, l_Lean_Meta_toPartialOrder,
    runtime_initialize_Lean_Meta_Order,
};
use crate::r#gen::Lean::Meta::PProdN::{
    l_Lean_Meta_PProdN_genMk___redArg, l_Lean_Meta_PProdN_mk, l_Lean_Meta_PProdN_pack,
    l_Lean_Meta_PProdN_proj, l_Lean_Meta_PProdN_reduceProjs,
};
use crate::r#gen::Lean::Meta::Sorry::l_Lean_Meta_mkSorry;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Lean::Meta::Transform::l_Lean_Core_betaReduce;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::Util::FindExpr::lean_find_expr;
use crate::lean_imports_rs::Lean::Util::ReplaceExpr::lean_replace_expr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_apply_7, lean_apply_8, lean_apply_9, lean_box, lean_box_usize,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0_value: LeanStringObject<45> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 46, 77, 97, 105, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__1_value: LeanStringObject<81> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 81, m_capacity: 81, m_length: 80, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 46, 77, 97, 105, 110, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 114, 101, 112, 108, 97, 99, 101, 82, 101, 99, 65, 112, 112, 115, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__2_value: LeanStringObject<69> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 114, 101, 99, 70, 110, 78, 97, 109, 101, 115, 46, 115, 105, 122, 101, 32, 61, 32, 102, 105, 120, 101, 100, 80, 97, 114, 97, 109, 80, 101, 114, 109, 115, 46, 112, 101, 114, 109, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 108, 97, 109, 98, 100, 97, 58, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [109, 107, 77, 111, 110, 111, 80, 80, 114, 111, 100, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 111, 102, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 114, 100, 101, 114, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__4_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 111, 110, 111, 116, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__4_value) as *mut LeanObject,13968876794123802173 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [80, 80, 114, 111, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__7_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 111, 110, 111, 116, 111, 110, 101, 95, 109, 107, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__6_value) as *mut LeanObject,1900977913816506253 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__7_value) as *mut LeanObject,6887720551906075630 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0_value) as *mut LeanObject;
pub static l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0_value
) as *mut LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_hasRecAppSyntax___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [67, 97, 110, 110, 111, 116, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 99, 97, 108, 108, 32, 96, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [96, 32, 101, 110, 99, 108, 111, 115, 101, 100, 32, 105, 110, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 112, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [103, 101, 116, 82, 101, 99, 65, 112, 112, 83, 121, 110, 116, 97, 120, 63, 32, 102, 97, 105, 108, 101, 100, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [67, 97, 110, 110, 111, 116, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 99, 97, 108, 108, 32, 105, 110, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [84, 114, 105, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [44, 32, 98, 117, 116, 32, 102, 97, 105, 108, 101, 100, 46, 10, 80, 111, 115, 115, 105, 98, 108, 101, 32, 99, 97, 117, 115, 101, 58, 32, 65, 32, 109, 105, 115, 115, 105, 110, 103, 32, 96, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [77, 111, 110, 111, 66, 105, 110, 100, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16_value) as *mut LeanObject;
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16_value) as *mut LeanObject,16732353260660660630 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18_value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 46, 10, 85, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 116, 114, 97, 99, 101, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 109, 111, 110, 111, 116, 111, 110, 105, 99, 105, 116, 121, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 100, 101, 98, 117, 103, 46, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 112, 114, 111, 118, 101, 32, 39, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [39, 32, 116, 111, 32, 98, 101, 32, 109, 111, 110, 111, 116, 111, 110, 101, 32, 105, 110, 32, 105, 116, 115, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 99, 97, 108, 108, 115, 58, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [112, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6_value) as *mut LeanObject;
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5_value) as *mut LeanObject,6897119537390546559 as *mut LeanObject] };
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6_value) as *mut LeanObject,3297018234817926677 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [109, 111, 110, 111, 116, 111, 110, 105, 99, 105, 116, 121, 32, 112, 114, 111, 111, 102, 32, 102, 111, 114, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [102, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0_value) as *mut LeanObject,1707590486618227741 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_partialFixpoint___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_partialFixpoint___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_partialFixpoint___lam__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_partialFixpoint___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_partialFixpoint___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_partialFixpoint___lam__0___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [109, 117, 116, 117, 97, 108, 0],
    };
static mut l_Lean_Elab_partialFixpoint___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_partialFixpoint___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_partialFixpoint___lam__0___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_partialFixpoint___lam__0___closed__2_value)
                as *mut LeanObject,
            17176105497081078574 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_partialFixpoint___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_partialFixpoint___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_partialFixpoint___lam__0___closed__4_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [112, 97, 99, 107, 101, 100, 86, 97, 108, 117, 101, 58, 32, 0],
    };
static mut l_Lean_Elab_partialFixpoint___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_partialFixpoint___lam__0___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_partialFixpoint___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_partialFixpoint___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0_value:
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
static mut l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111, 109, 112, 105, 108, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 39, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [39, 32, 117, 115, 105, 110, 103, 32, 96, 112, 97, 114, 116, 105, 97, 108, 95, 102, 105, 120, 112, 111, 105, 110, 116, 96, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 116, 114, 111, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6_value) as *mut LeanObject;
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5_value) as *mut LeanObject,13229434762204987278 as *mut LeanObject] };
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6_value) as *mut LeanObject,7945323172821520753 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 102, 78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9_value) as *mut LeanObject;
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8_value) as *mut LeanObject,10854111772627758120 as *mut LeanObject] };
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9_value) as *mut LeanObject,885287005709150661 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [70, 108, 97, 116, 79, 114, 100, 101, 114, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 67, 67, 80, 79, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [78, 111, 32, 67, 67, 80, 79, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 102, 111, 117, 110, 100, 32, 102, 111, 114, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [44, 32, 116, 114, 121, 105, 110, 103, 32, 105, 110, 104, 97, 98, 105, 116, 97, 116, 105, 111, 110, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 67, 80, 79, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4_value) as *mut LeanObject;
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4_value) as *mut LeanObject,14719117893866890003 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 114, 101, 68, 101, 102, 46, 118, 97, 108, 117, 101, 58, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [44, 32, 120, 115, 58, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [44, 32, 95, 98, 111, 100, 121, 58, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [73, 109, 112, 108, 105, 99, 97, 116, 105, 111, 110, 79, 114, 100, 101, 114, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 115, 116, 67, 111, 109, 112, 108, 101, 116, 101, 76, 97, 116, 116, 105, 99, 101, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value) as *mut LeanObject;
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0_value) as *mut LeanObject,1404824740281118826 as *mut LeanObject] };
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value) as *mut LeanObject,15344108618287221081 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4_value: LeanStringObject<59> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 59, m_capacity: 59, m_length: 58, m_data: [96, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 102, 105, 120, 112, 111, 105, 110, 116, 96, 32, 99, 97, 110, 32, 98, 101, 32, 111, 110, 108, 121, 32, 117, 115, 101, 100, 32, 116, 111, 32, 100, 101, 102, 105, 110, 101, 32, 112, 114, 101, 100, 105, 99, 97, 116, 101, 115, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [82, 101, 118, 101, 114, 115, 101, 73, 109, 112, 108, 105, 99, 97, 116, 105, 111, 110, 79, 114, 100, 101, 114, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0_value) as *mut LeanObject;
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0_value) as *mut LeanObject,3060782016661332237 as *mut LeanObject] };
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value) as *mut LeanObject,9384187537468742202 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3_value: LeanStringObject<61> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [96, 99, 111, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 102, 105, 120, 112, 111, 105, 110, 116, 96, 32, 99, 97, 110, 32, 98, 101, 32, 111, 110, 108, 121, 32, 117, 115, 101, 100, 32, 116, 111, 32, 100, 101, 102, 105, 110, 101, 32, 112, 114, 101, 100, 105, 99, 97, 116, 101, 115, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_partialFixpoint___closed__0_value: LeanStringObject<116> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 116,
        m_capacity: 116,
        m_length: 115,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 112, 114, 101, 68, 101, 102, 115, 46, 115, 105, 122, 101, 32, 61, 32, 104,
            105, 110, 116, 115, 46, 115, 105, 122, 101, 10, 32, 32, 45, 45, 32, 87, 101, 32, 99,
            104, 101, 99, 107, 32, 105, 102, 32, 97, 110, 121, 32, 102, 105, 120, 112, 111, 105,
            110, 116, 115, 32, 119, 101, 114, 101, 32, 100, 101, 102, 105, 110, 101, 100, 32, 108,
            97, 116, 116, 105, 99, 101, 45, 116, 104, 101, 111, 114, 101, 116, 105, 99, 97, 108,
            108, 121, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Elab_partialFixpoint___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_partialFixpoint___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_partialFixpoint___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_partialFixpoint___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_partialFixpoint___closed__2_value: LeanStringObject<218> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 218,
        m_capacity: 218,
        m_length: 213,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 104, 105, 110, 116, 115, 46, 97, 108, 108, 32, 102, 117, 110, 32, 120, 32,
            61, 62, 32, 105, 115, 76, 97, 116, 116, 105, 99, 101, 84, 104, 101, 111, 114, 101, 116,
            105, 99, 32, 120, 46, 102, 105, 120, 112, 111, 105, 110, 116, 84, 121, 112, 101, 10,
            10, 32, 32, 45, 45, 32, 70, 111, 114, 32, 101, 118, 101, 114, 121, 32, 102, 117, 110,
            99, 116, 105, 111, 110, 32, 111, 102, 32, 116, 121, 112, 101, 32, 96, 226, 136, 128,
            32, 120, 32, 121, 44, 32, 114, 32, 120, 32, 121, 96, 44, 32, 97, 110, 32, 67, 67, 80,
            79, 32, 105, 110, 115, 116, 97, 110, 99, 101, 10, 32, 32, 45, 45, 32, 226, 136, 128,
            32, 120, 32, 121, 44, 32, 67, 67, 80, 79, 32, 40, 114, 32, 120, 32, 121, 41, 44, 32,
            98, 117, 116, 32, 99, 114, 117, 99, 105, 97, 108, 108, 121, 32, 99, 111, 110, 115, 116,
            114, 117, 99, 116, 101, 100, 32, 117, 115, 105, 110, 103, 32, 96, 105, 110, 115, 116,
            67, 67, 80, 79, 80, 105, 96, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Elab_partialFixpoint___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_partialFixpoint___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_partialFixpoint___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_partialFixpoint___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_partialFixpoint___boxed__const__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + core::mem::size_of::<usize>() * 1) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(0 as *mut LeanObject)],
    };
pub static mut l_Lean_Elab_partialFixpoint___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_partialFixpoint___boxed__const__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,13137517462150097927 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [80, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,9591557227024223490 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 97, 105, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,14411028116393779375 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,6292779945975326914 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,6450059806917017399 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,940866959652618354 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value) as *mut LeanObject,1125095253515664115 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value) as *mut LeanObject,12036251161462470821 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,15892360154377873166 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,1255499534391214319 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,10870426477948315702 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,((( 1869300320 as usize) << 1) | 1) as *mut LeanObject,14638541164393750211 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,12868036163648122328 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,6633987362298141052 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,3032145853777581349 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0(
    mut v_msg_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
    mut v___y_4377_: *mut LeanObject,
    mut v___y_4378_: *mut LeanObject,
    mut v___y_4379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710__overap_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    v___f_4381_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0;
    v___x_710__overap_4382_ = lean_panic_fn_borrowed(v___f_4381_, v_msg_4375_);
    lean_inc(v___y_4379_);
    lean_inc_ref(v___y_4378_);
    lean_inc(v___y_4377_);
    lean_inc_ref(v___y_4376_);
    v___x_4383_ = lean_apply_5(
        v___x_710__overap_4382_,
        v___y_4376_,
        v___y_4377_,
        v___y_4378_,
        v___y_4379_,
        lean_box(0),
    );
    return v___x_4383_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___boxed(
    mut v_msg_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
    mut v___y_4386_: *mut LeanObject,
    mut v___y_4387_: *mut LeanObject,
    mut v___y_4388_: *mut LeanObject,
    mut v___y_4389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4390_: *mut LeanObject = core::ptr::null_mut();
    v_res_4390_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0(v_msg_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
    lean_dec(v___y_4388_);
    lean_dec_ref(v___y_4387_);
    lean_dec(v___y_4386_);
    lean_dec_ref(v___y_4385_);
    return v_res_4390_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2(
    mut v_xs_4391_: *mut LeanObject,
    mut v_v_4392_: *mut LeanObject,
    mut v_i_4393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: u8 = 0;
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4394_ = lean_array_get_size(v_xs_4391_);
                v___x_4395_ = lean_nat_dec_lt(v_i_4393_, v___x_4394_);
                if v___x_4395_ == 0 {
                    lean_dec(v_i_4393_);
                    v___x_4396_ = lean_box(0);
                    return v___x_4396_;
                } else {
                    v___x_4397_ = lean_array_fget_borrowed(v_xs_4391_, v_i_4393_);
                    v___x_4398_ = lean_name_eq(v___x_4397_, v_v_4392_);
                    if v___x_4398_ == 0 {
                        v___x_4399_ = lean_unsigned_to_nat(1);
                        v___x_4400_ = lean_nat_add(v_i_4393_, v___x_4399_);
                        lean_dec(v_i_4393_);
                        v_i_4393_ = v___x_4400_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4402_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4402_, 0, v_i_4393_);
                        return v___x_4402_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2___boxed(
    mut v_xs_4403_: *mut LeanObject,
    mut v_v_4404_: *mut LeanObject,
    mut v_i_4405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4406_: *mut LeanObject = core::ptr::null_mut();
    v_res_4406_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2(v_xs_4403_, v_v_4404_, v_i_4405_);
    lean_dec(v_v_4404_);
    lean_dec_ref(v_xs_4403_);
    return v_res_4406_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1(
    mut v_xs_4407_: *mut LeanObject,
    mut v_v_4408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    v___x_4409_ = lean_unsigned_to_nat(0);
    v___x_4410_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2(v_xs_4407_, v_v_4408_, v___x_4409_);
    return v___x_4410_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1___boxed(
    mut v_xs_4411_: *mut LeanObject,
    mut v_v_4412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4413_: *mut LeanObject = core::ptr::null_mut();
    v_res_4413_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1(v_xs_4411_, v_v_4412_);
    lean_dec(v_v_4412_);
    lean_dec_ref(v_xs_4411_);
    return v_res_4413_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1(
    mut v_xs_4414_: *mut LeanObject,
    mut v_v_4415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4421_: u8 = 0;
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4416_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1(v_xs_4414_, v_v_4415_);
                if lean_obj_tag(v___x_4416_) == 0 {
                    v___x_4417_ = lean_box(0);
                    return v___x_4417_;
                } else {
                    v_val_4418_ = lean_ctor_get(v___x_4416_, 0);
                    v_isSharedCheck_4425_ = (!lean_is_exclusive(v___x_4416_)) as u8;
                    if v_isSharedCheck_4425_ == 0 {
                        v___x_4420_ = v___x_4416_;
                        v_isShared_4421_ = v_isSharedCheck_4425_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4418_);
                        lean_dec(v___x_4416_);
                        v___x_4420_ = lean_box(0);
                        v_isShared_4421_ = v_isSharedCheck_4425_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4421_ == 0 {
                    v___x_4423_ = v___x_4420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_val_4418_);
                    v___x_4423_ = v_reuseFailAlloc_4424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1___boxed(
    mut v_xs_4426_: *mut LeanObject,
    mut v_v_4427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4428_: *mut LeanObject = core::ptr::null_mut();
    v_res_4428_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1(v_xs_4426_, v_v_4427_);
    lean_dec(v_v_4427_);
    lean_dec_ref(v_xs_4426_);
    return v_res_4428_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4430_: *mut LeanObject = core::ptr::null_mut();
    v___x_4429_ = lean_box(0);
    v_dummy_4430_ = l_Lean_Expr_sort___override(v___x_4429_);
    return v_dummy_4430_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    v___x_4431_ = l_Array_instInhabited(lean_box(0));
    return v___x_4431_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0(
    mut v_recFnNames_4432_: *mut LeanObject,
    mut v_perms_4433_: *mut LeanObject,
    mut v___x_4434_: *mut LeanObject,
    mut v_a_4435_: *mut LeanObject,
    mut v_f_4436_: *mut LeanObject,
    mut v_e_4437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: u8 = 0;
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4447_: u8 = 0;
    let mut v_dummy_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4438_ = l_Lean_Expr_getAppFn(v_e_4437_);
                v___x_4439_ = l_Lean_Expr_isConst(v___x_4438_);
                if v___x_4439_ == 0 {
                    lean_dec_ref(v___x_4438_);
                    lean_dec_ref(v_e_4437_);
                    lean_dec_ref(v_f_4436_);
                    lean_dec_ref(v_a_4435_);
                    v___x_4440_ = lean_box(0);
                    return v___x_4440_;
                } else {
                    v___x_4441_ = l_Lean_Expr_constName_x21(v___x_4438_);
                    lean_dec_ref(v___x_4438_);
                    v___x_4442_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1(v_recFnNames_4432_, v___x_4441_);
                    lean_dec(v___x_4441_);
                    if lean_obj_tag(v___x_4442_) == 0 {
                        lean_dec_ref(v_e_4437_);
                        lean_dec_ref(v_f_4436_);
                        lean_dec_ref(v_a_4435_);
                        v___x_4443_ = lean_box(0);
                        return v___x_4443_;
                    } else {
                        v_val_4444_ = lean_ctor_get(v___x_4442_, 0);
                        v_isSharedCheck_4462_ = (!lean_is_exclusive(v___x_4442_)) as u8;
                        if v_isSharedCheck_4462_ == 0 {
                            v___x_4446_ = v___x_4442_;
                            v_isShared_4447_ = v_isSharedCheck_4462_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_4444_);
                            lean_dec(v___x_4442_);
                            v___x_4446_ = lean_box(0);
                            v_isShared_4447_ = v_isSharedCheck_4462_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_dummy_4448_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0);
                v_nargs_4449_ = l_Lean_Expr_getAppNumArgs(v_e_4437_);
                lean_inc(v_nargs_4449_);
                v___x_4450_ = lean_mk_array(v_nargs_4449_, v_dummy_4448_);
                v___x_4451_ = lean_unsigned_to_nat(1);
                v___x_4452_ = lean_nat_sub(v_nargs_4449_, v___x_4451_);
                lean_dec(v_nargs_4449_);
                v___x_4453_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_4437_,
                    v___x_4450_,
                    v___x_4452_,
                );
                v___x_4454_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
                v___x_4455_ = lean_array_get_borrowed(v___x_4454_, v_perms_4433_, v_val_4444_);
                v___x_4456_ =
                    l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_4455_, v___x_4453_);
                lean_dec_ref(v___x_4453_);
                v___x_4457_ =
                    l_Lean_Meta_PProdN_proj(v___x_4434_, v_val_4444_, v_a_4435_, v_f_4436_);
                lean_dec(v_val_4444_);
                v___x_4458_ = l_Lean_mkAppN(v___x_4457_, v___x_4456_);
                lean_dec_ref(v___x_4456_);
                if v_isShared_4447_ == 0 {
                    lean_ctor_set(v___x_4446_, 0, v___x_4458_);
                    v___x_4460_ = v___x_4446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4458_);
                    v___x_4460_ = v_reuseFailAlloc_4461_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___boxed(
    mut v_recFnNames_4463_: *mut LeanObject,
    mut v_perms_4464_: *mut LeanObject,
    mut v___x_4465_: *mut LeanObject,
    mut v_a_4466_: *mut LeanObject,
    mut v_f_4467_: *mut LeanObject,
    mut v_e_4468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4469_: *mut LeanObject = core::ptr::null_mut();
    v_res_4469_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0(v_recFnNames_4463_, v_perms_4464_, v___x_4465_, v_a_4466_, v_f_4467_, v_e_4468_);
    lean_dec(v___x_4465_);
    lean_dec_ref(v_perms_4464_);
    lean_dec_ref(v_recFnNames_4463_);
    return v_res_4469_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3()
-> *mut LeanObject {
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    v___x_4473_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__2;
    v___x_4474_ = lean_unsigned_to_nat(2);
    v___x_4475_ = lean_unsigned_to_nat(25);
    v___x_4476_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__1;
    v___x_4477_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0;
    v___x_4478_ = l_mkPanicMessageWithDecl(
        v___x_4477_,
        v___x_4476_,
        v___x_4475_,
        v___x_4474_,
        v___x_4473_,
    );
    return v___x_4478_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(
    mut v_recFnNames_4479_: *mut LeanObject,
    mut v_fixedParamPerms_4480_: *mut LeanObject,
    mut v_f_4481_: *mut LeanObject,
    mut v_e_4482_: *mut LeanObject,
    mut v_a_4483_: *mut LeanObject,
    mut v_a_4484_: *mut LeanObject,
    mut v_a_4485_: *mut LeanObject,
    mut v_a_4486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_perms_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: u8 = 0;
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4498_: u8 = 0;
    let mut v___f_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_perms_4488_ = lean_ctor_get(v_fixedParamPerms_4480_, 1);
                lean_inc_ref(v_perms_4488_);
                lean_dec_ref(v_fixedParamPerms_4480_);
                v___x_4489_ = lean_array_get_size(v_recFnNames_4479_);
                v___x_4490_ = lean_array_get_size(v_perms_4488_);
                v___x_4491_ = lean_nat_dec_eq(v___x_4489_, v___x_4490_);
                if v___x_4491_ == 0 {
                    lean_dec_ref(v_perms_4488_);
                    lean_dec_ref(v_f_4481_);
                    lean_dec_ref(v_recFnNames_4479_);
                    v___x_4492_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3);
                    v___x_4493_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0(v___x_4492_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_);
                    return v___x_4493_;
                } else {
                    lean_inc(v_a_4486_);
                    lean_inc_ref(v_a_4485_);
                    lean_inc(v_a_4484_);
                    lean_inc_ref(v_a_4483_);
                    lean_inc_ref(v_f_4481_);
                    v___x_4494_ =
                        lean_infer_type(v_f_4481_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_);
                    if lean_obj_tag(v___x_4494_) == 0 {
                        v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
                        v_isSharedCheck_4504_ = (!lean_is_exclusive(v___x_4494_)) as u8;
                        if v_isSharedCheck_4504_ == 0 {
                            v___x_4497_ = v___x_4494_;
                            v_isShared_4498_ = v_isSharedCheck_4504_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4495_);
                            lean_dec(v___x_4494_);
                            v___x_4497_ = lean_box(0);
                            v_isShared_4498_ = v_isSharedCheck_4504_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_perms_4488_);
                        lean_dec_ref(v_f_4481_);
                        lean_dec_ref(v_recFnNames_4479_);
                        return v___x_4494_;
                    }
                }
            }
            1 => {
                v___f_4499_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___f_4499_, 0, v_recFnNames_4479_);
                lean_closure_set(v___f_4499_, 1, v_perms_4488_);
                lean_closure_set(v___f_4499_, 2, v___x_4489_);
                lean_closure_set(v___f_4499_, 3, v_a_4495_);
                lean_closure_set(v___f_4499_, 4, v_f_4481_);
                v___x_4500_ = lean_replace_expr(v___f_4499_, v_e_4482_);
                lean_dec_ref(v___f_4499_);
                if v_isShared_4498_ == 0 {
                    lean_ctor_set(v___x_4497_, 0, v___x_4500_);
                    v___x_4502_ = v___x_4497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
                    v___x_4502_ = v_reuseFailAlloc_4503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___boxed(
    mut v_recFnNames_4505_: *mut LeanObject,
    mut v_fixedParamPerms_4506_: *mut LeanObject,
    mut v_f_4507_: *mut LeanObject,
    mut v_e_4508_: *mut LeanObject,
    mut v_a_4509_: *mut LeanObject,
    mut v_a_4510_: *mut LeanObject,
    mut v_a_4511_: *mut LeanObject,
    mut v_a_4512_: *mut LeanObject,
    mut v_a_4513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4514_: *mut LeanObject = core::ptr::null_mut();
    v_res_4514_ =
        l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(
            v_recFnNames_4505_,
            v_fixedParamPerms_4506_,
            v_f_4507_,
            v_e_4508_,
            v_a_4509_,
            v_a_4510_,
            v_a_4511_,
            v_a_4512_,
        );
    lean_dec(v_a_4512_);
    lean_dec_ref(v_a_4511_);
    lean_dec(v_a_4510_);
    lean_dec_ref(v_a_4509_);
    lean_dec_ref(v_e_4508_);
    return v_res_4514_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0(
    mut v_k_4515_: *mut LeanObject,
    mut v_b_4516_: *mut LeanObject,
    mut v_c_4517_: *mut LeanObject,
    mut v___y_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
    mut v___y_4520_: *mut LeanObject,
    mut v___y_4521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4521_);
    lean_inc_ref(v___y_4520_);
    lean_inc(v___y_4519_);
    lean_inc_ref(v___y_4518_);
    v___x_4523_ = lean_apply_7(
        v_k_4515_,
        v_b_4516_,
        v_c_4517_,
        v___y_4518_,
        v___y_4519_,
        v___y_4520_,
        v___y_4521_,
        lean_box(0),
    );
    return v___x_4523_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0___boxed(
    mut v_k_4524_: *mut LeanObject,
    mut v_b_4525_: *mut LeanObject,
    mut v_c_4526_: *mut LeanObject,
    mut v___y_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
    mut v___y_4529_: *mut LeanObject,
    mut v___y_4530_: *mut LeanObject,
    mut v___y_4531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4532_: *mut LeanObject = core::ptr::null_mut();
    v_res_4532_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0(v_k_4524_, v_b_4525_, v_c_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
    lean_dec(v___y_4530_);
    lean_dec_ref(v___y_4529_);
    lean_dec(v___y_4528_);
    lean_dec_ref(v___y_4527_);
    return v_res_4532_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(
    mut v_e_4533_: *mut LeanObject,
    mut v_k_4534_: *mut LeanObject,
    mut v_cleanupAnnotations_4535_: u8,
    mut v___y_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
    mut v___y_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: u8 = 0;
    let mut v___x_4543_: u8 = 0;
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4549_: u8 = 0;
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4553_: u8 = 0;
    let mut v_a_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4557_: u8 = 0;
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4541_ = lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_4541_, 0, v_k_4534_);
                v___x_4542_ = 1;
                v___x_4543_ = 0;
                v___x_4544_ = lean_box(0);
                v___x_4545_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
                    v_e_4533_,
                    v___x_4542_,
                    v___x_4543_,
                    v___x_4542_,
                    v___x_4543_,
                    v___x_4544_,
                    v___f_4541_,
                    v_cleanupAnnotations_4535_,
                    v___y_4536_,
                    v___y_4537_,
                    v___y_4538_,
                    v___y_4539_,
                );
                if lean_obj_tag(v___x_4545_) == 0 {
                    v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
                    v_isSharedCheck_4553_ = (!lean_is_exclusive(v___x_4545_)) as u8;
                    if v_isSharedCheck_4553_ == 0 {
                        v___x_4548_ = v___x_4545_;
                        v_isShared_4549_ = v_isSharedCheck_4553_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4546_);
                        lean_dec(v___x_4545_);
                        v___x_4548_ = lean_box(0);
                        v_isShared_4549_ = v_isSharedCheck_4553_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4554_ = lean_ctor_get(v___x_4545_, 0);
                    v_isSharedCheck_4561_ = (!lean_is_exclusive(v___x_4545_)) as u8;
                    if v_isSharedCheck_4561_ == 0 {
                        v___x_4556_ = v___x_4545_;
                        v_isShared_4557_ = v_isSharedCheck_4561_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4554_);
                        lean_dec(v___x_4545_);
                        v___x_4556_ = lean_box(0);
                        v_isShared_4557_ = v_isSharedCheck_4561_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4549_ == 0 {
                    v___x_4551_ = v___x_4548_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
                    v___x_4551_ = v_reuseFailAlloc_4552_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4551_;
            }
            3 => {
                if v_isShared_4557_ == 0 {
                    v___x_4559_ = v___x_4556_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
                    v___x_4559_ = v_reuseFailAlloc_4560_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___boxed(
    mut v_e_4562_: *mut LeanObject,
    mut v_k_4563_: *mut LeanObject,
    mut v_cleanupAnnotations_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
    mut v___y_4566_: *mut LeanObject,
    mut v___y_4567_: *mut LeanObject,
    mut v___y_4568_: *mut LeanObject,
    mut v___y_4569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4570_: u8 = 0;
    let mut v_res_4571_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4570_ = (lean_unbox(v_cleanupAnnotations_4564_) as u8);
    v_res_4571_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(v_e_4562_, v_k_4563_, v_cleanupAnnotations_boxed_4570_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
    lean_dec(v___y_4568_);
    lean_dec_ref(v___y_4567_);
    lean_dec(v___y_4566_);
    lean_dec_ref(v___y_4565_);
    return v_res_4571_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1(
    mut v_00_u03b1_4572_: *mut LeanObject,
    mut v_e_4573_: *mut LeanObject,
    mut v_k_4574_: *mut LeanObject,
    mut v_cleanupAnnotations_4575_: u8,
    mut v___y_4576_: *mut LeanObject,
    mut v___y_4577_: *mut LeanObject,
    mut v___y_4578_: *mut LeanObject,
    mut v___y_4579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    v___x_4581_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(v_e_4573_, v_k_4574_, v_cleanupAnnotations_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
    return v___x_4581_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___boxed(
    mut v_00_u03b1_4582_: *mut LeanObject,
    mut v_e_4583_: *mut LeanObject,
    mut v_k_4584_: *mut LeanObject,
    mut v_cleanupAnnotations_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
    mut v___y_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4591_: u8 = 0;
    let mut v_res_4592_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4591_ = (lean_unbox(v_cleanupAnnotations_4585_) as u8);
    v_res_4592_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1(v_00_u03b1_4582_, v_e_4583_, v_k_4584_, v_cleanupAnnotations_boxed_4591_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
    lean_dec(v___y_4589_);
    lean_dec_ref(v___y_4588_);
    lean_dec(v___y_4587_);
    lean_dec_ref(v___y_4586_);
    return v_res_4592_;
}
pub unsafe fn l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(
    mut v_e_4593_: *mut LeanObject,
    mut v_maxFVars_4594_: *mut LeanObject,
    mut v_k_4595_: *mut LeanObject,
    mut v_cleanupAnnotations_4596_: u8,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: u8 = 0;
    let mut v___x_4604_: u8 = 0;
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4610_: u8 = 0;
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4614_: u8 = 0;
    let mut v_a_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4618_: u8 = 0;
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4622_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4602_ = lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_4602_, 0, v_k_4595_);
                v___x_4603_ = 1;
                v___x_4604_ = 0;
                v___x_4605_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4605_, 0, v_maxFVars_4594_);
                v___x_4606_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
                    v_e_4593_,
                    v___x_4603_,
                    v___x_4604_,
                    v___x_4603_,
                    v___x_4604_,
                    v___x_4605_,
                    v___f_4602_,
                    v_cleanupAnnotations_4596_,
                    v___y_4597_,
                    v___y_4598_,
                    v___y_4599_,
                    v___y_4600_,
                );
                lean_dec_ref_known(v___x_4605_, 1);
                if lean_obj_tag(v___x_4606_) == 0 {
                    v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
                    v_isSharedCheck_4614_ = (!lean_is_exclusive(v___x_4606_)) as u8;
                    if v_isSharedCheck_4614_ == 0 {
                        v___x_4609_ = v___x_4606_;
                        v_isShared_4610_ = v_isSharedCheck_4614_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4607_);
                        lean_dec(v___x_4606_);
                        v___x_4609_ = lean_box(0);
                        v_isShared_4610_ = v_isSharedCheck_4614_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4615_ = lean_ctor_get(v___x_4606_, 0);
                    v_isSharedCheck_4622_ = (!lean_is_exclusive(v___x_4606_)) as u8;
                    if v_isSharedCheck_4622_ == 0 {
                        v___x_4617_ = v___x_4606_;
                        v_isShared_4618_ = v_isSharedCheck_4622_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4615_);
                        lean_dec(v___x_4606_);
                        v___x_4617_ = lean_box(0);
                        v_isShared_4618_ = v_isSharedCheck_4622_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4610_ == 0 {
                    v___x_4612_ = v___x_4609_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
                    v___x_4612_ = v_reuseFailAlloc_4613_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4612_;
            }
            3 => {
                if v_isShared_4618_ == 0 {
                    v___x_4620_ = v___x_4617_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
                    v___x_4620_ = v_reuseFailAlloc_4621_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg___boxed(
    mut v_e_4623_: *mut LeanObject,
    mut v_maxFVars_4624_: *mut LeanObject,
    mut v_k_4625_: *mut LeanObject,
    mut v_cleanupAnnotations_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4632_: u8 = 0;
    let mut v_res_4633_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4632_ = (lean_unbox(v_cleanupAnnotations_4626_) as u8);
    v_res_4633_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(v_e_4623_, v_maxFVars_4624_, v_k_4625_, v_cleanupAnnotations_boxed_4632_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
    lean_dec(v___y_4630_);
    lean_dec_ref(v___y_4629_);
    lean_dec(v___y_4628_);
    lean_dec_ref(v___y_4627_);
    return v_res_4633_;
}
pub unsafe fn l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3(
    mut v_00_u03b1_4634_: *mut LeanObject,
    mut v_e_4635_: *mut LeanObject,
    mut v_maxFVars_4636_: *mut LeanObject,
    mut v_k_4637_: *mut LeanObject,
    mut v_cleanupAnnotations_4638_: u8,
    mut v___y_4639_: *mut LeanObject,
    mut v___y_4640_: *mut LeanObject,
    mut v___y_4641_: *mut LeanObject,
    mut v___y_4642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(v_e_4635_, v_maxFVars_4636_, v_k_4637_, v_cleanupAnnotations_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
    return v___x_4644_;
}
pub unsafe fn l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___boxed(
    mut v_00_u03b1_4645_: *mut LeanObject,
    mut v_e_4646_: *mut LeanObject,
    mut v_maxFVars_4647_: *mut LeanObject,
    mut v_k_4648_: *mut LeanObject,
    mut v_cleanupAnnotations_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
    mut v___y_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4655_: u8 = 0;
    let mut v_res_4656_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4655_ = (lean_unbox(v_cleanupAnnotations_4649_) as u8);
    v_res_4656_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3(v_00_u03b1_4645_, v_e_4646_, v_maxFVars_4647_, v_k_4648_, v_cleanupAnnotations_boxed_4655_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
    lean_dec(v___y_4653_);
    lean_dec_ref(v___y_4652_);
    lean_dec(v___y_4651_);
    lean_dec_ref(v___y_4650_);
    return v_res_4656_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0(
    mut v___x_4657_: *mut LeanObject,
    mut v_a_4658_: *mut LeanObject,
    mut v_e_4659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4660_: u8 = 0;
    v___x_4660_ = lean_expr_eqv(v_e_4659_, v___x_4657_);
    if v___x_4660_ == 0 {
        let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_a_4658_);
        v___x_4661_ = lean_box(0);
        return v___x_4661_;
    } else {
        let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
        v___x_4662_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4662_, 0, v_a_4658_);
        return v___x_4662_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0___boxed(
    mut v___x_4663_: *mut LeanObject,
    mut v_a_4664_: *mut LeanObject,
    mut v_e_4665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4666_: *mut LeanObject = core::ptr::null_mut();
    v_res_4666_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0(v___x_4663_, v_a_4664_, v_e_4665_);
    lean_dec_ref(v_e_4665_);
    lean_dec_ref(v___x_4663_);
    return v_res_4666_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1(
    mut v___x_4667_: *mut LeanObject,
    mut v___x_4668_: *mut LeanObject,
    mut v_a_4669_: *mut LeanObject,
    mut v_f_4670_: *mut LeanObject,
    mut v_e_4671_: *mut LeanObject,
    mut v___y_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    v___x_4677_ = lean_array_get_borrowed(v___x_4667_, v_f_4670_, v___x_4668_);
    lean_inc(v___x_4677_);
    v___f_4678_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___f_4678_, 0, v___x_4677_);
    lean_closure_set(v___f_4678_, 1, v_a_4669_);
    v___x_4679_ = lean_replace_expr(v___f_4678_, v_e_4671_);
    lean_dec_ref(v___f_4678_);
    v___x_4680_ = l_Lean_Meta_PProdN_reduceProjs(
        v___x_4679_,
        v___y_4672_,
        v___y_4673_,
        v___y_4674_,
        v___y_4675_,
    );
    if lean_obj_tag(v___x_4680_) == 0 {
        let mut v_a_4681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
        v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
        lean_inc(v_a_4681_);
        lean_dec_ref_known(v___x_4680_, 1);
        v___x_4682_ = l_Lean_Core_betaReduce(v_a_4681_, v___y_4674_, v___y_4675_);
        return v___x_4682_;
    } else {
        return v___x_4680_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1___boxed(
    mut v___x_4683_: *mut LeanObject,
    mut v___x_4684_: *mut LeanObject,
    mut v_a_4685_: *mut LeanObject,
    mut v_f_4686_: *mut LeanObject,
    mut v_e_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
    mut v___y_4692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4693_: *mut LeanObject = core::ptr::null_mut();
    v_res_4693_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1(v___x_4683_, v___x_4684_, v_a_4685_, v_f_4686_, v_e_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
    lean_dec(v___y_4691_);
    lean_dec_ref(v___y_4690_);
    lean_dec(v___y_4689_);
    lean_dec_ref(v___y_4688_);
    lean_dec_ref(v_e_4687_);
    lean_dec_ref(v_f_4686_);
    lean_dec(v___x_4684_);
    lean_dec_ref(v___x_4683_);
    return v_res_4693_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(
    mut v_as_4694_: *mut LeanObject,
    mut v_i_4695_: usize,
    mut v_stop_4696_: usize,
    mut v_b_4697_: *mut LeanObject,
    mut v___y_4698_: *mut LeanObject,
    mut v___y_4699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4701_: u8 = 0;
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: usize = 0;
    let mut v___x_4706_: usize = 0;
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4701_ = lean_usize_dec_eq(v_i_4695_, v_stop_4696_);
                if v___x_4701_ == 0 {
                    v___x_4702_ = lean_array_uget_borrowed(v_as_4694_, v_i_4695_);
                    v___x_4703_ =
                        l_Lean_Elab_addAsAxiom___redArg(v___x_4702_, v___y_4698_, v___y_4699_);
                    if lean_obj_tag(v___x_4703_) == 0 {
                        v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
                        lean_inc(v_a_4704_);
                        lean_dec_ref_known(v___x_4703_, 1);
                        v___x_4705_ = 1usize;
                        v___x_4706_ = lean_usize_add(v_i_4695_, v___x_4705_);
                        v_i_4695_ = v___x_4706_;
                        v_b_4697_ = v_a_4704_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4703_;
                    }
                } else {
                    v___x_4708_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4708_, 0, v_b_4697_);
                    return v___x_4708_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg___boxed(
    mut v_as_4709_: *mut LeanObject,
    mut v_i_4710_: *mut LeanObject,
    mut v_stop_4711_: *mut LeanObject,
    mut v_b_4712_: *mut LeanObject,
    mut v___y_4713_: *mut LeanObject,
    mut v___y_4714_: *mut LeanObject,
    mut v___y_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4716_: usize = 0;
    let mut v_stop_boxed_4717_: usize = 0;
    let mut v_res_4718_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4716_ = lean_unbox_usize(v_i_4710_);
    lean_dec(v_i_4710_);
    v_stop_boxed_4717_ = lean_unbox_usize(v_stop_4711_);
    lean_dec(v_stop_4711_);
    v_res_4718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_as_4709_, v_i_boxed_4716_, v_stop_boxed_4717_, v_b_4712_, v___y_4713_, v___y_4714_);
    lean_dec(v___y_4714_);
    lean_dec_ref(v___y_4713_);
    lean_dec_ref(v_as_4709_);
    return v_res_4718_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(
    mut v_a_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4726_: u8 = 0;
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4732_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4719_) == 0 {
                    v___x_4721_ = l_List_reverse___redArg(v_a_4720_);
                    return v___x_4721_;
                } else {
                    v_head_4722_ = lean_ctor_get(v_a_4719_, 0);
                    v_tail_4723_ = lean_ctor_get(v_a_4719_, 1);
                    v_isSharedCheck_4732_ = (!lean_is_exclusive(v_a_4719_)) as u8;
                    if v_isSharedCheck_4732_ == 0 {
                        v___x_4725_ = v_a_4719_;
                        v_isShared_4726_ = v_isSharedCheck_4732_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4723_);
                        lean_inc(v_head_4722_);
                        lean_dec(v_a_4719_);
                        v___x_4725_ = lean_box(0);
                        v_isShared_4726_ = v_isSharedCheck_4732_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4727_ = l_Lean_mkLevelParam(v_head_4722_);
                if v_isShared_4726_ == 0 {
                    lean_ctor_set(v___x_4725_, 1, v_a_4720_);
                    lean_ctor_set(v___x_4725_, 0, v___x_4727_);
                    v___x_4729_ = v___x_4725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4731_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4727_);
                    lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_a_4720_);
                    v___x_4729_ = v_reuseFailAlloc_4731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4719_ = v_tail_4723_;
                v_a_4720_ = v___x_4729_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0(
    mut v___x_4733_: *mut LeanObject,
    mut v___x_4734_: *mut LeanObject,
    mut v_fixedArgs_4735_: *mut LeanObject,
    mut v_isZero_4736_: u8,
    mut v_xs_4737_: *mut LeanObject,
    mut v_x_4738_: *mut LeanObject,
    mut v___y_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
    mut v___y_4742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_levelParams_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: u8 = 0;
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    v_levelParams_4744_ = lean_ctor_get(v___x_4733_, 1);
    lean_inc(v_levelParams_4744_);
    v_declName_4745_ = lean_ctor_get(v___x_4733_, 3);
    lean_inc(v_declName_4745_);
    lean_dec_ref(v___x_4733_);
    lean_inc_ref(v_xs_4737_);
    v___x_4746_ =
        l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_4734_, v_fixedArgs_4735_, v_xs_4737_);
    v___x_4747_ = lean_box(0);
    v___x_4748_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(v_levelParams_4744_, v___x_4747_);
    v___x_4749_ = l_Lean_Expr_const___override(v_declName_4745_, v___x_4748_);
    v___x_4750_ = l_Lean_mkAppN(v___x_4749_, v___x_4746_);
    lean_dec_ref(v___x_4746_);
    v___x_4751_ = 1;
    v___x_4752_ = 1;
    v___x_4753_ = l_Lean_Meta_mkLambdaFVars(
        v_xs_4737_,
        v___x_4750_,
        v_isZero_4736_,
        v___x_4751_,
        v___x_4751_,
        v___x_4751_,
        v___x_4752_,
        v___y_4739_,
        v___y_4740_,
        v___y_4741_,
        v___y_4742_,
    );
    lean_dec_ref(v_xs_4737_);
    return v___x_4753_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0___boxed(
    mut v___x_4754_: *mut LeanObject,
    mut v___x_4755_: *mut LeanObject,
    mut v_fixedArgs_4756_: *mut LeanObject,
    mut v_isZero_4757_: *mut LeanObject,
    mut v_xs_4758_: *mut LeanObject,
    mut v_x_4759_: *mut LeanObject,
    mut v___y_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
    mut v___y_4762_: *mut LeanObject,
    mut v___y_4763_: *mut LeanObject,
    mut v___y_4764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_4765_: u8 = 0;
    let mut v_res_4766_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_4765_ = (lean_unbox(v_isZero_4757_) as u8);
    v_res_4766_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0(v___x_4754_, v___x_4755_, v_fixedArgs_4756_, v_isZero_boxed_4765_, v_xs_4758_, v_x_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
    lean_dec(v___y_4763_);
    lean_dec_ref(v___y_4762_);
    lean_dec(v___y_4761_);
    lean_dec_ref(v___y_4760_);
    lean_dec_ref(v_x_4759_);
    lean_dec_ref(v_fixedArgs_4756_);
    return v_res_4766_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(
    mut v_fixedParamPerms_4767_: *mut LeanObject,
    mut v_fixedArgs_4768_: *mut LeanObject,
    mut v_as_4769_: *mut LeanObject,
    mut v_i_4770_: *mut LeanObject,
    mut v_j_4771_: *mut LeanObject,
    mut v_bs_4772_: *mut LeanObject,
    mut v___y_4773_: *mut LeanObject,
    mut v___y_4774_: *mut LeanObject,
    mut v___y_4775_: *mut LeanObject,
    mut v___y_4776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_4779_: u8 = 0;
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perms_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4778_ = lean_unsigned_to_nat(0);
                v_isZero_4779_ = lean_nat_dec_eq(v_i_4770_, v_zero_4778_);
                if v_isZero_4779_ == 1 {
                    lean_dec(v_j_4771_);
                    lean_dec(v_i_4770_);
                    lean_dec_ref(v_fixedArgs_4768_);
                    v___x_4780_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4780_, 0, v_bs_4772_);
                    return v___x_4780_;
                } else {
                    v_perms_4781_ = lean_ctor_get(v_fixedParamPerms_4767_, 1);
                    v___x_4782_ = lean_array_fget_borrowed(v_as_4769_, v_j_4771_);
                    v_value_4783_ = lean_ctor_get(v___x_4782_, 7);
                    v___x_4784_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
                    v_one_4785_ = lean_unsigned_to_nat(1);
                    v_n_4786_ = lean_nat_sub(v_i_4770_, v_one_4785_);
                    lean_dec(v_i_4770_);
                    v___x_4801_ = lean_array_get_borrowed(v___x_4784_, v_perms_4781_, v_j_4771_);
                    lean_inc_ref(v_fixedArgs_4768_);
                    lean_inc_ref(v_value_4783_);
                    lean_inc(v___x_4801_);
                    v___x_4802_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(
                        v___x_4801_,
                        v_value_4783_,
                        v_fixedArgs_4768_,
                        v___y_4773_,
                        v___y_4774_,
                        v___y_4775_,
                        v___y_4776_,
                    );
                    if lean_obj_tag(v___x_4802_) == 0 {
                        v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
                        lean_inc(v_a_4803_);
                        lean_dec_ref_known(v___x_4802_, 1);
                        v___x_4804_ = lean_box((v_isZero_4779_) as usize);
                        lean_inc_ref(v_fixedArgs_4768_);
                        lean_inc(v___x_4801_);
                        lean_inc(v___x_4782_);
                        v___f_4805_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
                        lean_closure_set(v___f_4805_, 0, v___x_4782_);
                        lean_closure_set(v___f_4805_, 1, v___x_4801_);
                        lean_closure_set(v___f_4805_, 2, v_fixedArgs_4768_);
                        lean_closure_set(v___f_4805_, 3, v___x_4804_);
                        v___x_4806_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(v_a_4803_, v___f_4805_, v_isZero_4779_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
                        v___y_4788_ = v___x_4806_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4788_ = v___x_4802_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_4788_) == 0 {
                    v_a_4789_ = lean_ctor_get(v___y_4788_, 0);
                    lean_inc(v_a_4789_);
                    lean_dec_ref_known(v___y_4788_, 1);
                    v___x_4790_ = lean_nat_add(v_j_4771_, v_one_4785_);
                    lean_dec(v_j_4771_);
                    v___x_4791_ = lean_array_push(v_bs_4772_, v_a_4789_);
                    v_i_4770_ = v_n_4786_;
                    v_j_4771_ = v___x_4790_;
                    v_bs_4772_ = v___x_4791_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_n_4786_);
                    lean_dec_ref(v_bs_4772_);
                    lean_dec(v_j_4771_);
                    lean_dec_ref(v_fixedArgs_4768_);
                    v_a_4793_ = lean_ctor_get(v___y_4788_, 0);
                    v_isSharedCheck_4800_ = (!lean_is_exclusive(v___y_4788_)) as u8;
                    if v_isSharedCheck_4800_ == 0 {
                        v___x_4795_ = v___y_4788_;
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4793_);
                        lean_dec(v___y_4788_);
                        v___x_4795_ = lean_box(0);
                        v_isShared_4796_ = v_isSharedCheck_4800_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4796_ == 0 {
                    v___x_4798_ = v___x_4795_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
                    v___x_4798_ = v_reuseFailAlloc_4799_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___boxed(
    mut v_fixedParamPerms_4807_: *mut LeanObject,
    mut v_fixedArgs_4808_: *mut LeanObject,
    mut v_as_4809_: *mut LeanObject,
    mut v_i_4810_: *mut LeanObject,
    mut v_j_4811_: *mut LeanObject,
    mut v_bs_4812_: *mut LeanObject,
    mut v___y_4813_: *mut LeanObject,
    mut v___y_4814_: *mut LeanObject,
    mut v___y_4815_: *mut LeanObject,
    mut v___y_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4818_: *mut LeanObject = core::ptr::null_mut();
    v_res_4818_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_4807_, v_fixedArgs_4808_, v_as_4809_, v_i_4810_, v_j_4811_, v_bs_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
    lean_dec(v___y_4816_);
    lean_dec_ref(v___y_4815_);
    lean_dec(v___y_4814_);
    lean_dec_ref(v___y_4813_);
    lean_dec_ref(v_as_4809_);
    lean_dec_ref(v_fixedParamPerms_4807_);
    return v_res_4818_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2(
    mut v___x_4819_: *mut LeanObject,
    mut v_fixedParamPerms_4820_: *mut LeanObject,
    mut v_fixedArgs_4821_: *mut LeanObject,
    mut v_preDefs_4822_: *mut LeanObject,
    mut v___x_4823_: *mut LeanObject,
    mut v___x_4824_: *mut LeanObject,
    mut v_F_4825_: *mut LeanObject,
    mut v_k_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
    mut v___y_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: u8 = 0;
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4848_: u8 = 0;
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4852_: u8 = 0;
    let mut v_a_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4856_: u8 = 0;
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4860_: u8 = 0;
    let mut v_a_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4868_: u8 = 0;
    let mut v___y_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4878_: u8 = 0;
    let mut v___x_4879_: u8 = 0;
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: u8 = 0;
    let mut v___x_4882_: usize = 0;
    let mut v___x_4883_: usize = 0;
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: usize = 0;
    let mut v___x_4886_: usize = 0;
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4879_ = lean_nat_dec_lt(v___x_4823_, v___x_4819_);
                if v___x_4879_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_4880_ = lean_box(0);
                    v___x_4881_ = lean_nat_dec_le(v___x_4819_, v___x_4819_);
                    if v___x_4881_ == 0 {
                        if v___x_4879_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_4882_ = 0usize;
                            v___x_4883_ = lean_usize_of_nat(v___x_4819_);
                            v___x_4884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_preDefs_4822_, v___x_4882_, v___x_4883_, v___x_4880_, v___y_4829_, v___y_4830_);
                            v___y_4870_ = v___x_4884_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_4885_ = 0usize;
                        v___x_4886_ = lean_usize_of_nat(v___x_4819_);
                        v___x_4887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_preDefs_4822_, v___x_4885_, v___x_4886_, v___x_4880_, v___y_4829_, v___y_4830_);
                        v___y_4870_ = v___x_4887_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4833_ = lean_mk_empty_array_with_capacity(v___x_4819_);
                lean_inc(v___x_4823_);
                v___x_4834_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_4820_, v_fixedArgs_4821_, v_preDefs_4822_, v___x_4819_, v___x_4823_, v___x_4833_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_);
                if lean_obj_tag(v___x_4834_) == 0 {
                    v_a_4835_ = lean_ctor_get(v___x_4834_, 0);
                    lean_inc(v_a_4835_);
                    lean_dec_ref_known(v___x_4834_, 1);
                    v___x_4836_ = l_Lean_Level_ofNat(v___x_4823_);
                    v___x_4837_ = l_Lean_Meta_PProdN_mk(
                        v___x_4836_,
                        v_a_4835_,
                        v___y_4827_,
                        v___y_4828_,
                        v___y_4829_,
                        v___y_4830_,
                    );
                    if lean_obj_tag(v___x_4837_) == 0 {
                        v_a_4838_ = lean_ctor_get(v___x_4837_, 0);
                        lean_inc(v_a_4838_);
                        lean_dec_ref_known(v___x_4837_, 1);
                        v___f_4839_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                        lean_closure_set(v___f_4839_, 0, v___x_4824_);
                        lean_closure_set(v___f_4839_, 1, v___x_4823_);
                        lean_closure_set(v___f_4839_, 2, v_a_4838_);
                        v___x_4840_ = lean_unsigned_to_nat(1);
                        v___x_4841_ = 0;
                        v___x_4842_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(v_F_4825_, v___x_4840_, v___f_4839_, v___x_4841_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_);
                        if lean_obj_tag(v___x_4842_) == 0 {
                            v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
                            lean_inc(v_a_4843_);
                            lean_dec_ref_known(v___x_4842_, 1);
                            v___x_4844_ = lean_apply_6(
                                v_k_4826_,
                                v_a_4843_,
                                v___y_4827_,
                                v___y_4828_,
                                v___y_4829_,
                                v___y_4830_,
                                lean_box(0),
                            );
                            return v___x_4844_;
                        } else {
                            lean_dec(v___y_4830_);
                            lean_dec_ref(v___y_4829_);
                            lean_dec(v___y_4828_);
                            lean_dec_ref(v___y_4827_);
                            lean_dec_ref(v_k_4826_);
                            v_a_4845_ = lean_ctor_get(v___x_4842_, 0);
                            v_isSharedCheck_4852_ = (!lean_is_exclusive(v___x_4842_)) as u8;
                            if v_isSharedCheck_4852_ == 0 {
                                v___x_4847_ = v___x_4842_;
                                v_isShared_4848_ = v_isSharedCheck_4852_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_4845_);
                                lean_dec(v___x_4842_);
                                v___x_4847_ = lean_box(0);
                                v_isShared_4848_ = v_isSharedCheck_4852_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_4830_);
                        lean_dec_ref(v___y_4829_);
                        lean_dec(v___y_4828_);
                        lean_dec_ref(v___y_4827_);
                        lean_dec_ref(v_k_4826_);
                        lean_dec_ref(v_F_4825_);
                        lean_dec_ref(v___x_4824_);
                        lean_dec(v___x_4823_);
                        v_a_4853_ = lean_ctor_get(v___x_4837_, 0);
                        v_isSharedCheck_4860_ = (!lean_is_exclusive(v___x_4837_)) as u8;
                        if v_isSharedCheck_4860_ == 0 {
                            v___x_4855_ = v___x_4837_;
                            v_isShared_4856_ = v_isSharedCheck_4860_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4853_);
                            lean_dec(v___x_4837_);
                            v___x_4855_ = lean_box(0);
                            v_isShared_4856_ = v_isSharedCheck_4860_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_4830_);
                    lean_dec_ref(v___y_4829_);
                    lean_dec(v___y_4828_);
                    lean_dec_ref(v___y_4827_);
                    lean_dec_ref(v_k_4826_);
                    lean_dec_ref(v_F_4825_);
                    lean_dec_ref(v___x_4824_);
                    lean_dec(v___x_4823_);
                    v_a_4861_ = lean_ctor_get(v___x_4834_, 0);
                    v_isSharedCheck_4868_ = (!lean_is_exclusive(v___x_4834_)) as u8;
                    if v_isSharedCheck_4868_ == 0 {
                        v___x_4863_ = v___x_4834_;
                        v_isShared_4864_ = v_isSharedCheck_4868_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4861_);
                        lean_dec(v___x_4834_);
                        v___x_4863_ = lean_box(0);
                        v_isShared_4864_ = v_isSharedCheck_4868_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4848_ == 0 {
                    v___x_4850_ = v___x_4847_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
                    v___x_4850_ = v_reuseFailAlloc_4851_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4850_;
            }
            4 => {
                if v_isShared_4856_ == 0 {
                    v___x_4858_ = v___x_4855_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
                    v___x_4858_ = v_reuseFailAlloc_4859_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4858_;
            }
            6 => {
                if v_isShared_4864_ == 0 {
                    v___x_4866_ = v___x_4863_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
                    v___x_4866_ = v_reuseFailAlloc_4867_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4866_;
            }
            8 => {
                if lean_obj_tag(v___y_4870_) == 0 {
                    lean_dec_ref_known(v___y_4870_, 1);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_4830_);
                    lean_dec_ref(v___y_4829_);
                    lean_dec(v___y_4828_);
                    lean_dec_ref(v___y_4827_);
                    lean_dec_ref(v_k_4826_);
                    lean_dec_ref(v_F_4825_);
                    lean_dec_ref(v___x_4824_);
                    lean_dec(v___x_4823_);
                    lean_dec_ref(v_fixedArgs_4821_);
                    lean_dec(v___x_4819_);
                    v_a_4871_ = lean_ctor_get(v___y_4870_, 0);
                    v_isSharedCheck_4878_ = (!lean_is_exclusive(v___y_4870_)) as u8;
                    if v_isSharedCheck_4878_ == 0 {
                        v___x_4873_ = v___y_4870_;
                        v_isShared_4874_ = v_isSharedCheck_4878_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4871_);
                        lean_dec(v___y_4870_);
                        v___x_4873_ = lean_box(0);
                        v_isShared_4874_ = v_isSharedCheck_4878_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4874_ == 0 {
                    v___x_4876_ = v___x_4873_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
                    v___x_4876_ = v_reuseFailAlloc_4877_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2___boxed(
    mut v___x_4888_: *mut LeanObject,
    mut v_fixedParamPerms_4889_: *mut LeanObject,
    mut v_fixedArgs_4890_: *mut LeanObject,
    mut v_preDefs_4891_: *mut LeanObject,
    mut v___x_4892_: *mut LeanObject,
    mut v___x_4893_: *mut LeanObject,
    mut v_F_4894_: *mut LeanObject,
    mut v_k_4895_: *mut LeanObject,
    mut v___y_4896_: *mut LeanObject,
    mut v___y_4897_: *mut LeanObject,
    mut v___y_4898_: *mut LeanObject,
    mut v___y_4899_: *mut LeanObject,
    mut v___y_4900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4901_: *mut LeanObject = core::ptr::null_mut();
    v_res_4901_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2(v___x_4888_, v_fixedParamPerms_4889_, v_fixedArgs_4890_, v_preDefs_4891_, v___x_4892_, v___x_4893_, v_F_4894_, v_k_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
    lean_dec_ref(v_preDefs_4891_);
    lean_dec_ref(v_fixedParamPerms_4889_);
    return v_res_4901_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    v___x_4902_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4902_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    v___x_4903_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0);
    v___x_4904_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4904_, 0, v___x_4903_);
    return v___x_4904_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    v___x_4905_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1);
    v___x_4906_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4906_, 0, v___x_4905_);
    lean_ctor_set(v___x_4906_, 1, v___x_4905_);
    return v___x_4906_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    v___x_4907_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1);
    v___x_4908_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4908_, 0, v___x_4907_);
    lean_ctor_set(v___x_4908_, 1, v___x_4907_);
    lean_ctor_set(v___x_4908_, 2, v___x_4907_);
    lean_ctor_set(v___x_4908_, 3, v___x_4907_);
    lean_ctor_set(v___x_4908_, 4, v___x_4907_);
    lean_ctor_set(v___x_4908_, 5, v___x_4907_);
    return v___x_4908_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(
    mut v_env_4909_: *mut LeanObject,
    mut v___y_4910_: *mut LeanObject,
    mut v___y_4911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4923_: u8 = 0;
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4943_: u8 = 0;
    let mut v_unused_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4946_: u8 = 0;
    let mut v_unused_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4913_ = lean_st_ref_take(v___y_4911_);
                v_nextMacroScope_4914_ = lean_ctor_get(v___x_4913_, 1);
                v_ngen_4915_ = lean_ctor_get(v___x_4913_, 2);
                v_auxDeclNGen_4916_ = lean_ctor_get(v___x_4913_, 3);
                v_traceState_4917_ = lean_ctor_get(v___x_4913_, 4);
                v_messages_4918_ = lean_ctor_get(v___x_4913_, 6);
                v_infoState_4919_ = lean_ctor_get(v___x_4913_, 7);
                v_snapshotTasks_4920_ = lean_ctor_get(v___x_4913_, 8);
                v_isSharedCheck_4946_ = (!lean_is_exclusive(v___x_4913_)) as u8;
                if v_isSharedCheck_4946_ == 0 {
                    v_unused_4947_ = lean_ctor_get(v___x_4913_, 5);
                    lean_dec(v_unused_4947_);
                    v_unused_4948_ = lean_ctor_get(v___x_4913_, 0);
                    lean_dec(v_unused_4948_);
                    v___x_4922_ = v___x_4913_;
                    v_isShared_4923_ = v_isSharedCheck_4946_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4920_);
                    lean_inc(v_infoState_4919_);
                    lean_inc(v_messages_4918_);
                    lean_inc(v_traceState_4917_);
                    lean_inc(v_auxDeclNGen_4916_);
                    lean_inc(v_ngen_4915_);
                    lean_inc(v_nextMacroScope_4914_);
                    lean_dec(v___x_4913_);
                    v___x_4922_ = lean_box(0);
                    v_isShared_4923_ = v_isSharedCheck_4946_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4924_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
                if v_isShared_4923_ == 0 {
                    lean_ctor_set(v___x_4922_, 5, v___x_4924_);
                    lean_ctor_set(v___x_4922_, 0, v_env_4909_);
                    v___x_4926_ = v___x_4922_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4945_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_env_4909_);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 1, v_nextMacroScope_4914_);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 2, v_ngen_4915_);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 3, v_auxDeclNGen_4916_);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 4, v_traceState_4917_);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 5, v___x_4924_);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 6, v_messages_4918_);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 7, v_infoState_4919_);
                    lean_ctor_set(v_reuseFailAlloc_4945_, 8, v_snapshotTasks_4920_);
                    v___x_4926_ = v_reuseFailAlloc_4945_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4927_ = lean_st_ref_set(v___y_4911_, v___x_4926_);
                v___x_4928_ = lean_st_ref_take(v___y_4910_);
                v_mctx_4929_ = lean_ctor_get(v___x_4928_, 0);
                v_zetaDeltaFVarIds_4930_ = lean_ctor_get(v___x_4928_, 2);
                v_postponed_4931_ = lean_ctor_get(v___x_4928_, 3);
                v_diag_4932_ = lean_ctor_get(v___x_4928_, 4);
                v_isSharedCheck_4943_ = (!lean_is_exclusive(v___x_4928_)) as u8;
                if v_isSharedCheck_4943_ == 0 {
                    v_unused_4944_ = lean_ctor_get(v___x_4928_, 1);
                    lean_dec(v_unused_4944_);
                    v___x_4934_ = v___x_4928_;
                    v_isShared_4935_ = v_isSharedCheck_4943_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_4932_);
                    lean_inc(v_postponed_4931_);
                    lean_inc(v_zetaDeltaFVarIds_4930_);
                    lean_inc(v_mctx_4929_);
                    lean_dec(v___x_4928_);
                    v___x_4934_ = lean_box(0);
                    v_isShared_4935_ = v_isSharedCheck_4943_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4936_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
                if v_isShared_4935_ == 0 {
                    lean_ctor_set(v___x_4934_, 1, v___x_4936_);
                    v___x_4938_ = v___x_4934_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_mctx_4929_);
                    lean_ctor_set(v_reuseFailAlloc_4942_, 1, v___x_4936_);
                    lean_ctor_set(v_reuseFailAlloc_4942_, 2, v_zetaDeltaFVarIds_4930_);
                    lean_ctor_set(v_reuseFailAlloc_4942_, 3, v_postponed_4931_);
                    lean_ctor_set(v_reuseFailAlloc_4942_, 4, v_diag_4932_);
                    v___x_4938_ = v_reuseFailAlloc_4942_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4939_ = lean_st_ref_set(v___y_4910_, v___x_4938_);
                v___x_4940_ = lean_box(0);
                v___x_4941_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4941_, 0, v___x_4940_);
                return v___x_4941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___boxed(
    mut v_env_4949_: *mut LeanObject,
    mut v___y_4950_: *mut LeanObject,
    mut v___y_4951_: *mut LeanObject,
    mut v___y_4952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4953_: *mut LeanObject = core::ptr::null_mut();
    v_res_4953_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_4949_, v___y_4950_, v___y_4951_);
    lean_dec(v___y_4951_);
    lean_dec(v___y_4950_);
    return v_res_4953_;
}
pub unsafe fn l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(
    mut v_env_4954_: *mut LeanObject,
    mut v_x_4955_: *mut LeanObject,
    mut v___y_4956_: *mut LeanObject,
    mut v___y_4957_: *mut LeanObject,
    mut v___y_4958_: *mut LeanObject,
    mut v___y_4959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4968_: u8 = 0;
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4972_: u8 = 0;
    let mut v_unused_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4984_: u8 = 0;
    let mut v_unused_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4961_ = lean_st_ref_get(v___y_4959_);
                v_env_4962_ = lean_ctor_get(v___x_4961_, 0);
                lean_inc_ref(v_env_4962_);
                lean_dec(v___x_4961_);
                v___x_4974_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_4954_, v___y_4957_, v___y_4959_);
                lean_dec_ref(v___x_4974_);
                lean_inc(v___y_4959_);
                lean_inc_ref(v___y_4958_);
                lean_inc(v___y_4957_);
                lean_inc_ref(v___y_4956_);
                v___x_4975_ = lean_apply_5(
                    v_x_4955_,
                    v___y_4956_,
                    v___y_4957_,
                    v___y_4958_,
                    v___y_4959_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4975_) == 0 {
                    v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
                    lean_inc(v_a_4976_);
                    lean_dec_ref_known(v___x_4975_, 1);
                    v___x_4977_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_4962_, v___y_4957_, v___y_4959_);
                    v_isSharedCheck_4984_ = (!lean_is_exclusive(v___x_4977_)) as u8;
                    if v_isSharedCheck_4984_ == 0 {
                        v_unused_4985_ = lean_ctor_get(v___x_4977_, 0);
                        lean_dec(v_unused_4985_);
                        v___x_4979_ = v___x_4977_;
                        v_isShared_4980_ = v_isSharedCheck_4984_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_4977_);
                        v___x_4979_ = lean_box(0);
                        v_isShared_4980_ = v_isSharedCheck_4984_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4986_ = lean_ctor_get(v___x_4975_, 0);
                    lean_inc(v_a_4986_);
                    lean_dec_ref_known(v___x_4975_, 1);
                    v_a_4964_ = v_a_4986_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4965_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_4962_, v___y_4957_, v___y_4959_);
                v_isSharedCheck_4972_ = (!lean_is_exclusive(v___x_4965_)) as u8;
                if v_isSharedCheck_4972_ == 0 {
                    v_unused_4973_ = lean_ctor_get(v___x_4965_, 0);
                    lean_dec(v_unused_4973_);
                    v___x_4967_ = v___x_4965_;
                    v_isShared_4968_ = v_isSharedCheck_4972_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_4965_);
                    v___x_4967_ = lean_box(0);
                    v_isShared_4968_ = v_isSharedCheck_4972_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4968_ == 0 {
                    lean_ctor_set_tag(v___x_4967_, 1);
                    lean_ctor_set(v___x_4967_, 0, v_a_4964_);
                    v___x_4970_ = v___x_4967_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4971_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4964_);
                    v___x_4970_ = v_reuseFailAlloc_4971_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4970_;
            }
            4 => {
                if v_isShared_4980_ == 0 {
                    lean_ctor_set(v___x_4979_, 0, v_a_4976_);
                    v___x_4982_ = v___x_4979_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4983_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4976_);
                    v___x_4982_ = v_reuseFailAlloc_4983_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg___boxed(
    mut v_env_4987_: *mut LeanObject,
    mut v_x_4988_: *mut LeanObject,
    mut v___y_4989_: *mut LeanObject,
    mut v___y_4990_: *mut LeanObject,
    mut v___y_4991_: *mut LeanObject,
    mut v___y_4992_: *mut LeanObject,
    mut v___y_4993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4994_: *mut LeanObject = core::ptr::null_mut();
    v_res_4994_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v_env_4987_, v_x_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
    lean_dec(v___y_4992_);
    lean_dec_ref(v___y_4991_);
    lean_dec(v___y_4990_);
    lean_dec_ref(v___y_4989_);
    return v_res_4994_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(
    mut v_msgData_4995_: *mut LeanObject,
    mut v___y_4996_: *mut LeanObject,
    mut v___y_4997_: *mut LeanObject,
    mut v___y_4998_: *mut LeanObject,
    mut v___y_4999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    v___x_5001_ = lean_st_ref_get(v___y_4999_);
    v_env_5002_ = lean_ctor_get(v___x_5001_, 0);
    lean_inc_ref(v_env_5002_);
    lean_dec(v___x_5001_);
    v___x_5003_ = lean_st_ref_get(v___y_4997_);
    v_mctx_5004_ = lean_ctor_get(v___x_5003_, 0);
    lean_inc_ref(v_mctx_5004_);
    lean_dec(v___x_5003_);
    v_lctx_5005_ = lean_ctor_get(v___y_4996_, 2);
    v_options_5006_ = lean_ctor_get(v___y_4998_, 2);
    lean_inc_ref(v_options_5006_);
    lean_inc_ref(v_lctx_5005_);
    v___x_5007_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_5007_, 0, v_env_5002_);
    lean_ctor_set(v___x_5007_, 1, v_mctx_5004_);
    lean_ctor_set(v___x_5007_, 2, v_lctx_5005_);
    lean_ctor_set(v___x_5007_, 3, v_options_5006_);
    v___x_5008_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_5008_, 0, v___x_5007_);
    lean_ctor_set(v___x_5008_, 1, v_msgData_4995_);
    v___x_5009_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5009_, 0, v___x_5008_);
    return v___x_5009_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7___boxed(
    mut v_msgData_5010_: *mut LeanObject,
    mut v___y_5011_: *mut LeanObject,
    mut v___y_5012_: *mut LeanObject,
    mut v___y_5013_: *mut LeanObject,
    mut v___y_5014_: *mut LeanObject,
    mut v___y_5015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5016_: *mut LeanObject = core::ptr::null_mut();
    v_res_5016_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msgData_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
    lean_dec(v___y_5014_);
    lean_dec_ref(v___y_5013_);
    lean_dec(v___y_5012_);
    lean_dec_ref(v___y_5011_);
    return v_res_5016_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(
    mut v_msg_5017_: *mut LeanObject,
    mut v___y_5018_: *mut LeanObject,
    mut v___y_5019_: *mut LeanObject,
    mut v___y_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5028_: u8 = 0;
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5023_ = lean_ctor_get(v___y_5020_, 5);
                v___x_5024_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
                v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
                v_isSharedCheck_5033_ = (!lean_is_exclusive(v___x_5024_)) as u8;
                if v_isSharedCheck_5033_ == 0 {
                    v___x_5027_ = v___x_5024_;
                    v_isShared_5028_ = v_isSharedCheck_5033_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5025_);
                    lean_dec(v___x_5024_);
                    v___x_5027_ = lean_box(0);
                    v_isShared_5028_ = v_isSharedCheck_5033_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5023_);
                v___x_5029_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5029_, 0, v_ref_5023_);
                lean_ctor_set(v___x_5029_, 1, v_a_5025_);
                if v_isShared_5028_ == 0 {
                    lean_ctor_set_tag(v___x_5027_, 1);
                    lean_ctor_set(v___x_5027_, 0, v___x_5029_);
                    v___x_5031_ = v___x_5027_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5029_);
                    v___x_5031_ = v_reuseFailAlloc_5032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg___boxed(
    mut v_msg_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
    mut v___y_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5040_: *mut LeanObject = core::ptr::null_mut();
    v_res_5040_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v_msg_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
    lean_dec(v___y_5038_);
    lean_dec_ref(v___y_5037_);
    lean_dec(v___y_5036_);
    lean_dec_ref(v___y_5035_);
    return v_res_5040_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    v___x_5042_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0;
    v___x_5043_ = l_Lean_stringToMessageData(v___x_5042_);
    return v___x_5043_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(
    mut v_preDefs_5044_: *mut LeanObject,
    mut v_fixedParamPerms_5045_: *mut LeanObject,
    mut v_fixedArgs_5046_: *mut LeanObject,
    mut v_F_5047_: *mut LeanObject,
    mut v_k_5048_: *mut LeanObject,
    mut v_a_5049_: *mut LeanObject,
    mut v_a_5050_: *mut LeanObject,
    mut v_a_5051_: *mut LeanObject,
    mut v_a_5052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: u8 = 0;
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5075_: u8 = 0;
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5054_ = l_Lean_instInhabitedExpr;
                v___x_5067_ = l_Lean_Expr_isLambda(v_F_5047_);
                if v___x_5067_ == 0 {
                    lean_dec_ref(v_k_5048_);
                    lean_dec_ref(v_fixedArgs_5046_);
                    lean_dec_ref(v_fixedParamPerms_5045_);
                    lean_dec_ref(v_preDefs_5044_);
                    v___x_5068_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1);
                    v___x_5069_ = l_Lean_indentExpr(v_F_5047_);
                    v___x_5070_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5070_, 0, v___x_5068_);
                    lean_ctor_set(v___x_5070_, 1, v___x_5069_);
                    v___x_5071_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_5070_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_);
                    v_a_5072_ = lean_ctor_get(v___x_5071_, 0);
                    v_isSharedCheck_5079_ = (!lean_is_exclusive(v___x_5071_)) as u8;
                    if v_isSharedCheck_5079_ == 0 {
                        v___x_5074_ = v___x_5071_;
                        v_isShared_5075_ = v_isSharedCheck_5079_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5072_);
                        lean_dec(v___x_5071_);
                        v___x_5074_ = lean_box(0);
                        v_isShared_5075_ = v_isSharedCheck_5079_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_5056_ = v_a_5049_;
                    v___y_5057_ = v_a_5050_;
                    v___y_5058_ = v_a_5051_;
                    v___y_5059_ = v_a_5052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5060_ = lean_st_ref_get(v___y_5059_);
                v_env_5061_ = lean_ctor_get(v___x_5060_, 0);
                lean_inc_ref(v_env_5061_);
                lean_dec(v___x_5060_);
                v___x_5062_ = lean_unsigned_to_nat(0);
                v___x_5063_ = lean_array_get_size(v_preDefs_5044_);
                v___f_5064_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2___boxed as *mut core::ffi::c_void, 13, 8);
                lean_closure_set(v___f_5064_, 0, v___x_5063_);
                lean_closure_set(v___f_5064_, 1, v_fixedParamPerms_5045_);
                lean_closure_set(v___f_5064_, 2, v_fixedArgs_5046_);
                lean_closure_set(v___f_5064_, 3, v_preDefs_5044_);
                lean_closure_set(v___f_5064_, 4, v___x_5062_);
                lean_closure_set(v___f_5064_, 5, v___x_5054_);
                lean_closure_set(v___f_5064_, 6, v_F_5047_);
                lean_closure_set(v___f_5064_, 7, v_k_5048_);
                v___x_5065_ = l_Lean_Environment_unlockAsync(v_env_5061_);
                v___x_5066_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v___x_5065_, v___f_5064_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_);
                return v___x_5066_;
            }
            2 => {
                if v_isShared_5075_ == 0 {
                    v___x_5077_ = v___x_5074_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
                    v___x_5077_ = v_reuseFailAlloc_5078_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___boxed(
    mut v_preDefs_5080_: *mut LeanObject,
    mut v_fixedParamPerms_5081_: *mut LeanObject,
    mut v_fixedArgs_5082_: *mut LeanObject,
    mut v_F_5083_: *mut LeanObject,
    mut v_k_5084_: *mut LeanObject,
    mut v_a_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
    mut v_a_5088_: *mut LeanObject,
    mut v_a_5089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5090_: *mut LeanObject = core::ptr::null_mut();
    v_res_5090_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_5080_, v_fixedParamPerms_5081_, v_fixedArgs_5082_, v_F_5083_, v_k_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_);
    lean_dec(v_a_5088_);
    lean_dec_ref(v_a_5087_);
    lean_dec(v_a_5086_);
    lean_dec_ref(v_a_5085_);
    return v_res_5090_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(
    mut v_00_u03b1_5091_: *mut LeanObject,
    mut v_preDefs_5092_: *mut LeanObject,
    mut v_fixedParamPerms_5093_: *mut LeanObject,
    mut v_fixedArgs_5094_: *mut LeanObject,
    mut v_F_5095_: *mut LeanObject,
    mut v_k_5096_: *mut LeanObject,
    mut v_a_5097_: *mut LeanObject,
    mut v_a_5098_: *mut LeanObject,
    mut v_a_5099_: *mut LeanObject,
    mut v_a_5100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    v___x_5102_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_5092_, v_fixedParamPerms_5093_, v_fixedArgs_5094_, v_F_5095_, v_k_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_);
    return v___x_5102_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___boxed(
    mut v_00_u03b1_5103_: *mut LeanObject,
    mut v_preDefs_5104_: *mut LeanObject,
    mut v_fixedParamPerms_5105_: *mut LeanObject,
    mut v_fixedArgs_5106_: *mut LeanObject,
    mut v_F_5107_: *mut LeanObject,
    mut v_k_5108_: *mut LeanObject,
    mut v_a_5109_: *mut LeanObject,
    mut v_a_5110_: *mut LeanObject,
    mut v_a_5111_: *mut LeanObject,
    mut v_a_5112_: *mut LeanObject,
    mut v_a_5113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5114_: *mut LeanObject = core::ptr::null_mut();
    v_res_5114_ =
        l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(
            v_00_u03b1_5103_,
            v_preDefs_5104_,
            v_fixedParamPerms_5105_,
            v_fixedArgs_5106_,
            v_F_5107_,
            v_k_5108_,
            v_a_5109_,
            v_a_5110_,
            v_a_5111_,
            v_a_5112_,
        );
    lean_dec(v_a_5112_);
    lean_dec_ref(v_a_5111_);
    lean_dec(v_a_5110_);
    lean_dec_ref(v_a_5109_);
    return v_res_5114_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(
    mut v_fixedParamPerms_5115_: *mut LeanObject,
    mut v_fixedArgs_5116_: *mut LeanObject,
    mut v_as_5117_: *mut LeanObject,
    mut v_i_5118_: *mut LeanObject,
    mut v_j_5119_: *mut LeanObject,
    mut v_inv_5120_: *mut LeanObject,
    mut v_bs_5121_: *mut LeanObject,
    mut v___y_5122_: *mut LeanObject,
    mut v___y_5123_: *mut LeanObject,
    mut v___y_5124_: *mut LeanObject,
    mut v___y_5125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    v___x_5127_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_5115_, v_fixedArgs_5116_, v_as_5117_, v_i_5118_, v_j_5119_, v_bs_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
    return v___x_5127_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___boxed(
    mut v_fixedParamPerms_5128_: *mut LeanObject,
    mut v_fixedArgs_5129_: *mut LeanObject,
    mut v_as_5130_: *mut LeanObject,
    mut v_i_5131_: *mut LeanObject,
    mut v_j_5132_: *mut LeanObject,
    mut v_inv_5133_: *mut LeanObject,
    mut v_bs_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
    mut v___y_5136_: *mut LeanObject,
    mut v___y_5137_: *mut LeanObject,
    mut v___y_5138_: *mut LeanObject,
    mut v___y_5139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5140_: *mut LeanObject = core::ptr::null_mut();
    v_res_5140_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(v_fixedParamPerms_5128_, v_fixedArgs_5129_, v_as_5130_, v_i_5131_, v_j_5132_, v_inv_5133_, v_bs_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
    lean_dec(v___y_5138_);
    lean_dec_ref(v___y_5137_);
    lean_dec(v___y_5136_);
    lean_dec_ref(v___y_5135_);
    lean_dec_ref(v_as_5130_);
    lean_dec_ref(v_fixedParamPerms_5128_);
    return v_res_5140_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4(
    mut v_as_5141_: *mut LeanObject,
    mut v_i_5142_: usize,
    mut v_stop_5143_: usize,
    mut v_b_5144_: *mut LeanObject,
    mut v___y_5145_: *mut LeanObject,
    mut v___y_5146_: *mut LeanObject,
    mut v___y_5147_: *mut LeanObject,
    mut v___y_5148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    v___x_5150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_as_5141_, v_i_5142_, v_stop_5143_, v_b_5144_, v___y_5147_, v___y_5148_);
    return v___x_5150_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___boxed(
    mut v_as_5151_: *mut LeanObject,
    mut v_i_5152_: *mut LeanObject,
    mut v_stop_5153_: *mut LeanObject,
    mut v_b_5154_: *mut LeanObject,
    mut v___y_5155_: *mut LeanObject,
    mut v___y_5156_: *mut LeanObject,
    mut v___y_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5160_: usize = 0;
    let mut v_stop_boxed_5161_: usize = 0;
    let mut v_res_5162_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5160_ = lean_unbox_usize(v_i_5152_);
    lean_dec(v_i_5152_);
    v_stop_boxed_5161_ = lean_unbox_usize(v_stop_5153_);
    lean_dec(v_stop_5153_);
    v_res_5162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4(v_as_5151_, v_i_boxed_5160_, v_stop_boxed_5161_, v_b_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
    lean_dec(v___y_5158_);
    lean_dec_ref(v___y_5157_);
    lean_dec(v___y_5156_);
    lean_dec_ref(v___y_5155_);
    lean_dec_ref(v_as_5151_);
    return v_res_5162_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5(
    mut v_env_5163_: *mut LeanObject,
    mut v___y_5164_: *mut LeanObject,
    mut v___y_5165_: *mut LeanObject,
    mut v___y_5166_: *mut LeanObject,
    mut v___y_5167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    v___x_5169_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_5163_, v___y_5165_, v___y_5167_);
    return v___x_5169_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___boxed(
    mut v_env_5170_: *mut LeanObject,
    mut v___y_5171_: *mut LeanObject,
    mut v___y_5172_: *mut LeanObject,
    mut v___y_5173_: *mut LeanObject,
    mut v___y_5174_: *mut LeanObject,
    mut v___y_5175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5176_: *mut LeanObject = core::ptr::null_mut();
    v_res_5176_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5(v_env_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_);
    lean_dec(v___y_5174_);
    lean_dec_ref(v___y_5173_);
    lean_dec(v___y_5172_);
    lean_dec_ref(v___y_5171_);
    return v_res_5176_;
}
pub unsafe fn l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5(
    mut v_00_u03b1_5177_: *mut LeanObject,
    mut v_env_5178_: *mut LeanObject,
    mut v_x_5179_: *mut LeanObject,
    mut v___y_5180_: *mut LeanObject,
    mut v___y_5181_: *mut LeanObject,
    mut v___y_5182_: *mut LeanObject,
    mut v___y_5183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    v___x_5185_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v_env_5178_, v_x_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
    return v___x_5185_;
}
pub unsafe fn l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___boxed(
    mut v_00_u03b1_5186_: *mut LeanObject,
    mut v_env_5187_: *mut LeanObject,
    mut v_x_5188_: *mut LeanObject,
    mut v___y_5189_: *mut LeanObject,
    mut v___y_5190_: *mut LeanObject,
    mut v___y_5191_: *mut LeanObject,
    mut v___y_5192_: *mut LeanObject,
    mut v___y_5193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5194_: *mut LeanObject = core::ptr::null_mut();
    v_res_5194_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5(v_00_u03b1_5186_, v_env_5187_, v_x_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_);
    lean_dec(v___y_5192_);
    lean_dec_ref(v___y_5191_);
    lean_dec(v___y_5190_);
    lean_dec_ref(v___y_5189_);
    return v_res_5194_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6(
    mut v_00_u03b1_5195_: *mut LeanObject,
    mut v_msg_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
    mut v___y_5198_: *mut LeanObject,
    mut v___y_5199_: *mut LeanObject,
    mut v___y_5200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    v___x_5202_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v_msg_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
    return v___x_5202_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___boxed(
    mut v_00_u03b1_5203_: *mut LeanObject,
    mut v_msg_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
    mut v___y_5209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5210_: *mut LeanObject = core::ptr::null_mut();
    v_res_5210_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6(v_00_u03b1_5203_, v_msg_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
    lean_dec(v___y_5208_);
    lean_dec_ref(v___y_5207_);
    lean_dec(v___y_5206_);
    lean_dec_ref(v___y_5205_);
    return v_res_5210_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1()
-> *mut LeanObject {
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    v___x_5212_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0;
    v___x_5213_ = l_Lean_stringToMessageData(v___x_5212_);
    return v___x_5213_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9()
-> *mut LeanObject {
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    v___x_5228_ = lean_box(0);
    v___x_5229_ = lean_unsigned_to_nat(10);
    v___x_5230_ = lean_mk_empty_array_with_capacity(v___x_5229_);
    v___x_5231_ = lean_array_push(v___x_5230_, v___x_5228_);
    return v___x_5231_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10()
-> *mut LeanObject {
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    v___x_5232_ = lean_box(0);
    v___x_5233_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9);
    v___x_5234_ = lean_array_push(v___x_5233_, v___x_5232_);
    return v___x_5234_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11()
-> *mut LeanObject {
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    v___x_5235_ = lean_box(0);
    v___x_5236_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10);
    v___x_5237_ = lean_array_push(v___x_5236_, v___x_5235_);
    return v___x_5237_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd(
    mut v_x_5238_: *mut LeanObject,
    mut v_x_5239_: *mut LeanObject,
    mut v_a_5240_: *mut LeanObject,
    mut v_a_5241_: *mut LeanObject,
    mut v_a_5242_: *mut LeanObject,
    mut v_a_5243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v___y_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5265_: u8 = 0;
    let mut v___y_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: u8 = 0;
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: u8 = 0;
    let mut v_arg_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: u8 = 0;
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: u8 = 0;
    let mut v_arg_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: u8 = 0;
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: u8 = 0;
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: u8 = 0;
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: u8 = 0;
    let mut v_arg_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: u8 = 0;
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: u8 = 0;
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: u8 = 0;
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: u8 = 0;
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5324_: u8 = 0;
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5331_: u8 = 0;
    let mut v_a_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5335_: u8 = 0;
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5339_: u8 = 0;
    let mut v_a_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5343_: u8 = 0;
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v_isSharedCheck_5348_: u8 = 0;
    let mut v_isSharedCheck_5349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5245_ = lean_ctor_get(v_x_5238_, 0);
                v_snd_5246_ = lean_ctor_get(v_x_5238_, 1);
                v_isSharedCheck_5349_ = (!lean_is_exclusive(v_x_5238_)) as u8;
                if v_isSharedCheck_5349_ == 0 {
                    v___x_5248_ = v_x_5238_;
                    v_isShared_5249_ = v_isSharedCheck_5349_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_5246_);
                    lean_inc(v_fst_5245_);
                    lean_dec(v_x_5238_);
                    v___x_5248_ = lean_box(0);
                    v_isShared_5249_ = v_isSharedCheck_5349_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_5261_ = lean_ctor_get(v_x_5239_, 0);
                v_snd_5262_ = lean_ctor_get(v_x_5239_, 1);
                v_isSharedCheck_5348_ = (!lean_is_exclusive(v_x_5239_)) as u8;
                if v_isSharedCheck_5348_ == 0 {
                    v___x_5264_ = v_x_5239_;
                    v_isShared_5265_ = v_isSharedCheck_5348_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_5262_);
                    lean_inc(v_fst_5261_);
                    lean_dec(v_x_5239_);
                    v___x_5264_ = lean_box(0);
                    v_isShared_5265_ = v_isSharedCheck_5348_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_5255_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1);
                v___x_5256_ = l_Lean_indentExpr(v_snd_5246_);
                if v_isShared_5249_ == 0 {
                    lean_ctor_set_tag(v___x_5248_, 7);
                    lean_ctor_set(v___x_5248_, 1, v___x_5256_);
                    lean_ctor_set(v___x_5248_, 0, v___x_5255_);
                    v___x_5258_ = v___x_5248_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5260_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5255_);
                    lean_ctor_set(v_reuseFailAlloc_5260_, 1, v___x_5256_);
                    v___x_5258_ = v_reuseFailAlloc_5260_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5259_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_5258_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
                return v___x_5259_;
            }
            4 => {
                v___x_5275_ = l_Lean_Expr_cleanupAnnotations(v_fst_5245_);
                v___x_5276_ = l_Lean_Expr_isApp(v___x_5275_);
                if v___x_5276_ == 0 {
                    lean_dec_ref(v___x_5275_);
                    lean_del_object(v___x_5264_);
                    lean_dec(v_snd_5262_);
                    lean_dec(v_fst_5261_);
                    v___y_5251_ = v_a_5240_;
                    v___y_5252_ = v_a_5241_;
                    v___y_5253_ = v_a_5242_;
                    v___y_5254_ = v_a_5243_;
                    state = 2;
                    continue;
                } else {
                    v___x_5277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5275_);
                    v___x_5278_ = l_Lean_Expr_isApp(v___x_5277_);
                    if v___x_5278_ == 0 {
                        lean_dec_ref(v___x_5277_);
                        lean_del_object(v___x_5264_);
                        lean_dec(v_snd_5262_);
                        lean_dec(v_fst_5261_);
                        v___y_5251_ = v_a_5240_;
                        v___y_5252_ = v_a_5241_;
                        v___y_5253_ = v_a_5242_;
                        v___y_5254_ = v_a_5243_;
                        state = 2;
                        continue;
                    } else {
                        v_arg_5279_ = lean_ctor_get(v___x_5277_, 1);
                        lean_inc_ref(v_arg_5279_);
                        v___x_5280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5277_);
                        v___x_5281_ = l_Lean_Expr_isApp(v___x_5280_);
                        if v___x_5281_ == 0 {
                            lean_dec_ref(v___x_5280_);
                            lean_dec_ref(v_arg_5279_);
                            lean_del_object(v___x_5264_);
                            lean_dec(v_snd_5262_);
                            lean_dec(v_fst_5261_);
                            v___y_5251_ = v_a_5240_;
                            v___y_5252_ = v_a_5241_;
                            v___y_5253_ = v_a_5242_;
                            v___y_5254_ = v_a_5243_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5282_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5280_);
                            v___x_5283_ = l_Lean_Expr_isApp(v___x_5282_);
                            if v___x_5283_ == 0 {
                                lean_dec_ref(v___x_5282_);
                                lean_dec_ref(v_arg_5279_);
                                lean_del_object(v___x_5264_);
                                lean_dec(v_snd_5262_);
                                lean_dec(v_fst_5261_);
                                v___y_5251_ = v_a_5240_;
                                v___y_5252_ = v_a_5241_;
                                v___y_5253_ = v_a_5242_;
                                v___y_5254_ = v_a_5243_;
                                state = 2;
                                continue;
                            } else {
                                v_arg_5284_ = lean_ctor_get(v___x_5282_, 1);
                                lean_inc_ref(v_arg_5284_);
                                v___x_5285_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5282_);
                                v___x_5286_ = l_Lean_Expr_isApp(v___x_5285_);
                                if v___x_5286_ == 0 {
                                    lean_dec_ref(v___x_5285_);
                                    lean_dec_ref(v_arg_5284_);
                                    lean_dec_ref(v_arg_5279_);
                                    lean_del_object(v___x_5264_);
                                    lean_dec(v_snd_5262_);
                                    lean_dec(v_fst_5261_);
                                    v___y_5251_ = v_a_5240_;
                                    v___y_5252_ = v_a_5241_;
                                    v___y_5253_ = v_a_5242_;
                                    v___y_5254_ = v_a_5243_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_5287_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5285_);
                                    v___x_5288_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5;
                                    v___x_5289_ = l_Lean_Expr_isConstOf(v___x_5287_, v___x_5288_);
                                    lean_dec_ref(v___x_5287_);
                                    if v___x_5289_ == 0 {
                                        lean_dec_ref(v_arg_5284_);
                                        lean_dec_ref(v_arg_5279_);
                                        lean_del_object(v___x_5264_);
                                        lean_dec(v_snd_5262_);
                                        lean_dec(v_fst_5261_);
                                        v___y_5251_ = v_a_5240_;
                                        v___y_5252_ = v_a_5241_;
                                        v___y_5253_ = v_a_5242_;
                                        v___y_5254_ = v_a_5243_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_del_object(v___x_5248_);
                                        v___x_5290_ = l_Lean_Expr_cleanupAnnotations(v_fst_5261_);
                                        v___x_5291_ = l_Lean_Expr_isApp(v___x_5290_);
                                        if v___x_5291_ == 0 {
                                            lean_dec_ref(v___x_5290_);
                                            lean_dec_ref(v_arg_5284_);
                                            lean_dec_ref(v_arg_5279_);
                                            lean_del_object(v___x_5264_);
                                            lean_dec(v_snd_5246_);
                                            v___y_5267_ = v_a_5240_;
                                            v___y_5268_ = v_a_5241_;
                                            v___y_5269_ = v_a_5242_;
                                            v___y_5270_ = v_a_5243_;
                                            state = 5;
                                            continue;
                                        } else {
                                            v___x_5292_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_5290_);
                                            v___x_5293_ = l_Lean_Expr_isApp(v___x_5292_);
                                            if v___x_5293_ == 0 {
                                                lean_dec_ref(v___x_5292_);
                                                lean_dec_ref(v_arg_5284_);
                                                lean_dec_ref(v_arg_5279_);
                                                lean_del_object(v___x_5264_);
                                                lean_dec(v_snd_5246_);
                                                v___y_5267_ = v_a_5240_;
                                                v___y_5268_ = v_a_5241_;
                                                v___y_5269_ = v_a_5242_;
                                                v___y_5270_ = v_a_5243_;
                                                state = 5;
                                                continue;
                                            } else {
                                                v_arg_5294_ = lean_ctor_get(v___x_5292_, 1);
                                                lean_inc_ref(v_arg_5294_);
                                                v___x_5295_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_5292_);
                                                v___x_5296_ = l_Lean_Expr_isApp(v___x_5295_);
                                                if v___x_5296_ == 0 {
                                                    lean_dec_ref(v___x_5295_);
                                                    lean_dec_ref(v_arg_5294_);
                                                    lean_dec_ref(v_arg_5284_);
                                                    lean_dec_ref(v_arg_5279_);
                                                    lean_del_object(v___x_5264_);
                                                    lean_dec(v_snd_5246_);
                                                    v___y_5267_ = v_a_5240_;
                                                    v___y_5268_ = v_a_5241_;
                                                    v___y_5269_ = v_a_5242_;
                                                    v___y_5270_ = v_a_5243_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    v___x_5297_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_5295_,
                                                    );
                                                    v___x_5298_ = l_Lean_Expr_isApp(v___x_5297_);
                                                    if v___x_5298_ == 0 {
                                                        lean_dec_ref(v___x_5297_);
                                                        lean_dec_ref(v_arg_5294_);
                                                        lean_dec_ref(v_arg_5284_);
                                                        lean_dec_ref(v_arg_5279_);
                                                        lean_del_object(v___x_5264_);
                                                        lean_dec(v_snd_5246_);
                                                        v___y_5267_ = v_a_5240_;
                                                        v___y_5268_ = v_a_5241_;
                                                        v___y_5269_ = v_a_5242_;
                                                        v___y_5270_ = v_a_5243_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        v___x_5299_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_5297_,
                                                            );
                                                        v___x_5300_ =
                                                            l_Lean_Expr_isApp(v___x_5299_);
                                                        if v___x_5300_ == 0 {
                                                            lean_dec_ref(v___x_5299_);
                                                            lean_dec_ref(v_arg_5294_);
                                                            lean_dec_ref(v_arg_5284_);
                                                            lean_dec_ref(v_arg_5279_);
                                                            lean_del_object(v___x_5264_);
                                                            lean_dec(v_snd_5246_);
                                                            v___y_5267_ = v_a_5240_;
                                                            v___y_5268_ = v_a_5241_;
                                                            v___y_5269_ = v_a_5242_;
                                                            v___y_5270_ = v_a_5243_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            v___x_5301_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_5299_,
                                                                );
                                                            v___x_5302_ = l_Lean_Expr_isConstOf(
                                                                v___x_5301_,
                                                                v___x_5288_,
                                                            );
                                                            lean_dec_ref(v___x_5301_);
                                                            if v___x_5302_ == 0 {
                                                                lean_dec_ref(v_arg_5294_);
                                                                lean_dec_ref(v_arg_5284_);
                                                                lean_dec_ref(v_arg_5279_);
                                                                lean_del_object(v___x_5264_);
                                                                lean_dec(v_snd_5246_);
                                                                v___y_5267_ = v_a_5240_;
                                                                v___y_5268_ = v_a_5241_;
                                                                v___y_5269_ = v_a_5242_;
                                                                v___y_5270_ = v_a_5243_;
                                                                state = 5;
                                                                continue;
                                                            } else {
                                                                v___x_5303_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8;
                                                                v___x_5304_ = lean_box(0);
                                                                v___x_5305_ = lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_5305_,
                                                                    0,
                                                                    v_arg_5279_,
                                                                );
                                                                v___x_5306_ = lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_5306_,
                                                                    0,
                                                                    v_arg_5294_,
                                                                );
                                                                v___x_5307_ = lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_5307_,
                                                                    0,
                                                                    v_arg_5284_,
                                                                );
                                                                v___x_5308_ = lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_5308_,
                                                                    0,
                                                                    v_snd_5246_,
                                                                );
                                                                v___x_5309_ = lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_5309_,
                                                                    0,
                                                                    v_snd_5262_,
                                                                );
                                                                v___x_5310_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11);
                                                                v___x_5311_ = lean_array_push(
                                                                    v___x_5310_,
                                                                    v___x_5305_,
                                                                );
                                                                v___x_5312_ = lean_array_push(
                                                                    v___x_5311_,
                                                                    v___x_5306_,
                                                                );
                                                                v___x_5313_ = lean_array_push(
                                                                    v___x_5312_,
                                                                    v___x_5307_,
                                                                );
                                                                v___x_5314_ = lean_array_push(
                                                                    v___x_5313_,
                                                                    v___x_5304_,
                                                                );
                                                                v___x_5315_ = lean_array_push(
                                                                    v___x_5314_,
                                                                    v___x_5304_,
                                                                );
                                                                v___x_5316_ = lean_array_push(
                                                                    v___x_5315_,
                                                                    v___x_5308_,
                                                                );
                                                                v___x_5317_ = lean_array_push(
                                                                    v___x_5316_,
                                                                    v___x_5309_,
                                                                );
                                                                v___x_5318_ = l_Lean_Meta_mkAppOptM(
                                                                    v___x_5303_,
                                                                    v___x_5317_,
                                                                    v_a_5240_,
                                                                    v_a_5241_,
                                                                    v_a_5242_,
                                                                    v_a_5243_,
                                                                );
                                                                if lean_obj_tag(v___x_5318_) == 0 {
                                                                    v_a_5319_ = lean_ctor_get(
                                                                        v___x_5318_,
                                                                        0,
                                                                    );
                                                                    lean_inc_n(v_a_5319_, 2);
                                                                    lean_dec_ref_known(
                                                                        v___x_5318_,
                                                                        1,
                                                                    );
                                                                    lean_inc(v_a_5243_);
                                                                    lean_inc_ref(v_a_5242_);
                                                                    lean_inc(v_a_5241_);
                                                                    lean_inc_ref(v_a_5240_);
                                                                    v___x_5320_ = lean_infer_type(
                                                                        v_a_5319_, v_a_5240_,
                                                                        v_a_5241_, v_a_5242_,
                                                                        v_a_5243_,
                                                                    );
                                                                    if lean_obj_tag(v___x_5320_)
                                                                        == 0
                                                                    {
                                                                        v_a_5321_ = lean_ctor_get(
                                                                            v___x_5320_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_5331_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_5320_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_5331_
                                                                            == 0
                                                                        {
                                                                            v___x_5323_ =
                                                                                v___x_5320_;
                                                                            v_isShared_5324_ = v_isSharedCheck_5331_;
                                                                            state = 6;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_5321_);
                                                                            lean_dec(v___x_5320_);
                                                                            v___x_5323_ =
                                                                                lean_box(0);
                                                                            v_isShared_5324_ = v_isSharedCheck_5331_;
                                                                            state = 6;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec(v_a_5319_);
                                                                        lean_del_object(
                                                                            v___x_5264_,
                                                                        );
                                                                        v_a_5332_ = lean_ctor_get(
                                                                            v___x_5320_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_5339_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_5320_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_5339_
                                                                            == 0
                                                                        {
                                                                            v___x_5334_ =
                                                                                v___x_5320_;
                                                                            v_isShared_5335_ = v_isSharedCheck_5339_;
                                                                            state = 9;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_5332_);
                                                                            lean_dec(v___x_5320_);
                                                                            v___x_5334_ =
                                                                                lean_box(0);
                                                                            v_isShared_5335_ = v_isSharedCheck_5339_;
                                                                            state = 9;
                                                                            continue;
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_del_object(v___x_5264_);
                                                                    v_a_5340_ = lean_ctor_get(
                                                                        v___x_5318_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_5347_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_5318_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_5347_ == 0 {
                                                                        v___x_5342_ = v___x_5318_;
                                                                        v_isShared_5343_ =
                                                                            v_isSharedCheck_5347_;
                                                                        state = 11;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_5340_);
                                                                        lean_dec(v___x_5318_);
                                                                        v___x_5342_ = lean_box(0);
                                                                        v_isShared_5343_ =
                                                                            v_isSharedCheck_5347_;
                                                                        state = 11;
                                                                        continue;
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
                        }
                    }
                }
            }
            5 => {
                v___x_5271_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1);
                v___x_5272_ = l_Lean_indentExpr(v_snd_5262_);
                v___x_5273_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5273_, 0, v___x_5271_);
                lean_ctor_set(v___x_5273_, 1, v___x_5272_);
                v___x_5274_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_5273_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
                return v___x_5274_;
            }
            6 => {
                if v_isShared_5265_ == 0 {
                    lean_ctor_set(v___x_5264_, 1, v_a_5319_);
                    lean_ctor_set(v___x_5264_, 0, v_a_5321_);
                    v___x_5326_ = v___x_5264_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5330_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5321_);
                    lean_ctor_set(v_reuseFailAlloc_5330_, 1, v_a_5319_);
                    v___x_5326_ = v_reuseFailAlloc_5330_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5324_ == 0 {
                    lean_ctor_set(v___x_5323_, 0, v___x_5326_);
                    v___x_5328_ = v___x_5323_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5329_, 0, v___x_5326_);
                    v___x_5328_ = v_reuseFailAlloc_5329_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5328_;
            }
            9 => {
                if v_isShared_5335_ == 0 {
                    v___x_5337_ = v___x_5334_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5338_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5332_);
                    v___x_5337_ = v_reuseFailAlloc_5338_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5337_;
            }
            11 => {
                if v_isShared_5343_ == 0 {
                    v___x_5345_ = v___x_5342_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
                    v___x_5345_ = v_reuseFailAlloc_5346_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___boxed(
    mut v_x_5350_: *mut LeanObject,
    mut v_x_5351_: *mut LeanObject,
    mut v_a_5352_: *mut LeanObject,
    mut v_a_5353_: *mut LeanObject,
    mut v_a_5354_: *mut LeanObject,
    mut v_a_5355_: *mut LeanObject,
    mut v_a_5356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5357_: *mut LeanObject = core::ptr::null_mut();
    v_res_5357_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd(
        v_x_5350_, v_x_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_,
    );
    lean_dec(v_a_5355_);
    lean_dec_ref(v_a_5354_);
    lean_dec(v_a_5353_);
    lean_dec_ref(v_a_5352_);
    return v_res_5357_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0(
    mut v_k_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
    mut v___y_5360_: *mut LeanObject,
    mut v_b_5361_: *mut LeanObject,
    mut v_c_5362_: *mut LeanObject,
    mut v___y_5363_: *mut LeanObject,
    mut v___y_5364_: *mut LeanObject,
    mut v___y_5365_: *mut LeanObject,
    mut v___y_5366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5366_);
    lean_inc_ref(v___y_5365_);
    lean_inc(v___y_5364_);
    lean_inc_ref(v___y_5363_);
    lean_inc(v___y_5360_);
    lean_inc_ref(v___y_5359_);
    v___x_5368_ = lean_apply_9(
        v_k_5358_,
        v_b_5361_,
        v_c_5362_,
        v___y_5359_,
        v___y_5360_,
        v___y_5363_,
        v___y_5364_,
        v___y_5365_,
        v___y_5366_,
        lean_box(0),
    );
    return v___x_5368_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed(
    mut v_k_5369_: *mut LeanObject,
    mut v___y_5370_: *mut LeanObject,
    mut v___y_5371_: *mut LeanObject,
    mut v_b_5372_: *mut LeanObject,
    mut v_c_5373_: *mut LeanObject,
    mut v___y_5374_: *mut LeanObject,
    mut v___y_5375_: *mut LeanObject,
    mut v___y_5376_: *mut LeanObject,
    mut v___y_5377_: *mut LeanObject,
    mut v___y_5378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5379_: *mut LeanObject = core::ptr::null_mut();
    v_res_5379_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0(v_k_5369_, v___y_5370_, v___y_5371_, v_b_5372_, v_c_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
    lean_dec(v___y_5377_);
    lean_dec_ref(v___y_5376_);
    lean_dec(v___y_5375_);
    lean_dec_ref(v___y_5374_);
    lean_dec(v___y_5371_);
    lean_dec_ref(v___y_5370_);
    return v_res_5379_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(
    mut v_type_5380_: *mut LeanObject,
    mut v_k_5381_: *mut LeanObject,
    mut v_cleanupAnnotations_5382_: u8,
    mut v_whnfType_5383_: u8,
    mut v___y_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
    mut v___y_5386_: *mut LeanObject,
    mut v___y_5387_: *mut LeanObject,
    mut v___y_5388_: *mut LeanObject,
    mut v___y_5389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5400_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5385_);
                lean_inc_ref(v___y_5384_);
                v___f_5391_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_5391_, 0, v_k_5381_);
                lean_closure_set(v___f_5391_, 1, v___y_5384_);
                lean_closure_set(v___f_5391_, 2, v___y_5385_);
                v___x_5392_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_5380_,
                    v___f_5391_,
                    v_cleanupAnnotations_5382_,
                    v_whnfType_5383_,
                    v___y_5386_,
                    v___y_5387_,
                    v___y_5388_,
                    v___y_5389_,
                );
                if lean_obj_tag(v___x_5392_) == 0 {
                    return v___x_5392_;
                } else {
                    v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
                    v_isSharedCheck_5400_ = (!lean_is_exclusive(v___x_5392_)) as u8;
                    if v_isSharedCheck_5400_ == 0 {
                        v___x_5395_ = v___x_5392_;
                        v_isShared_5396_ = v_isSharedCheck_5400_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5393_);
                        lean_dec(v___x_5392_);
                        v___x_5395_ = lean_box(0);
                        v_isShared_5396_ = v_isSharedCheck_5400_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5396_ == 0 {
                    v___x_5398_ = v___x_5395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
                    v___x_5398_ = v_reuseFailAlloc_5399_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___boxed(
    mut v_type_5401_: *mut LeanObject,
    mut v_k_5402_: *mut LeanObject,
    mut v_cleanupAnnotations_5403_: *mut LeanObject,
    mut v_whnfType_5404_: *mut LeanObject,
    mut v___y_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
    mut v___y_5409_: *mut LeanObject,
    mut v___y_5410_: *mut LeanObject,
    mut v___y_5411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5412_: u8 = 0;
    let mut v_whnfType_boxed_5413_: u8 = 0;
    let mut v_res_5414_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5412_ = (lean_unbox(v_cleanupAnnotations_5403_) as u8);
    v_whnfType_boxed_5413_ = (lean_unbox(v_whnfType_5404_) as u8);
    v_res_5414_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(
            v_type_5401_,
            v_k_5402_,
            v_cleanupAnnotations_boxed_5412_,
            v_whnfType_boxed_5413_,
            v___y_5405_,
            v___y_5406_,
            v___y_5407_,
            v___y_5408_,
            v___y_5409_,
            v___y_5410_,
        );
    lean_dec(v___y_5410_);
    lean_dec_ref(v___y_5409_);
    lean_dec(v___y_5408_);
    lean_dec_ref(v___y_5407_);
    lean_dec(v___y_5406_);
    lean_dec_ref(v___y_5405_);
    return v_res_5414_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3(
    mut v_00_u03b1_5415_: *mut LeanObject,
    mut v_type_5416_: *mut LeanObject,
    mut v_k_5417_: *mut LeanObject,
    mut v_cleanupAnnotations_5418_: u8,
    mut v_whnfType_5419_: u8,
    mut v___y_5420_: *mut LeanObject,
    mut v___y_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
    mut v___y_5423_: *mut LeanObject,
    mut v___y_5424_: *mut LeanObject,
    mut v___y_5425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    v___x_5427_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(
            v_type_5416_,
            v_k_5417_,
            v_cleanupAnnotations_5418_,
            v_whnfType_5419_,
            v___y_5420_,
            v___y_5421_,
            v___y_5422_,
            v___y_5423_,
            v___y_5424_,
            v___y_5425_,
        );
    return v___x_5427_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___boxed(
    mut v_00_u03b1_5428_: *mut LeanObject,
    mut v_type_5429_: *mut LeanObject,
    mut v_k_5430_: *mut LeanObject,
    mut v_cleanupAnnotations_5431_: *mut LeanObject,
    mut v_whnfType_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
    mut v___y_5437_: *mut LeanObject,
    mut v___y_5438_: *mut LeanObject,
    mut v___y_5439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5440_: u8 = 0;
    let mut v_whnfType_boxed_5441_: u8 = 0;
    let mut v_res_5442_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5440_ = (lean_unbox(v_cleanupAnnotations_5431_) as u8);
    v_whnfType_boxed_5441_ = (lean_unbox(v_whnfType_5432_) as u8);
    v_res_5442_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3(
        v_00_u03b1_5428_,
        v_type_5429_,
        v_k_5430_,
        v_cleanupAnnotations_boxed_5440_,
        v_whnfType_boxed_5441_,
        v___y_5433_,
        v___y_5434_,
        v___y_5435_,
        v___y_5436_,
        v___y_5437_,
        v___y_5438_,
    );
    lean_dec(v___y_5438_);
    lean_dec_ref(v___y_5437_);
    lean_dec(v___y_5436_);
    lean_dec_ref(v___y_5435_);
    lean_dec(v___y_5434_);
    lean_dec_ref(v___y_5433_);
    return v_res_5442_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(
    mut v_e_5443_: *mut LeanObject,
    mut v_k_5444_: *mut LeanObject,
    mut v_cleanupAnnotations_5445_: u8,
    mut v___y_5446_: *mut LeanObject,
    mut v___y_5447_: *mut LeanObject,
    mut v___y_5448_: *mut LeanObject,
    mut v___y_5449_: *mut LeanObject,
    mut v___y_5450_: *mut LeanObject,
    mut v___y_5451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: u8 = 0;
    let mut v___x_5455_: u8 = 0;
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5461_: u8 = 0;
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5447_);
                lean_inc_ref(v___y_5446_);
                v___f_5453_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_5453_, 0, v_k_5444_);
                lean_closure_set(v___f_5453_, 1, v___y_5446_);
                lean_closure_set(v___f_5453_, 2, v___y_5447_);
                v___x_5454_ = 1;
                v___x_5455_ = 0;
                v___x_5456_ = lean_box(0);
                v___x_5457_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
                    v_e_5443_,
                    v___x_5454_,
                    v___x_5455_,
                    v___x_5454_,
                    v___x_5455_,
                    v___x_5456_,
                    v___f_5453_,
                    v_cleanupAnnotations_5445_,
                    v___y_5448_,
                    v___y_5449_,
                    v___y_5450_,
                    v___y_5451_,
                );
                if lean_obj_tag(v___x_5457_) == 0 {
                    return v___x_5457_;
                } else {
                    v_a_5458_ = lean_ctor_get(v___x_5457_, 0);
                    v_isSharedCheck_5465_ = (!lean_is_exclusive(v___x_5457_)) as u8;
                    if v_isSharedCheck_5465_ == 0 {
                        v___x_5460_ = v___x_5457_;
                        v_isShared_5461_ = v_isSharedCheck_5465_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5458_);
                        lean_dec(v___x_5457_);
                        v___x_5460_ = lean_box(0);
                        v_isShared_5461_ = v_isSharedCheck_5465_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5461_ == 0 {
                    v___x_5463_ = v___x_5460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5464_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_a_5458_);
                    v___x_5463_ = v_reuseFailAlloc_5464_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg___boxed(
    mut v_e_5466_: *mut LeanObject,
    mut v_k_5467_: *mut LeanObject,
    mut v_cleanupAnnotations_5468_: *mut LeanObject,
    mut v___y_5469_: *mut LeanObject,
    mut v___y_5470_: *mut LeanObject,
    mut v___y_5471_: *mut LeanObject,
    mut v___y_5472_: *mut LeanObject,
    mut v___y_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5476_: u8 = 0;
    let mut v_res_5477_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5476_ = (lean_unbox(v_cleanupAnnotations_5468_) as u8);
    v_res_5477_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(
        v_e_5466_,
        v_k_5467_,
        v_cleanupAnnotations_boxed_5476_,
        v___y_5469_,
        v___y_5470_,
        v___y_5471_,
        v___y_5472_,
        v___y_5473_,
        v___y_5474_,
    );
    lean_dec(v___y_5474_);
    lean_dec_ref(v___y_5473_);
    lean_dec(v___y_5472_);
    lean_dec_ref(v___y_5471_);
    lean_dec(v___y_5470_);
    lean_dec_ref(v___y_5469_);
    return v_res_5477_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5(
    mut v_00_u03b1_5478_: *mut LeanObject,
    mut v_e_5479_: *mut LeanObject,
    mut v_k_5480_: *mut LeanObject,
    mut v_cleanupAnnotations_5481_: u8,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
    mut v___y_5486_: *mut LeanObject,
    mut v___y_5487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    v___x_5489_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(
        v_e_5479_,
        v_k_5480_,
        v_cleanupAnnotations_5481_,
        v___y_5482_,
        v___y_5483_,
        v___y_5484_,
        v___y_5485_,
        v___y_5486_,
        v___y_5487_,
    );
    return v___x_5489_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___boxed(
    mut v_00_u03b1_5490_: *mut LeanObject,
    mut v_e_5491_: *mut LeanObject,
    mut v_k_5492_: *mut LeanObject,
    mut v_cleanupAnnotations_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
    mut v___y_5497_: *mut LeanObject,
    mut v___y_5498_: *mut LeanObject,
    mut v___y_5499_: *mut LeanObject,
    mut v___y_5500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5501_: u8 = 0;
    let mut v_res_5502_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5501_ = (lean_unbox(v_cleanupAnnotations_5493_) as u8);
    v_res_5502_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5(
        v_00_u03b1_5490_,
        v_e_5491_,
        v_k_5492_,
        v_cleanupAnnotations_boxed_5501_,
        v___y_5494_,
        v___y_5495_,
        v___y_5496_,
        v___y_5497_,
        v___y_5498_,
        v___y_5499_,
    );
    lean_dec(v___y_5499_);
    lean_dec_ref(v___y_5498_);
    lean_dec(v___y_5497_);
    lean_dec_ref(v___y_5496_);
    lean_dec(v___y_5495_);
    lean_dec_ref(v___y_5494_);
    return v_res_5502_;
}
pub unsafe fn l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(
    mut v_msg_5503_: *mut LeanObject,
    mut v___y_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_41586__overap_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    v___f_5509_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0;
    v___x_41586__overap_5510_ = lean_panic_fn_borrowed(v___f_5509_, v_msg_5503_);
    lean_inc(v___y_5507_);
    lean_inc_ref(v___y_5506_);
    lean_inc(v___y_5505_);
    lean_inc_ref(v___y_5504_);
    v___x_5511_ = lean_apply_5(
        v___x_41586__overap_5510_,
        v___y_5504_,
        v___y_5505_,
        v___y_5506_,
        v___y_5507_,
        lean_box(0),
    );
    return v___x_5511_;
}
pub unsafe fn l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg___boxed(
    mut v_msg_5512_: *mut LeanObject,
    mut v___y_5513_: *mut LeanObject,
    mut v___y_5514_: *mut LeanObject,
    mut v___y_5515_: *mut LeanObject,
    mut v___y_5516_: *mut LeanObject,
    mut v___y_5517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5518_: *mut LeanObject = core::ptr::null_mut();
    v_res_5518_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(
        v_msg_5512_,
        v___y_5513_,
        v___y_5514_,
        v___y_5515_,
        v___y_5516_,
    );
    lean_dec(v___y_5516_);
    lean_dec_ref(v___y_5515_);
    lean_dec(v___y_5514_);
    lean_dec_ref(v___y_5513_);
    return v_res_5518_;
}
pub unsafe fn l_panic___at___00Lean_Elab_partialFixpoint_spec__8(
    mut v_00_u03b1_5519_: *mut LeanObject,
    mut v_msg_5520_: *mut LeanObject,
    mut v___y_5521_: *mut LeanObject,
    mut v___y_5522_: *mut LeanObject,
    mut v___y_5523_: *mut LeanObject,
    mut v___y_5524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    v___x_5526_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(
        v_msg_5520_,
        v___y_5521_,
        v___y_5522_,
        v___y_5523_,
        v___y_5524_,
    );
    return v___x_5526_;
}
pub unsafe fn l_panic___at___00Lean_Elab_partialFixpoint_spec__8___boxed(
    mut v_00_u03b1_5527_: *mut LeanObject,
    mut v_msg_5528_: *mut LeanObject,
    mut v___y_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
    mut v___y_5533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5534_: *mut LeanObject = core::ptr::null_mut();
    v_res_5534_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8(
        v_00_u03b1_5527_,
        v_msg_5528_,
        v___y_5529_,
        v___y_5530_,
        v___y_5531_,
        v___y_5532_,
    );
    lean_dec(v___y_5532_);
    lean_dec_ref(v___y_5531_);
    lean_dec(v___y_5530_);
    lean_dec_ref(v___y_5529_);
    return v_res_5534_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(
    mut v_e_5535_: *mut LeanObject,
    mut v___y_5536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5552_: u8 = 0;
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5558_: u8 = 0;
    let mut v_unused_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5538_ = l_Lean_Expr_hasMVar(v_e_5535_);
                if v___x_5538_ == 0 {
                    v___x_5539_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5539_, 0, v_e_5535_);
                    return v___x_5539_;
                } else {
                    v___x_5540_ = lean_st_ref_get(v___y_5536_);
                    v_mctx_5541_ = lean_ctor_get(v___x_5540_, 0);
                    lean_inc_ref(v_mctx_5541_);
                    lean_dec(v___x_5540_);
                    v___x_5542_ = l_Lean_instantiateMVarsCore(v_mctx_5541_, v_e_5535_);
                    v_fst_5543_ = lean_ctor_get(v___x_5542_, 0);
                    lean_inc(v_fst_5543_);
                    v_snd_5544_ = lean_ctor_get(v___x_5542_, 1);
                    lean_inc(v_snd_5544_);
                    lean_dec_ref(v___x_5542_);
                    v___x_5545_ = lean_st_ref_take(v___y_5536_);
                    v_cache_5546_ = lean_ctor_get(v___x_5545_, 1);
                    v_zetaDeltaFVarIds_5547_ = lean_ctor_get(v___x_5545_, 2);
                    v_postponed_5548_ = lean_ctor_get(v___x_5545_, 3);
                    v_diag_5549_ = lean_ctor_get(v___x_5545_, 4);
                    v_isSharedCheck_5558_ = (!lean_is_exclusive(v___x_5545_)) as u8;
                    if v_isSharedCheck_5558_ == 0 {
                        v_unused_5559_ = lean_ctor_get(v___x_5545_, 0);
                        lean_dec(v_unused_5559_);
                        v___x_5551_ = v___x_5545_;
                        v_isShared_5552_ = v_isSharedCheck_5558_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_5549_);
                        lean_inc(v_postponed_5548_);
                        lean_inc(v_zetaDeltaFVarIds_5547_);
                        lean_inc(v_cache_5546_);
                        lean_dec(v___x_5545_);
                        v___x_5551_ = lean_box(0);
                        v_isShared_5552_ = v_isSharedCheck_5558_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5552_ == 0 {
                    lean_ctor_set(v___x_5551_, 0, v_snd_5544_);
                    v___x_5554_ = v___x_5551_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_snd_5544_);
                    lean_ctor_set(v_reuseFailAlloc_5557_, 1, v_cache_5546_);
                    lean_ctor_set(v_reuseFailAlloc_5557_, 2, v_zetaDeltaFVarIds_5547_);
                    lean_ctor_set(v_reuseFailAlloc_5557_, 3, v_postponed_5548_);
                    lean_ctor_set(v_reuseFailAlloc_5557_, 4, v_diag_5549_);
                    v___x_5554_ = v_reuseFailAlloc_5557_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5555_ = lean_st_ref_set(v___y_5536_, v___x_5554_);
                v___x_5556_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5556_, 0, v_fst_5543_);
                return v___x_5556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg___boxed(
    mut v_e_5560_: *mut LeanObject,
    mut v___y_5561_: *mut LeanObject,
    mut v___y_5562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5563_: *mut LeanObject = core::ptr::null_mut();
    v_res_5563_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(
        v_e_5560_,
        v___y_5561_,
    );
    lean_dec(v___y_5561_);
    return v_res_5563_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18(
    mut v_e_5564_: *mut LeanObject,
    mut v___y_5565_: *mut LeanObject,
    mut v___y_5566_: *mut LeanObject,
    mut v___y_5567_: *mut LeanObject,
    mut v___y_5568_: *mut LeanObject,
    mut v___y_5569_: *mut LeanObject,
    mut v___y_5570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    v___x_5572_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(
        v_e_5564_,
        v___y_5568_,
    );
    return v___x_5572_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___boxed(
    mut v_e_5573_: *mut LeanObject,
    mut v___y_5574_: *mut LeanObject,
    mut v___y_5575_: *mut LeanObject,
    mut v___y_5576_: *mut LeanObject,
    mut v___y_5577_: *mut LeanObject,
    mut v___y_5578_: *mut LeanObject,
    mut v___y_5579_: *mut LeanObject,
    mut v___y_5580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5581_: *mut LeanObject = core::ptr::null_mut();
    v_res_5581_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18(
        v_e_5573_,
        v___y_5574_,
        v___y_5575_,
        v___y_5576_,
        v___y_5577_,
        v___y_5578_,
        v___y_5579_,
    );
    lean_dec(v___y_5579_);
    lean_dec_ref(v___y_5578_);
    lean_dec(v___y_5577_);
    lean_dec_ref(v___y_5576_);
    lean_dec(v___y_5575_);
    lean_dec_ref(v___y_5574_);
    return v_res_5581_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(
    mut v_type_5582_: *mut LeanObject,
    mut v_maxFVars_x3f_5583_: *mut LeanObject,
    mut v_k_5584_: *mut LeanObject,
    mut v_cleanupAnnotations_5585_: u8,
    mut v_whnfType_5586_: u8,
    mut v___y_5587_: *mut LeanObject,
    mut v___y_5588_: *mut LeanObject,
    mut v___y_5589_: *mut LeanObject,
    mut v___y_5590_: *mut LeanObject,
    mut v___y_5591_: *mut LeanObject,
    mut v___y_5592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5599_: u8 = 0;
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5588_);
                lean_inc_ref(v___y_5587_);
                v___f_5594_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_5594_, 0, v_k_5584_);
                lean_closure_set(v___f_5594_, 1, v___y_5587_);
                lean_closure_set(v___f_5594_, 2, v___y_5588_);
                v___x_5595_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_5582_,
                    v_maxFVars_x3f_5583_,
                    v___f_5594_,
                    v_cleanupAnnotations_5585_,
                    v_whnfType_5586_,
                    v___y_5589_,
                    v___y_5590_,
                    v___y_5591_,
                    v___y_5592_,
                );
                if lean_obj_tag(v___x_5595_) == 0 {
                    return v___x_5595_;
                } else {
                    v_a_5596_ = lean_ctor_get(v___x_5595_, 0);
                    v_isSharedCheck_5603_ = (!lean_is_exclusive(v___x_5595_)) as u8;
                    if v_isSharedCheck_5603_ == 0 {
                        v___x_5598_ = v___x_5595_;
                        v_isShared_5599_ = v_isSharedCheck_5603_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5596_);
                        lean_dec(v___x_5595_);
                        v___x_5598_ = lean_box(0);
                        v_isShared_5599_ = v_isSharedCheck_5603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5599_ == 0 {
                    v___x_5601_ = v___x_5598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5596_);
                    v___x_5601_ = v_reuseFailAlloc_5602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg___boxed(
    mut v_type_5604_: *mut LeanObject,
    mut v_maxFVars_x3f_5605_: *mut LeanObject,
    mut v_k_5606_: *mut LeanObject,
    mut v_cleanupAnnotations_5607_: *mut LeanObject,
    mut v_whnfType_5608_: *mut LeanObject,
    mut v___y_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
    mut v___y_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
    mut v___y_5614_: *mut LeanObject,
    mut v___y_5615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5616_: u8 = 0;
    let mut v_whnfType_boxed_5617_: u8 = 0;
    let mut v_res_5618_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5616_ = (lean_unbox(v_cleanupAnnotations_5607_) as u8);
    v_whnfType_boxed_5617_ = (lean_unbox(v_whnfType_5608_) as u8);
    v_res_5618_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(
            v_type_5604_,
            v_maxFVars_x3f_5605_,
            v_k_5606_,
            v_cleanupAnnotations_boxed_5616_,
            v_whnfType_boxed_5617_,
            v___y_5609_,
            v___y_5610_,
            v___y_5611_,
            v___y_5612_,
            v___y_5613_,
            v___y_5614_,
        );
    lean_dec(v___y_5614_);
    lean_dec_ref(v___y_5613_);
    lean_dec(v___y_5612_);
    lean_dec_ref(v___y_5611_);
    lean_dec(v___y_5610_);
    lean_dec_ref(v___y_5609_);
    return v_res_5618_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20(
    mut v_00_u03b1_5619_: *mut LeanObject,
    mut v_type_5620_: *mut LeanObject,
    mut v_maxFVars_x3f_5621_: *mut LeanObject,
    mut v_k_5622_: *mut LeanObject,
    mut v_cleanupAnnotations_5623_: u8,
    mut v_whnfType_5624_: u8,
    mut v___y_5625_: *mut LeanObject,
    mut v___y_5626_: *mut LeanObject,
    mut v___y_5627_: *mut LeanObject,
    mut v___y_5628_: *mut LeanObject,
    mut v___y_5629_: *mut LeanObject,
    mut v___y_5630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    v___x_5632_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(
            v_type_5620_,
            v_maxFVars_x3f_5621_,
            v_k_5622_,
            v_cleanupAnnotations_5623_,
            v_whnfType_5624_,
            v___y_5625_,
            v___y_5626_,
            v___y_5627_,
            v___y_5628_,
            v___y_5629_,
            v___y_5630_,
        );
    return v___x_5632_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___boxed(
    mut v_00_u03b1_5633_: *mut LeanObject,
    mut v_type_5634_: *mut LeanObject,
    mut v_maxFVars_x3f_5635_: *mut LeanObject,
    mut v_k_5636_: *mut LeanObject,
    mut v_cleanupAnnotations_5637_: *mut LeanObject,
    mut v_whnfType_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
    mut v___y_5640_: *mut LeanObject,
    mut v___y_5641_: *mut LeanObject,
    mut v___y_5642_: *mut LeanObject,
    mut v___y_5643_: *mut LeanObject,
    mut v___y_5644_: *mut LeanObject,
    mut v___y_5645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5646_: u8 = 0;
    let mut v_whnfType_boxed_5647_: u8 = 0;
    let mut v_res_5648_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5646_ = (lean_unbox(v_cleanupAnnotations_5637_) as u8);
    v_whnfType_boxed_5647_ = (lean_unbox(v_whnfType_5638_) as u8);
    v_res_5648_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20(
        v_00_u03b1_5633_,
        v_type_5634_,
        v_maxFVars_x3f_5635_,
        v_k_5636_,
        v_cleanupAnnotations_boxed_5646_,
        v_whnfType_boxed_5647_,
        v___y_5639_,
        v___y_5640_,
        v___y_5641_,
        v___y_5642_,
        v___y_5643_,
        v___y_5644_,
    );
    lean_dec(v___y_5644_);
    lean_dec_ref(v___y_5643_);
    lean_dec(v___y_5642_);
    lean_dec_ref(v___y_5641_);
    lean_dec(v___y_5640_);
    lean_dec_ref(v___y_5639_);
    return v_res_5648_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0(
    mut v_k_5649_: *mut LeanObject,
    mut v___y_5650_: *mut LeanObject,
    mut v___y_5651_: *mut LeanObject,
    mut v_b_5652_: *mut LeanObject,
    mut v___y_5653_: *mut LeanObject,
    mut v___y_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5656_);
    lean_inc_ref(v___y_5655_);
    lean_inc(v___y_5654_);
    lean_inc_ref(v___y_5653_);
    lean_inc(v___y_5651_);
    lean_inc_ref(v___y_5650_);
    v___x_5658_ = lean_apply_8(
        v_k_5649_,
        v_b_5652_,
        v___y_5650_,
        v___y_5651_,
        v___y_5653_,
        v___y_5654_,
        v___y_5655_,
        v___y_5656_,
        lean_box(0),
    );
    return v___x_5658_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0___boxed(
    mut v_k_5659_: *mut LeanObject,
    mut v___y_5660_: *mut LeanObject,
    mut v___y_5661_: *mut LeanObject,
    mut v_b_5662_: *mut LeanObject,
    mut v___y_5663_: *mut LeanObject,
    mut v___y_5664_: *mut LeanObject,
    mut v___y_5665_: *mut LeanObject,
    mut v___y_5666_: *mut LeanObject,
    mut v___y_5667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5668_: *mut LeanObject = core::ptr::null_mut();
    v_res_5668_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0(v_k_5659_, v___y_5660_, v___y_5661_, v_b_5662_, v___y_5663_, v___y_5664_, v___y_5665_, v___y_5666_);
    lean_dec(v___y_5666_);
    lean_dec_ref(v___y_5665_);
    lean_dec(v___y_5664_);
    lean_dec_ref(v___y_5663_);
    lean_dec(v___y_5661_);
    lean_dec_ref(v___y_5660_);
    return v_res_5668_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(
    mut v_perm_5669_: *mut LeanObject,
    mut v_type_5670_: *mut LeanObject,
    mut v_k_5671_: *mut LeanObject,
    mut v___y_5672_: *mut LeanObject,
    mut v___y_5673_: *mut LeanObject,
    mut v___y_5674_: *mut LeanObject,
    mut v___y_5675_: *mut LeanObject,
    mut v___y_5676_: *mut LeanObject,
    mut v___y_5677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5684_: u8 = 0;
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5673_);
                lean_inc_ref(v___y_5672_);
                v___f_5679_ = lean_alloc_closure(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                lean_closure_set(v___f_5679_, 0, v_k_5671_);
                lean_closure_set(v___f_5679_, 1, v___y_5672_);
                lean_closure_set(v___f_5679_, 2, v___y_5673_);
                v___x_5680_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_5669_, v_type_5670_, v___f_5679_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
                if lean_obj_tag(v___x_5680_) == 0 {
                    return v___x_5680_;
                } else {
                    v_a_5681_ = lean_ctor_get(v___x_5680_, 0);
                    v_isSharedCheck_5688_ = (!lean_is_exclusive(v___x_5680_)) as u8;
                    if v_isSharedCheck_5688_ == 0 {
                        v___x_5683_ = v___x_5680_;
                        v_isShared_5684_ = v_isSharedCheck_5688_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5681_);
                        lean_dec(v___x_5680_);
                        v___x_5683_ = lean_box(0);
                        v_isShared_5684_ = v_isSharedCheck_5688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5684_ == 0 {
                    v___x_5686_ = v___x_5683_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
                    v___x_5686_ = v_reuseFailAlloc_5687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___boxed(
    mut v_perm_5689_: *mut LeanObject,
    mut v_type_5690_: *mut LeanObject,
    mut v_k_5691_: *mut LeanObject,
    mut v___y_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
    mut v___y_5695_: *mut LeanObject,
    mut v___y_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5699_: *mut LeanObject = core::ptr::null_mut();
    v_res_5699_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v_perm_5689_, v_type_5690_, v_k_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_);
    lean_dec(v___y_5697_);
    lean_dec_ref(v___y_5696_);
    lean_dec(v___y_5695_);
    lean_dec_ref(v___y_5694_);
    lean_dec(v___y_5693_);
    lean_dec_ref(v___y_5692_);
    return v_res_5699_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24(
    mut v_00_u03b1_5700_: *mut LeanObject,
    mut v_perm_5701_: *mut LeanObject,
    mut v_type_5702_: *mut LeanObject,
    mut v_k_5703_: *mut LeanObject,
    mut v___y_5704_: *mut LeanObject,
    mut v___y_5705_: *mut LeanObject,
    mut v___y_5706_: *mut LeanObject,
    mut v___y_5707_: *mut LeanObject,
    mut v___y_5708_: *mut LeanObject,
    mut v___y_5709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    v___x_5711_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v_perm_5701_, v_type_5702_, v_k_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_);
    return v___x_5711_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___boxed(
    mut v_00_u03b1_5712_: *mut LeanObject,
    mut v_perm_5713_: *mut LeanObject,
    mut v_type_5714_: *mut LeanObject,
    mut v_k_5715_: *mut LeanObject,
    mut v___y_5716_: *mut LeanObject,
    mut v___y_5717_: *mut LeanObject,
    mut v___y_5718_: *mut LeanObject,
    mut v___y_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5723_: *mut LeanObject = core::ptr::null_mut();
    v_res_5723_ =
        l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24(
            v_00_u03b1_5712_,
            v_perm_5713_,
            v_type_5714_,
            v_k_5715_,
            v___y_5716_,
            v___y_5717_,
            v___y_5718_,
            v___y_5719_,
            v___y_5720_,
            v___y_5721_,
        );
    lean_dec(v___y_5721_);
    lean_dec_ref(v___y_5720_);
    lean_dec(v___y_5719_);
    lean_dec_ref(v___y_5718_);
    lean_dec(v___y_5717_);
    lean_dec_ref(v___y_5716_);
    return v_res_5723_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0()
-> *mut LeanObject {
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    v___x_5724_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
    return v___x_5724_;
}
pub unsafe fn l_panic___at___00Lean_Elab_partialFixpoint_spec__25(
    mut v_msg_5725_: *mut LeanObject,
    mut v___y_5726_: *mut LeanObject,
    mut v___y_5727_: *mut LeanObject,
    mut v___y_5728_: *mut LeanObject,
    mut v___y_5729_: *mut LeanObject,
    mut v___y_5730_: *mut LeanObject,
    mut v___y_5731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_47528__overap_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    v___x_5733_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0_once
        ),
        _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0,
    );
    v___x_47528__overap_5734_ = lean_panic_fn_borrowed(v___x_5733_, v_msg_5725_);
    lean_inc(v___y_5731_);
    lean_inc_ref(v___y_5730_);
    lean_inc(v___y_5729_);
    lean_inc_ref(v___y_5728_);
    lean_inc(v___y_5727_);
    lean_inc_ref(v___y_5726_);
    v___x_5735_ = lean_apply_7(
        v___x_47528__overap_5734_,
        v___y_5726_,
        v___y_5727_,
        v___y_5728_,
        v___y_5729_,
        v___y_5730_,
        v___y_5731_,
        lean_box(0),
    );
    return v___x_5735_;
}
pub unsafe fn l_panic___at___00Lean_Elab_partialFixpoint_spec__25___boxed(
    mut v_msg_5736_: *mut LeanObject,
    mut v___y_5737_: *mut LeanObject,
    mut v___y_5738_: *mut LeanObject,
    mut v___y_5739_: *mut LeanObject,
    mut v___y_5740_: *mut LeanObject,
    mut v___y_5741_: *mut LeanObject,
    mut v___y_5742_: *mut LeanObject,
    mut v___y_5743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5744_: *mut LeanObject = core::ptr::null_mut();
    v_res_5744_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(
        v_msg_5736_,
        v___y_5737_,
        v___y_5738_,
        v___y_5739_,
        v___y_5740_,
        v___y_5741_,
        v___y_5742_,
    );
    lean_dec(v___y_5742_);
    lean_dec_ref(v___y_5741_);
    lean_dec(v___y_5740_);
    lean_dec_ref(v___y_5739_);
    lean_dec(v___y_5738_);
    lean_dec_ref(v___y_5737_);
    return v_res_5744_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: f64 = 0.0;
    v___x_5745_ = lean_unsigned_to_nat(0);
    v___x_5746_ = lean_float_of_nat(v___x_5745_);
    return v___x_5746_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(
    mut v_cls_5750_: *mut LeanObject,
    mut v_msg_5751_: *mut LeanObject,
    mut v___y_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5762_: u8 = 0;
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v_tid_5776_: u64 = 0;
    let mut v_traces_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5780_: u8 = 0;
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: f64 = 0.0;
    let mut v___x_5783_: u8 = 0;
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5801_: u8 = 0;
    let mut v_isSharedCheck_5802_: u8 = 0;
    let mut v_isSharedCheck_5803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5757_ = lean_ctor_get(v___y_5754_, 5);
                v___x_5758_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_);
                v_a_5759_ = lean_ctor_get(v___x_5758_, 0);
                v_isSharedCheck_5803_ = (!lean_is_exclusive(v___x_5758_)) as u8;
                if v_isSharedCheck_5803_ == 0 {
                    v___x_5761_ = v___x_5758_;
                    v_isShared_5762_ = v_isSharedCheck_5803_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5759_);
                    lean_dec(v___x_5758_);
                    v___x_5761_ = lean_box(0);
                    v_isShared_5762_ = v_isSharedCheck_5803_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5763_ = lean_st_ref_take(v___y_5755_);
                v_traceState_5764_ = lean_ctor_get(v___x_5763_, 4);
                v_env_5765_ = lean_ctor_get(v___x_5763_, 0);
                v_nextMacroScope_5766_ = lean_ctor_get(v___x_5763_, 1);
                v_ngen_5767_ = lean_ctor_get(v___x_5763_, 2);
                v_auxDeclNGen_5768_ = lean_ctor_get(v___x_5763_, 3);
                v_cache_5769_ = lean_ctor_get(v___x_5763_, 5);
                v_messages_5770_ = lean_ctor_get(v___x_5763_, 6);
                v_infoState_5771_ = lean_ctor_get(v___x_5763_, 7);
                v_snapshotTasks_5772_ = lean_ctor_get(v___x_5763_, 8);
                v_isSharedCheck_5802_ = (!lean_is_exclusive(v___x_5763_)) as u8;
                if v_isSharedCheck_5802_ == 0 {
                    v___x_5774_ = v___x_5763_;
                    v_isShared_5775_ = v_isSharedCheck_5802_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5772_);
                    lean_inc(v_infoState_5771_);
                    lean_inc(v_messages_5770_);
                    lean_inc(v_cache_5769_);
                    lean_inc(v_traceState_5764_);
                    lean_inc(v_auxDeclNGen_5768_);
                    lean_inc(v_ngen_5767_);
                    lean_inc(v_nextMacroScope_5766_);
                    lean_inc(v_env_5765_);
                    lean_dec(v___x_5763_);
                    v___x_5774_ = lean_box(0);
                    v_isShared_5775_ = v_isSharedCheck_5802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5776_ = lean_ctor_get_uint64(
                    v_traceState_5764_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5777_ = lean_ctor_get(v_traceState_5764_, 0);
                v_isSharedCheck_5801_ = (!lean_is_exclusive(v_traceState_5764_)) as u8;
                if v_isSharedCheck_5801_ == 0 {
                    v___x_5779_ = v_traceState_5764_;
                    v_isShared_5780_ = v_isSharedCheck_5801_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_5777_);
                    lean_dec(v_traceState_5764_);
                    v___x_5779_ = lean_box(0);
                    v_isShared_5780_ = v_isSharedCheck_5801_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5781_ = lean_box(0);
                v___x_5782_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0);
                v___x_5783_ = 0;
                v___x_5784_ =
                    l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1;
                v___x_5785_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_5785_, 0, v_cls_5750_);
                lean_ctor_set(v___x_5785_, 1, v___x_5781_);
                lean_ctor_set(v___x_5785_, 2, v___x_5784_);
                lean_ctor_set_float(
                    v___x_5785_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5782_,
                );
                lean_ctor_set_float(
                    v___x_5785_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5782_,
                );
                lean_ctor_set_uint8(
                    v___x_5785_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_5783_,
                );
                v___x_5786_ =
                    l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2;
                v___x_5787_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_5787_, 0, v___x_5785_);
                lean_ctor_set(v___x_5787_, 1, v_a_5759_);
                lean_ctor_set(v___x_5787_, 2, v___x_5786_);
                lean_inc(v_ref_5757_);
                v___x_5788_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5788_, 0, v_ref_5757_);
                lean_ctor_set(v___x_5788_, 1, v___x_5787_);
                v___x_5789_ = l_Lean_PersistentArray_push___redArg(v_traces_5777_, v___x_5788_);
                if v_isShared_5780_ == 0 {
                    lean_ctor_set(v___x_5779_, 0, v___x_5789_);
                    v___x_5791_ = v___x_5779_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5800_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5800_, 0, v___x_5789_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5800_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5776_,
                    );
                    v___x_5791_ = v_reuseFailAlloc_5800_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5775_ == 0 {
                    lean_ctor_set(v___x_5774_, 4, v___x_5791_);
                    v___x_5793_ = v___x_5774_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 0, v_env_5765_);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 1, v_nextMacroScope_5766_);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 2, v_ngen_5767_);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 3, v_auxDeclNGen_5768_);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 4, v___x_5791_);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 5, v_cache_5769_);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 6, v_messages_5770_);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 7, v_infoState_5771_);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 8, v_snapshotTasks_5772_);
                    v___x_5793_ = v_reuseFailAlloc_5799_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5794_ = lean_st_ref_set(v___y_5755_, v___x_5793_);
                v___x_5795_ = lean_box(0);
                if v_isShared_5762_ == 0 {
                    lean_ctor_set(v___x_5761_, 0, v___x_5795_);
                    v___x_5797_ = v___x_5761_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5798_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5798_, 0, v___x_5795_);
                    v___x_5797_ = v_reuseFailAlloc_5798_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___boxed(
    mut v_cls_5804_: *mut LeanObject,
    mut v_msg_5805_: *mut LeanObject,
    mut v___y_5806_: *mut LeanObject,
    mut v___y_5807_: *mut LeanObject,
    mut v___y_5808_: *mut LeanObject,
    mut v___y_5809_: *mut LeanObject,
    mut v___y_5810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5811_: *mut LeanObject = core::ptr::null_mut();
    v_res_5811_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(
        v_cls_5804_,
        v_msg_5805_,
        v___y_5806_,
        v___y_5807_,
        v___y_5808_,
        v___y_5809_,
    );
    lean_dec(v___y_5809_);
    lean_dec_ref(v___y_5808_);
    lean_dec(v___y_5807_);
    lean_dec_ref(v___y_5806_);
    return v_res_5811_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(
    mut v_sz_5812_: usize,
    mut v_i_5813_: usize,
    mut v_bs_5814_: *mut LeanObject,
    mut v___y_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5820_: u8 = 0;
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: usize = 0;
    let mut v___x_5828_: usize = 0;
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5834_: u8 = 0;
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5820_ = lean_usize_dec_lt(v_i_5813_, v_sz_5812_);
                if v___x_5820_ == 0 {
                    v___x_5821_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5821_, 0, v_bs_5814_);
                    return v___x_5821_;
                } else {
                    v_v_5822_ = lean_array_uget_borrowed(v_bs_5814_, v_i_5813_);
                    lean_inc(v_v_5822_);
                    v___x_5823_ = l_Lean_Elab_Mutual_cleanPreDef(
                        v_v_5822_,
                        v___x_5820_,
                        v___y_5815_,
                        v___y_5816_,
                        v___y_5817_,
                        v___y_5818_,
                    );
                    if lean_obj_tag(v___x_5823_) == 0 {
                        v_a_5824_ = lean_ctor_get(v___x_5823_, 0);
                        lean_inc(v_a_5824_);
                        lean_dec_ref_known(v___x_5823_, 1);
                        v___x_5825_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5826_ = lean_array_uset(v_bs_5814_, v_i_5813_, v___x_5825_);
                        v___x_5827_ = 1usize;
                        v___x_5828_ = lean_usize_add(v_i_5813_, v___x_5827_);
                        v___x_5829_ = lean_array_uset(v_bs_x27_5826_, v_i_5813_, v_a_5824_);
                        v_i_5813_ = v___x_5828_;
                        v_bs_5814_ = v___x_5829_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5814_);
                        v_a_5831_ = lean_ctor_get(v___x_5823_, 0);
                        v_isSharedCheck_5838_ = (!lean_is_exclusive(v___x_5823_)) as u8;
                        if v_isSharedCheck_5838_ == 0 {
                            v___x_5833_ = v___x_5823_;
                            v_isShared_5834_ = v_isSharedCheck_5838_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5831_);
                            lean_dec(v___x_5823_);
                            v___x_5833_ = lean_box(0);
                            v_isShared_5834_ = v_isSharedCheck_5838_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5834_ == 0 {
                    v___x_5836_ = v___x_5833_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5837_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5837_, 0, v_a_5831_);
                    v___x_5836_ = v_reuseFailAlloc_5837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___boxed(
    mut v_sz_5839_: *mut LeanObject,
    mut v_i_5840_: *mut LeanObject,
    mut v_bs_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5847_: usize = 0;
    let mut v_i_boxed_5848_: usize = 0;
    let mut v_res_5849_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5847_ = lean_unbox_usize(v_sz_5839_);
    lean_dec(v_sz_5839_);
    v_i_boxed_5848_ = lean_unbox_usize(v_i_5840_);
    lean_dec(v_i_5840_);
    v_res_5849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_boxed_5847_, v_i_boxed_5848_, v_bs_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_);
    lean_dec(v___y_5845_);
    lean_dec_ref(v___y_5844_);
    lean_dec(v___y_5843_);
    lean_dec_ref(v___y_5842_);
    return v_res_5849_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0(
    mut v_xs_5850_: *mut LeanObject,
    mut v_inst_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
    mut v___y_5854_: *mut LeanObject,
    mut v___y_5855_: *mut LeanObject,
    mut v___y_5856_: *mut LeanObject,
    mut v___y_5857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    v___x_5859_ = l_Lean_Meta_mkInstPiOfInstsForall(
        v_xs_5850_,
        v_inst_5851_,
        v___y_5854_,
        v___y_5855_,
        v___y_5856_,
        v___y_5857_,
    );
    return v___x_5859_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0___boxed(
    mut v_xs_5860_: *mut LeanObject,
    mut v_inst_5861_: *mut LeanObject,
    mut v___y_5862_: *mut LeanObject,
    mut v___y_5863_: *mut LeanObject,
    mut v___y_5864_: *mut LeanObject,
    mut v___y_5865_: *mut LeanObject,
    mut v___y_5866_: *mut LeanObject,
    mut v___y_5867_: *mut LeanObject,
    mut v___y_5868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5869_: *mut LeanObject = core::ptr::null_mut();
    v_res_5869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0(v_xs_5860_, v_inst_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_);
    lean_dec(v___y_5867_);
    lean_dec_ref(v___y_5866_);
    lean_dec(v___y_5865_);
    lean_dec_ref(v___y_5864_);
    lean_dec(v___y_5863_);
    lean_dec_ref(v___y_5862_);
    return v_res_5869_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(
    mut v_sz_5871_: usize,
    mut v_i_5872_: usize,
    mut v_bs_5873_: *mut LeanObject,
    mut v___y_5874_: *mut LeanObject,
    mut v___y_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
    mut v___y_5877_: *mut LeanObject,
    mut v___y_5878_: *mut LeanObject,
    mut v___y_5879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5881_: u8 = 0;
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: u8 = 0;
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: usize = 0;
    let mut v___x_5891_: usize = 0;
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5897_: u8 = 0;
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5881_ = lean_usize_dec_lt(v_i_5872_, v_sz_5871_);
                if v___x_5881_ == 0 {
                    v___x_5882_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5882_, 0, v_bs_5873_);
                    return v___x_5882_;
                } else {
                    v___f_5883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0;
                    v_v_5884_ = lean_array_uget_borrowed(v_bs_5873_, v_i_5872_);
                    v___x_5885_ = 0;
                    lean_inc(v_v_5884_);
                    v___x_5886_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_v_5884_, v___f_5883_, v___x_5885_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_);
                    if lean_obj_tag(v___x_5886_) == 0 {
                        v_a_5887_ = lean_ctor_get(v___x_5886_, 0);
                        lean_inc(v_a_5887_);
                        lean_dec_ref_known(v___x_5886_, 1);
                        v___x_5888_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5889_ = lean_array_uset(v_bs_5873_, v_i_5872_, v___x_5888_);
                        v___x_5890_ = 1usize;
                        v___x_5891_ = lean_usize_add(v_i_5872_, v___x_5890_);
                        v___x_5892_ = lean_array_uset(v_bs_x27_5889_, v_i_5872_, v_a_5887_);
                        v_i_5872_ = v___x_5891_;
                        v_bs_5873_ = v___x_5892_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5873_);
                        v_a_5894_ = lean_ctor_get(v___x_5886_, 0);
                        v_isSharedCheck_5901_ = (!lean_is_exclusive(v___x_5886_)) as u8;
                        if v_isSharedCheck_5901_ == 0 {
                            v___x_5896_ = v___x_5886_;
                            v_isShared_5897_ = v_isSharedCheck_5901_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5894_);
                            lean_dec(v___x_5886_);
                            v___x_5896_ = lean_box(0);
                            v_isShared_5897_ = v_isSharedCheck_5901_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5897_ == 0 {
                    v___x_5899_ = v___x_5896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5900_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_a_5894_);
                    v___x_5899_ = v_reuseFailAlloc_5900_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___boxed(
    mut v_sz_5902_: *mut LeanObject,
    mut v_i_5903_: *mut LeanObject,
    mut v_bs_5904_: *mut LeanObject,
    mut v___y_5905_: *mut LeanObject,
    mut v___y_5906_: *mut LeanObject,
    mut v___y_5907_: *mut LeanObject,
    mut v___y_5908_: *mut LeanObject,
    mut v___y_5909_: *mut LeanObject,
    mut v___y_5910_: *mut LeanObject,
    mut v___y_5911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5912_: usize = 0;
    let mut v_i_boxed_5913_: usize = 0;
    let mut v_res_5914_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5912_ = lean_unbox_usize(v_sz_5902_);
    lean_dec(v_sz_5902_);
    v_i_boxed_5913_ = lean_unbox_usize(v_i_5903_);
    lean_dec(v_i_5903_);
    v_res_5914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(v_sz_boxed_5912_, v_i_boxed_5913_, v_bs_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_);
    lean_dec(v___y_5910_);
    lean_dec_ref(v___y_5909_);
    lean_dec(v___y_5908_);
    lean_dec_ref(v___y_5907_);
    lean_dec(v___y_5906_);
    lean_dec_ref(v___y_5905_);
    return v_res_5914_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(
    mut v___x_5915_: *mut LeanObject,
    mut v_fixedArgs_5916_: *mut LeanObject,
    mut v_as_5917_: *mut LeanObject,
    mut v_i_5918_: *mut LeanObject,
    mut v_j_5919_: *mut LeanObject,
    mut v_bs_5920_: *mut LeanObject,
    mut v___y_5921_: *mut LeanObject,
    mut v___y_5922_: *mut LeanObject,
    mut v___y_5923_: *mut LeanObject,
    mut v___y_5924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5927_: u8 = 0;
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5942_: u8 = 0;
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5926_ = lean_unsigned_to_nat(0);
                v_isZero_5927_ = lean_nat_dec_eq(v_i_5918_, v_zero_5926_);
                if v_isZero_5927_ == 1 {
                    lean_dec(v_j_5919_);
                    lean_dec(v_i_5918_);
                    lean_dec_ref(v_fixedArgs_5916_);
                    v___x_5928_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5928_, 0, v_bs_5920_);
                    return v___x_5928_;
                } else {
                    v___x_5929_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
                    v___x_5930_ = lean_array_fget_borrowed(v_as_5917_, v_j_5919_);
                    v___x_5931_ = lean_array_get_borrowed(v___x_5929_, v___x_5915_, v_j_5919_);
                    lean_inc_ref(v_fixedArgs_5916_);
                    lean_inc(v___x_5930_);
                    lean_inc(v___x_5931_);
                    v___x_5932_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(
                        v___x_5931_,
                        v___x_5930_,
                        v_fixedArgs_5916_,
                        v___y_5921_,
                        v___y_5922_,
                        v___y_5923_,
                        v___y_5924_,
                    );
                    if lean_obj_tag(v___x_5932_) == 0 {
                        v_a_5933_ = lean_ctor_get(v___x_5932_, 0);
                        lean_inc(v_a_5933_);
                        lean_dec_ref_known(v___x_5932_, 1);
                        v_one_5934_ = lean_unsigned_to_nat(1);
                        v_n_5935_ = lean_nat_sub(v_i_5918_, v_one_5934_);
                        lean_dec(v_i_5918_);
                        v___x_5936_ = lean_nat_add(v_j_5919_, v_one_5934_);
                        lean_dec(v_j_5919_);
                        v___x_5937_ = lean_array_push(v_bs_5920_, v_a_5933_);
                        v_i_5918_ = v_n_5935_;
                        v_j_5919_ = v___x_5936_;
                        v_bs_5920_ = v___x_5937_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5920_);
                        lean_dec(v_j_5919_);
                        lean_dec(v_i_5918_);
                        lean_dec_ref(v_fixedArgs_5916_);
                        v_a_5939_ = lean_ctor_get(v___x_5932_, 0);
                        v_isSharedCheck_5946_ = (!lean_is_exclusive(v___x_5932_)) as u8;
                        if v_isSharedCheck_5946_ == 0 {
                            v___x_5941_ = v___x_5932_;
                            v_isShared_5942_ = v_isSharedCheck_5946_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5939_);
                            lean_dec(v___x_5932_);
                            v___x_5941_ = lean_box(0);
                            v_isShared_5942_ = v_isSharedCheck_5946_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5942_ == 0 {
                    v___x_5944_ = v___x_5941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5945_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_a_5939_);
                    v___x_5944_ = v_reuseFailAlloc_5945_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg___boxed(
    mut v___x_5947_: *mut LeanObject,
    mut v_fixedArgs_5948_: *mut LeanObject,
    mut v_as_5949_: *mut LeanObject,
    mut v_i_5950_: *mut LeanObject,
    mut v_j_5951_: *mut LeanObject,
    mut v_bs_5952_: *mut LeanObject,
    mut v___y_5953_: *mut LeanObject,
    mut v___y_5954_: *mut LeanObject,
    mut v___y_5955_: *mut LeanObject,
    mut v___y_5956_: *mut LeanObject,
    mut v___y_5957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5958_: *mut LeanObject = core::ptr::null_mut();
    v_res_5958_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(
        v___x_5947_,
        v_fixedArgs_5948_,
        v_as_5949_,
        v_i_5950_,
        v_j_5951_,
        v_bs_5952_,
        v___y_5953_,
        v___y_5954_,
        v___y_5955_,
        v___y_5956_,
    );
    lean_dec(v___y_5956_);
    lean_dec_ref(v___y_5955_);
    lean_dec(v___y_5954_);
    lean_dec_ref(v___y_5953_);
    lean_dec_ref(v_as_5949_);
    lean_dec_ref(v___x_5947_);
    return v_res_5958_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(
    mut v___x_5959_: *mut LeanObject,
    mut v_fixedArgs_5960_: *mut LeanObject,
    mut v_as_5961_: *mut LeanObject,
    mut v_i_5962_: *mut LeanObject,
    mut v_j_5963_: *mut LeanObject,
    mut v_bs_5964_: *mut LeanObject,
    mut v___y_5965_: *mut LeanObject,
    mut v___y_5966_: *mut LeanObject,
    mut v___y_5967_: *mut LeanObject,
    mut v___y_5968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5971_: u8 = 0;
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5987_: u8 = 0;
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5970_ = lean_unsigned_to_nat(0);
                v_isZero_5971_ = lean_nat_dec_eq(v_i_5962_, v_zero_5970_);
                if v_isZero_5971_ == 1 {
                    lean_dec(v_j_5963_);
                    lean_dec(v_i_5962_);
                    lean_dec_ref(v_fixedArgs_5960_);
                    v___x_5972_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5972_, 0, v_bs_5964_);
                    return v___x_5972_;
                } else {
                    v___x_5973_ = lean_array_fget_borrowed(v_as_5961_, v_j_5963_);
                    v_type_5974_ = lean_ctor_get(v___x_5973_, 6);
                    v___x_5975_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
                    v___x_5976_ = lean_array_get_borrowed(v___x_5975_, v___x_5959_, v_j_5963_);
                    lean_inc_ref(v_fixedArgs_5960_);
                    lean_inc_ref(v_type_5974_);
                    lean_inc(v___x_5976_);
                    v___x_5977_ = l_Lean_Elab_FixedParamPerm_instantiateForall(
                        v___x_5976_,
                        v_type_5974_,
                        v_fixedArgs_5960_,
                        v___y_5965_,
                        v___y_5966_,
                        v___y_5967_,
                        v___y_5968_,
                    );
                    if lean_obj_tag(v___x_5977_) == 0 {
                        v_a_5978_ = lean_ctor_get(v___x_5977_, 0);
                        lean_inc(v_a_5978_);
                        lean_dec_ref_known(v___x_5977_, 1);
                        v_one_5979_ = lean_unsigned_to_nat(1);
                        v_n_5980_ = lean_nat_sub(v_i_5962_, v_one_5979_);
                        lean_dec(v_i_5962_);
                        v___x_5981_ = lean_nat_add(v_j_5963_, v_one_5979_);
                        lean_dec(v_j_5963_);
                        v___x_5982_ = lean_array_push(v_bs_5964_, v_a_5978_);
                        v_i_5962_ = v_n_5980_;
                        v_j_5963_ = v___x_5981_;
                        v_bs_5964_ = v___x_5982_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5964_);
                        lean_dec(v_j_5963_);
                        lean_dec(v_i_5962_);
                        lean_dec_ref(v_fixedArgs_5960_);
                        v_a_5984_ = lean_ctor_get(v___x_5977_, 0);
                        v_isSharedCheck_5991_ = (!lean_is_exclusive(v___x_5977_)) as u8;
                        if v_isSharedCheck_5991_ == 0 {
                            v___x_5986_ = v___x_5977_;
                            v_isShared_5987_ = v_isSharedCheck_5991_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5984_);
                            lean_dec(v___x_5977_);
                            v___x_5986_ = lean_box(0);
                            v_isShared_5987_ = v_isSharedCheck_5991_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5987_ == 0 {
                    v___x_5989_ = v___x_5986_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5990_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_a_5984_);
                    v___x_5989_ = v_reuseFailAlloc_5990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg___boxed(
    mut v___x_5992_: *mut LeanObject,
    mut v_fixedArgs_5993_: *mut LeanObject,
    mut v_as_5994_: *mut LeanObject,
    mut v_i_5995_: *mut LeanObject,
    mut v_j_5996_: *mut LeanObject,
    mut v_bs_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
    mut v___y_6000_: *mut LeanObject,
    mut v___y_6001_: *mut LeanObject,
    mut v___y_6002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6003_: *mut LeanObject = core::ptr::null_mut();
    v_res_6003_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(
        v___x_5992_,
        v_fixedArgs_5993_,
        v_as_5994_,
        v_i_5995_,
        v_j_5996_,
        v_bs_5997_,
        v___y_5998_,
        v___y_5999_,
        v___y_6000_,
        v___y_6001_,
    );
    lean_dec(v___y_6001_);
    lean_dec_ref(v___y_6000_);
    lean_dec(v___y_5999_);
    lean_dec_ref(v___y_5998_);
    lean_dec_ref(v_as_5994_);
    lean_dec_ref(v___x_5992_);
    return v_res_6003_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2(
    mut v___x_6004_: *mut LeanObject,
    mut v_e_6005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    v___x_6006_ = l_Lean_indentD(v_e_6005_);
    v___x_6007_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_6007_, 0, v___x_6004_);
    lean_ctor_set(v___x_6007_, 1, v___x_6006_);
    return v___x_6007_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(
    mut v___f_6008_: *mut LeanObject,
    mut v___x_6009_: *mut LeanObject,
    mut v___y_6010_: *mut LeanObject,
    mut v___y_6011_: *mut LeanObject,
    mut v___y_6012_: *mut LeanObject,
    mut v___y_6013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    v___x_6015_ = l_Lean_Meta_Monotonicity_solveMono(
        v___f_6008_,
        v___x_6009_,
        v___y_6010_,
        v___y_6011_,
        v___y_6012_,
        v___y_6013_,
    );
    return v___x_6015_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed(
    mut v___f_6016_: *mut LeanObject,
    mut v___x_6017_: *mut LeanObject,
    mut v___y_6018_: *mut LeanObject,
    mut v___y_6019_: *mut LeanObject,
    mut v___y_6020_: *mut LeanObject,
    mut v___y_6021_: *mut LeanObject,
    mut v___y_6022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6023_: *mut LeanObject = core::ptr::null_mut();
    v_res_6023_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(
            v___f_6016_,
            v___x_6017_,
            v___y_6018_,
            v___y_6019_,
            v___y_6020_,
            v___y_6021_,
        );
    lean_dec(v___y_6021_);
    lean_dec_ref(v___y_6020_);
    lean_dec(v___y_6019_);
    lean_dec_ref(v___y_6018_);
    return v_res_6023_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1()
-> *mut LeanObject {
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    v___x_6025_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0;
    v___x_6026_ = l_Lean_stringToMessageData(v___x_6025_);
    return v___x_6026_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(
    mut v_a_6027_: *mut LeanObject,
    mut v_a_6028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6034_: u8 = 0;
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: u8 = 0;
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6027_) == 0 {
                    v___x_6029_ = l_List_reverse___redArg(v_a_6028_);
                    return v___x_6029_;
                } else {
                    v_head_6030_ = lean_ctor_get(v_a_6027_, 0);
                    v_tail_6031_ = lean_ctor_get(v_a_6027_, 1);
                    v_isSharedCheck_6044_ = (!lean_is_exclusive(v_a_6027_)) as u8;
                    if v_isSharedCheck_6044_ == 0 {
                        v___x_6033_ = v_a_6027_;
                        v_isShared_6034_ = v_isSharedCheck_6044_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6031_);
                        lean_inc(v_head_6030_);
                        lean_dec(v_a_6027_);
                        v___x_6033_ = lean_box(0);
                        v_isShared_6034_ = v_isSharedCheck_6044_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6035_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1);
                v___x_6036_ = 0;
                v___x_6037_ = l_Lean_MessageData_ofConstName(v_head_6030_, v___x_6036_);
                v___x_6038_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6038_, 0, v___x_6035_);
                lean_ctor_set(v___x_6038_, 1, v___x_6037_);
                v___x_6039_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6039_, 0, v___x_6038_);
                lean_ctor_set(v___x_6039_, 1, v___x_6035_);
                if v_isShared_6034_ == 0 {
                    lean_ctor_set(v___x_6033_, 1, v_a_6028_);
                    lean_ctor_set(v___x_6033_, 0, v___x_6039_);
                    v___x_6041_ = v___x_6033_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6043_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6043_, 0, v___x_6039_);
                    lean_ctor_set(v_reuseFailAlloc_6043_, 1, v_a_6028_);
                    v___x_6041_ = v_reuseFailAlloc_6043_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6027_ = v_tail_6031_;
                v_a_6028_ = v___x_6041_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    v___x_6047_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1;
    v___x_6048_ = l_Lean_stringToMessageData(v___x_6047_);
    return v___x_6048_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    v___x_6050_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3;
    v___x_6051_ = l_Lean_stringToMessageData(v___x_6050_);
    return v___x_6051_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    v___x_6053_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5;
    v___x_6054_ = l_Lean_stringToMessageData(v___x_6053_);
    return v___x_6054_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    v___x_6057_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8;
    v___x_6058_ = lean_unsigned_to_nat(52);
    v___x_6059_ = lean_unsigned_to_nat(148);
    v___x_6060_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7;
    v___x_6061_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0;
    v___x_6062_ = l_mkPanicMessageWithDecl(
        v___x_6061_,
        v___x_6060_,
        v___x_6059_,
        v___x_6058_,
        v___x_6057_,
    );
    return v___x_6062_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11()
-> *mut LeanObject {
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    v___x_6064_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10;
    v___x_6065_ = l_Lean_stringToMessageData(v___x_6064_);
    return v___x_6065_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13()
-> *mut LeanObject {
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    v___x_6067_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12;
    v___x_6068_ = l_Lean_stringToMessageData(v___x_6067_);
    return v___x_6068_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15()
-> *mut LeanObject {
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    v___x_6070_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14;
    v___x_6071_ = l_Lean_stringToMessageData(v___x_6070_);
    return v___x_6071_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19()
-> *mut LeanObject {
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut LeanObject = core::ptr::null_mut();
    v___x_6078_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18;
    v___x_6079_ = l_Lean_stringToMessageData(v___x_6078_);
    return v___x_6079_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20()
-> *mut LeanObject {
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    v___x_6080_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1;
    v___x_6081_ = l_Lean_stringToMessageData(v___x_6080_);
    return v___x_6081_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(
    mut v_monoThms_6082_: *mut LeanObject,
    mut v_t_6083_: *mut LeanObject,
    mut v___y_6084_: *mut LeanObject,
    mut v___y_6085_: *mut LeanObject,
    mut v___y_6086_: *mut LeanObject,
    mut v___y_6087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6108_: u8 = 0;
    let mut v_cancelTk_x3f_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6110_: u8 = 0;
    let mut v_inheritedTraceOptions_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: u8 = 0;
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6134_ = lean_array_get_size(v_monoThms_6082_);
                v___x_6135_ = lean_unsigned_to_nat(0);
                v___x_6136_ = lean_nat_dec_eq(v___x_6134_, v___x_6135_);
                if v___x_6136_ == 0 {
                    v___x_6137_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13);
                    v___x_6138_ = lean_array_to_list(v_monoThms_6082_);
                    v___x_6139_ = lean_box(0);
                    v___x_6140_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(
                        v___x_6138_,
                        v___x_6139_,
                    );
                    v___x_6141_ = l_Lean_MessageData_andList(v___x_6140_);
                    v___x_6142_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6142_, 0, v___x_6137_);
                    lean_ctor_set(v___x_6142_, 1, v___x_6141_);
                    v___x_6143_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15);
                    v___x_6144_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6144_, 0, v___x_6142_);
                    lean_ctor_set(v___x_6144_, 1, v___x_6143_);
                    v___x_6145_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17;
                    v___x_6146_ = l_Lean_MessageData_ofConstName(v___x_6145_, v___x_6136_);
                    v___x_6147_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6147_, 0, v___x_6144_);
                    lean_ctor_set(v___x_6147_, 1, v___x_6146_);
                    v___x_6148_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19);
                    v___x_6149_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6149_, 0, v___x_6147_);
                    lean_ctor_set(v___x_6149_, 1, v___x_6148_);
                    v___y_6090_ = v___x_6149_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_monoThms_6082_);
                    v___x_6150_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20);
                    v___y_6090_ = v___x_6150_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6091_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0;
                v___x_6092_ = lean_find_expr(v___x_6091_, v_t_6083_);
                if lean_obj_tag(v___x_6092_) == 1 {
                    v_val_6093_ = lean_ctor_get(v___x_6092_, 0);
                    lean_inc(v_val_6093_);
                    lean_dec_ref_known(v___x_6092_, 1);
                    v___x_6094_ = l_Lean_getRecAppSyntax_x3f(v_val_6093_);
                    lean_dec(v_val_6093_);
                    if lean_obj_tag(v___x_6094_) == 1 {
                        v_val_6095_ = lean_ctor_get(v___x_6094_, 0);
                        lean_inc_n(v_val_6095_, 2);
                        lean_dec_ref_known(v___x_6094_, 1);
                        v_fileName_6096_ = lean_ctor_get(v___y_6086_, 0);
                        v_fileMap_6097_ = lean_ctor_get(v___y_6086_, 1);
                        v_options_6098_ = lean_ctor_get(v___y_6086_, 2);
                        v_currRecDepth_6099_ = lean_ctor_get(v___y_6086_, 3);
                        v_maxRecDepth_6100_ = lean_ctor_get(v___y_6086_, 4);
                        v_ref_6101_ = lean_ctor_get(v___y_6086_, 5);
                        v_currNamespace_6102_ = lean_ctor_get(v___y_6086_, 6);
                        v_openDecls_6103_ = lean_ctor_get(v___y_6086_, 7);
                        v_initHeartbeats_6104_ = lean_ctor_get(v___y_6086_, 8);
                        v_maxHeartbeats_6105_ = lean_ctor_get(v___y_6086_, 9);
                        v_quotContext_6106_ = lean_ctor_get(v___y_6086_, 10);
                        v_currMacroScope_6107_ = lean_ctor_get(v___y_6086_, 11);
                        v_diag_6108_ = lean_ctor_get_uint8(
                            v___y_6086_,
                            (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        );
                        v_cancelTk_x3f_6109_ = lean_ctor_get(v___y_6086_, 12);
                        v_suppressElabErrors_6110_ = lean_ctor_get_uint8(
                            v___y_6086_,
                            (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        );
                        v_inheritedTraceOptions_6111_ = lean_ctor_get(v___y_6086_, 13);
                        v___x_6112_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2);
                        v___x_6113_ = l_Lean_MessageData_ofSyntax(v_val_6095_);
                        v___x_6114_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6114_, 0, v___x_6112_);
                        lean_ctor_set(v___x_6114_, 1, v___x_6113_);
                        v___x_6115_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4);
                        v___x_6116_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6116_, 0, v___x_6114_);
                        lean_ctor_set(v___x_6116_, 1, v___x_6115_);
                        v___x_6117_ = l_Lean_indentExpr(v_t_6083_);
                        v___x_6118_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6118_, 0, v___x_6116_);
                        lean_ctor_set(v___x_6118_, 1, v___x_6117_);
                        v___x_6119_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6);
                        v___x_6120_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6120_, 0, v___x_6118_);
                        lean_ctor_set(v___x_6120_, 1, v___x_6119_);
                        v___x_6121_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6121_, 0, v___x_6120_);
                        lean_ctor_set(v___x_6121_, 1, v___y_6090_);
                        v_ref_6122_ = l_Lean_replaceRef(v_val_6095_, v_ref_6101_);
                        lean_dec(v_val_6095_);
                        lean_inc_ref(v_inheritedTraceOptions_6111_);
                        lean_inc(v_cancelTk_x3f_6109_);
                        lean_inc(v_currMacroScope_6107_);
                        lean_inc(v_quotContext_6106_);
                        lean_inc(v_maxHeartbeats_6105_);
                        lean_inc(v_initHeartbeats_6104_);
                        lean_inc(v_openDecls_6103_);
                        lean_inc(v_currNamespace_6102_);
                        lean_inc(v_maxRecDepth_6100_);
                        lean_inc(v_currRecDepth_6099_);
                        lean_inc_ref(v_options_6098_);
                        lean_inc_ref(v_fileMap_6097_);
                        lean_inc_ref(v_fileName_6096_);
                        v___x_6123_ = lean_alloc_ctor(0, 14, (2) as u32);
                        lean_ctor_set(v___x_6123_, 0, v_fileName_6096_);
                        lean_ctor_set(v___x_6123_, 1, v_fileMap_6097_);
                        lean_ctor_set(v___x_6123_, 2, v_options_6098_);
                        lean_ctor_set(v___x_6123_, 3, v_currRecDepth_6099_);
                        lean_ctor_set(v___x_6123_, 4, v_maxRecDepth_6100_);
                        lean_ctor_set(v___x_6123_, 5, v_ref_6122_);
                        lean_ctor_set(v___x_6123_, 6, v_currNamespace_6102_);
                        lean_ctor_set(v___x_6123_, 7, v_openDecls_6103_);
                        lean_ctor_set(v___x_6123_, 8, v_initHeartbeats_6104_);
                        lean_ctor_set(v___x_6123_, 9, v_maxHeartbeats_6105_);
                        lean_ctor_set(v___x_6123_, 10, v_quotContext_6106_);
                        lean_ctor_set(v___x_6123_, 11, v_currMacroScope_6107_);
                        lean_ctor_set(v___x_6123_, 12, v_cancelTk_x3f_6109_);
                        lean_ctor_set(v___x_6123_, 13, v_inheritedTraceOptions_6111_);
                        lean_ctor_set_uint8(
                            v___x_6123_,
                            (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                            v_diag_6108_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6123_,
                            (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                            v_suppressElabErrors_6110_,
                        );
                        v___x_6124_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_6121_, v___y_6084_, v___y_6085_, v___x_6123_, v___y_6087_);
                        lean_dec_ref_known(v___x_6123_, 14);
                        return v___x_6124_;
                    } else {
                        lean_dec(v___x_6094_);
                        lean_dec_ref(v___y_6090_);
                        lean_dec_ref(v_t_6083_);
                        v___x_6125_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9);
                        v___x_6126_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(
                            v___x_6125_,
                            v___y_6084_,
                            v___y_6085_,
                            v___y_6086_,
                            v___y_6087_,
                        );
                        return v___x_6126_;
                    }
                } else {
                    lean_dec(v___x_6092_);
                    v___x_6127_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11);
                    v___x_6128_ = l_Lean_indentExpr(v_t_6083_);
                    v___x_6129_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6129_, 0, v___x_6127_);
                    lean_ctor_set(v___x_6129_, 1, v___x_6128_);
                    v___x_6130_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6);
                    v___x_6131_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6131_, 0, v___x_6129_);
                    lean_ctor_set(v___x_6131_, 1, v___x_6130_);
                    v___x_6132_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6132_, 0, v___x_6131_);
                    lean_ctor_set(v___x_6132_, 1, v___y_6090_);
                    v___x_6133_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_6132_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
                    return v___x_6133_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed(
    mut v_monoThms_6151_: *mut LeanObject,
    mut v_t_6152_: *mut LeanObject,
    mut v___y_6153_: *mut LeanObject,
    mut v___y_6154_: *mut LeanObject,
    mut v___y_6155_: *mut LeanObject,
    mut v___y_6156_: *mut LeanObject,
    mut v___y_6157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6158_: *mut LeanObject = core::ptr::null_mut();
    v_res_6158_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(
            v_monoThms_6151_,
            v_t_6152_,
            v___y_6153_,
            v___y_6154_,
            v___y_6155_,
            v___y_6156_,
        );
    lean_dec(v___y_6156_);
    lean_dec_ref(v___y_6155_);
    lean_dec(v___y_6154_);
    lean_dec_ref(v___y_6153_);
    return v_res_6158_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(
    mut v_preDefs_6159_: *mut LeanObject,
    mut v_a_6160_: *mut LeanObject,
    mut v_fixedArgs_6161_: *mut LeanObject,
    mut v_00_u03b1_6162_: *mut LeanObject,
    mut v_f_6163_: *mut LeanObject,
    mut v_monoThms_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
    mut v___y_6167_: *mut LeanObject,
    mut v___y_6168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    v___f_6170_ = lean_alloc_closure(
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_6170_, 0, v_monoThms_6164_);
    v___x_6171_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_6159_, v_a_6160_, v_fixedArgs_6161_, v_f_6163_, v___f_6170_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_);
    return v___x_6171_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed(
    mut v_preDefs_6172_: *mut LeanObject,
    mut v_a_6173_: *mut LeanObject,
    mut v_fixedArgs_6174_: *mut LeanObject,
    mut v_00_u03b1_6175_: *mut LeanObject,
    mut v_f_6176_: *mut LeanObject,
    mut v_monoThms_6177_: *mut LeanObject,
    mut v___y_6178_: *mut LeanObject,
    mut v___y_6179_: *mut LeanObject,
    mut v___y_6180_: *mut LeanObject,
    mut v___y_6181_: *mut LeanObject,
    mut v___y_6182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6183_: *mut LeanObject = core::ptr::null_mut();
    v_res_6183_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(
            v_preDefs_6172_,
            v_a_6173_,
            v_fixedArgs_6174_,
            v_00_u03b1_6175_,
            v_f_6176_,
            v_monoThms_6177_,
            v___y_6178_,
            v___y_6179_,
            v___y_6180_,
            v___y_6181_,
        );
    lean_dec(v___y_6181_);
    lean_dec_ref(v___y_6180_);
    lean_dec(v___y_6179_);
    lean_dec_ref(v___y_6178_);
    return v_res_6183_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    v___x_6185_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0;
    v___x_6186_ = l_Lean_stringToMessageData(v___x_6185_);
    return v___x_6186_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    v___x_6188_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2;
    v___x_6189_ = l_Lean_stringToMessageData(v___x_6188_);
    return v___x_6189_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
    v___x_6200_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7;
    v___x_6201_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9;
    v___x_6202_ = l_Lean_Name_append(v___x_6201_, v___x_6200_);
    return v___x_6202_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    v___x_6204_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11;
    v___x_6205_ = l_Lean_stringToMessageData(v___x_6204_);
    return v___x_6205_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14()
-> *mut LeanObject {
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    v___x_6207_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13;
    v___x_6208_ = l_Lean_stringToMessageData(v___x_6207_);
    return v___x_6208_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(
    mut v_a_6209_: *mut LeanObject,
    mut v_a_6210_: *mut LeanObject,
    mut v_a_6211_: *mut LeanObject,
    mut v_a_6212_: *mut LeanObject,
    mut v_a_6213_: *mut LeanObject,
    mut v_hints_6214_: *mut LeanObject,
    mut v_preDefs_6215_: *mut LeanObject,
    mut v_a_6216_: *mut LeanObject,
    mut v_fixedArgs_6217_: *mut LeanObject,
    mut v_as_6218_: *mut LeanObject,
    mut v_i_6219_: *mut LeanObject,
    mut v_j_6220_: *mut LeanObject,
    mut v_bs_6221_: *mut LeanObject,
    mut v___y_6222_: *mut LeanObject,
    mut v___y_6223_: *mut LeanObject,
    mut v___y_6224_: *mut LeanObject,
    mut v___y_6225_: *mut LeanObject,
    mut v___y_6226_: *mut LeanObject,
    mut v___y_6227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6230_: u8 = 0;
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6266_: u8 = 0;
    let mut v___x_6267_: u8 = 0;
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: u8 = 0;
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: u8 = 0;
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6290_: u8 = 0;
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6294_: u8 = 0;
    let mut v_a_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6298_: u8 = 0;
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6302_: u8 = 0;
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6307_: u8 = 0;
    let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6311_: u8 = 0;
    let mut v_a_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6315_: u8 = 0;
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6319_: u8 = 0;
    let mut v_reuseFailAlloc_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6321_: u8 = 0;
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6348_: u8 = 0;
    let mut v_inheritedTraceOptions_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: u8 = 0;
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6363_: u8 = 0;
    let mut v___x_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6367_: u8 = 0;
    let mut v_a_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6371_: u8 = 0;
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6375_: u8 = 0;
    let mut v_a_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6379_: u8 = 0;
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6383_: u8 = 0;
    let mut v_a_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6387_: u8 = 0;
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6391_: u8 = 0;
    let mut v_a_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6395_: u8 = 0;
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6399_: u8 = 0;
    let mut v_a_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6403_: u8 = 0;
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6229_ = lean_unsigned_to_nat(0);
                v_isZero_6230_ = lean_nat_dec_eq(v_i_6219_, v_zero_6229_);
                if v_isZero_6230_ == 1 {
                    lean_dec(v_j_6220_);
                    lean_dec(v_i_6219_);
                    lean_dec_ref(v_fixedArgs_6217_);
                    lean_dec_ref(v_a_6216_);
                    lean_dec_ref(v_preDefs_6215_);
                    lean_dec_ref(v_a_6213_);
                    lean_dec_ref(v_a_6212_);
                    v___x_6231_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6231_, 0, v_bs_6221_);
                    return v___x_6231_;
                } else {
                    v___x_6232_ = l_Lean_instInhabitedExpr;
                    v___x_6233_ = lean_array_get_borrowed(v___x_6232_, v_a_6209_, v_j_6220_);
                    v___x_6234_ = lean_array_get_borrowed(v___x_6232_, v_a_6210_, v_j_6220_);
                    lean_inc(v___x_6233_);
                    v___x_6235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6235_, 0, v___x_6233_);
                    lean_inc_ref(v___x_6235_);
                    lean_inc(v___x_6234_);
                    v___x_6236_ = l_Lean_Meta_toPartialOrder(
                        v___x_6234_,
                        v___x_6235_,
                        v___y_6224_,
                        v___y_6225_,
                        v___y_6226_,
                        v___y_6227_,
                    );
                    if lean_obj_tag(v___x_6236_) == 0 {
                        v_a_6237_ = lean_ctor_get(v___x_6236_, 0);
                        lean_inc(v_a_6237_);
                        lean_dec_ref_known(v___x_6236_, 1);
                        v___x_6238_ = lean_array_get_borrowed(v___x_6232_, v_a_6211_, v_j_6220_);
                        v___x_6239_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5;
                        lean_inc_ref(v_a_6212_);
                        v___x_6240_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6240_, 0, v_a_6212_);
                        lean_inc_ref(v_a_6213_);
                        v___x_6241_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6241_, 0, v_a_6213_);
                        v___x_6242_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6242_, 0, v_a_6237_);
                        lean_inc(v___x_6238_);
                        v___x_6243_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6243_, 0, v___x_6238_);
                        v___x_6244_ = lean_unsigned_to_nat(5);
                        v___x_6245_ = lean_mk_empty_array_with_capacity(v___x_6244_);
                        v___x_6246_ = lean_array_push(v___x_6245_, v___x_6240_);
                        v___x_6247_ = lean_array_push(v___x_6246_, v___x_6241_);
                        v___x_6248_ = lean_array_push(v___x_6247_, v___x_6235_);
                        v___x_6249_ = lean_array_push(v___x_6248_, v___x_6242_);
                        v___x_6250_ = lean_array_push(v___x_6249_, v___x_6243_);
                        v___x_6251_ = l_Lean_Meta_mkAppOptM(
                            v___x_6239_,
                            v___x_6250_,
                            v___y_6224_,
                            v___y_6225_,
                            v___y_6226_,
                            v___y_6227_,
                        );
                        if lean_obj_tag(v___x_6251_) == 0 {
                            v_a_6252_ = lean_ctor_get(v___x_6251_, 0);
                            lean_inc(v_a_6252_);
                            lean_dec_ref_known(v___x_6251_, 1);
                            v___x_6253_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
                            v___x_6254_ =
                                lean_array_get_borrowed(v___x_6253_, v_hints_6214_, v_j_6220_);
                            v_term_x3f_6255_ = lean_ctor_get(v___x_6254_, 1);
                            lean_inc(v_term_x3f_6255_);
                            v_one_6256_ = lean_unsigned_to_nat(1);
                            v_n_6257_ = lean_nat_sub(v_i_6219_, v_one_6256_);
                            lean_dec(v_i_6219_);
                            if lean_obj_tag(v_term_x3f_6255_) == 1 {
                                v_val_6263_ = lean_ctor_get(v_term_x3f_6255_, 0);
                                v_isSharedCheck_6321_ =
                                    (!lean_is_exclusive(v_term_x3f_6255_)) as u8;
                                if v_isSharedCheck_6321_ == 0 {
                                    v___x_6265_ = v_term_x3f_6255_;
                                    v_isShared_6266_ = v_isSharedCheck_6321_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_val_6263_);
                                    lean_dec(v_term_x3f_6255_);
                                    v___x_6265_ = lean_box(0);
                                    v_isShared_6266_ = v_isSharedCheck_6321_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_term_x3f_6255_);
                                v___x_6322_ = lean_box(0);
                                lean_inc(v_a_6252_);
                                v___x_6323_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                    v_a_6252_,
                                    v___x_6322_,
                                    v___y_6224_,
                                    v___y_6225_,
                                    v___y_6226_,
                                    v___y_6227_,
                                );
                                if lean_obj_tag(v___x_6323_) == 0 {
                                    v_a_6324_ = lean_ctor_get(v___x_6323_, 0);
                                    lean_inc(v_a_6324_);
                                    lean_dec_ref_known(v___x_6323_, 1);
                                    v___x_6335_ = lean_array_fget_borrowed(v_as_6218_, v_j_6220_);
                                    v_declName_6336_ = lean_ctor_get(v___x_6335_, 3);
                                    lean_inc_ref(v_fixedArgs_6217_);
                                    lean_inc_ref(v_a_6216_);
                                    lean_inc_ref(v_preDefs_6215_);
                                    v___f_6337_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed as *mut core::ffi::c_void, 11, 3);
                                    lean_closure_set(v___f_6337_, 0, v_preDefs_6215_);
                                    lean_closure_set(v___f_6337_, 1, v_a_6216_);
                                    lean_closure_set(v___f_6337_, 2, v_fixedArgs_6217_);
                                    v___x_6338_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1);
                                    lean_inc(v_declName_6336_);
                                    v___x_6339_ = l_Lean_MessageData_ofName(v_declName_6336_);
                                    lean_inc_ref(v___x_6339_);
                                    v___x_6340_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6340_, 0, v___x_6338_);
                                    lean_ctor_set(v___x_6340_, 1, v___x_6339_);
                                    v___x_6341_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3);
                                    v___x_6342_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_6342_, 0, v___x_6340_);
                                    lean_ctor_set(v___x_6342_, 1, v___x_6341_);
                                    v___f_6343_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2 as *mut core::ffi::c_void, 2, 1);
                                    lean_closure_set(v___f_6343_, 0, v___x_6342_);
                                    v___x_6344_ = l_Lean_Expr_mvarId_x21(v_a_6324_);
                                    v___f_6345_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed as *mut core::ffi::c_void, 7, 2);
                                    lean_closure_set(v___f_6345_, 0, v___f_6337_);
                                    lean_closure_set(v___f_6345_, 1, v___x_6344_);
                                    v___x_6346_ = l_Lean_Meta_mapErrorImp___redArg(
                                        v___f_6345_,
                                        v___f_6343_,
                                        v___y_6224_,
                                        v___y_6225_,
                                        v___y_6226_,
                                        v___y_6227_,
                                    );
                                    if lean_obj_tag(v___x_6346_) == 0 {
                                        if lean_obj_tag(v___x_6346_) == 0 {
                                            lean_dec_ref_known(v___x_6346_, 1);
                                            v_options_6347_ = lean_ctor_get(v___y_6226_, 2);
                                            v_hasTrace_6348_ = lean_ctor_get_uint8(
                                                v_options_6347_,
                                                (core::mem::size_of::<*mut LeanObject>() * 1)
                                                    as u32,
                                            );
                                            if v_hasTrace_6348_ == 0 {
                                                lean_dec_ref(v___x_6339_);
                                                v___y_6326_ = v___y_6222_;
                                                v___y_6327_ = v___y_6223_;
                                                v___y_6328_ = v___y_6224_;
                                                v___y_6329_ = v___y_6225_;
                                                v___y_6330_ = v___y_6226_;
                                                v___y_6331_ = v___y_6227_;
                                                state = 12;
                                                continue;
                                            } else {
                                                v_inheritedTraceOptions_6349_ =
                                                    lean_ctor_get(v___y_6226_, 13);
                                                v___x_6350_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7;
                                                v___x_6351_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
                                                v___x_6352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6349_, v_options_6347_, v___x_6351_);
                                                if v___x_6352_ == 0 {
                                                    lean_dec_ref(v___x_6339_);
                                                    v___y_6326_ = v___y_6222_;
                                                    v___y_6327_ = v___y_6223_;
                                                    v___y_6328_ = v___y_6224_;
                                                    v___y_6329_ = v___y_6225_;
                                                    v___y_6330_ = v___y_6226_;
                                                    v___y_6331_ = v___y_6227_;
                                                    state = 12;
                                                    continue;
                                                } else {
                                                    v___x_6353_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12);
                                                    v___x_6354_ = lean_alloc_ctor(7, 2, (0) as u32);
                                                    lean_ctor_set(v___x_6354_, 0, v___x_6353_);
                                                    lean_ctor_set(v___x_6354_, 1, v___x_6339_);
                                                    v___x_6355_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14);
                                                    v___x_6356_ = lean_alloc_ctor(7, 2, (0) as u32);
                                                    lean_ctor_set(v___x_6356_, 0, v___x_6354_);
                                                    lean_ctor_set(v___x_6356_, 1, v___x_6355_);
                                                    lean_inc(v_a_6324_);
                                                    v___x_6357_ =
                                                        l_Lean_MessageData_ofExpr(v_a_6324_);
                                                    v___x_6358_ = lean_alloc_ctor(7, 2, (0) as u32);
                                                    lean_ctor_set(v___x_6358_, 0, v___x_6356_);
                                                    lean_ctor_set(v___x_6358_, 1, v___x_6357_);
                                                    v___x_6359_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v___x_6350_, v___x_6358_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_);
                                                    if lean_obj_tag(v___x_6359_) == 0 {
                                                        lean_dec_ref_known(v___x_6359_, 1);
                                                        v___y_6326_ = v___y_6222_;
                                                        v___y_6327_ = v___y_6223_;
                                                        v___y_6328_ = v___y_6224_;
                                                        v___y_6329_ = v___y_6225_;
                                                        v___y_6330_ = v___y_6226_;
                                                        v___y_6331_ = v___y_6227_;
                                                        state = 12;
                                                        continue;
                                                    } else {
                                                        lean_dec(v_a_6324_);
                                                        lean_dec(v_n_6257_);
                                                        lean_dec(v_a_6252_);
                                                        lean_dec_ref(v_bs_6221_);
                                                        lean_dec(v_j_6220_);
                                                        lean_dec_ref(v_fixedArgs_6217_);
                                                        lean_dec_ref(v_a_6216_);
                                                        lean_dec_ref(v_preDefs_6215_);
                                                        lean_dec_ref(v_a_6213_);
                                                        lean_dec_ref(v_a_6212_);
                                                        v_a_6360_ = lean_ctor_get(v___x_6359_, 0);
                                                        v_isSharedCheck_6367_ =
                                                            (!lean_is_exclusive(v___x_6359_)) as u8;
                                                        if v_isSharedCheck_6367_ == 0 {
                                                            v___x_6362_ = v___x_6359_;
                                                            v_isShared_6363_ =
                                                                v_isSharedCheck_6367_;
                                                            state = 13;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_6360_);
                                                            lean_dec(v___x_6359_);
                                                            v___x_6362_ = lean_box(0);
                                                            v_isShared_6363_ =
                                                                v_isSharedCheck_6367_;
                                                            state = 13;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_6339_);
                                            lean_dec(v_a_6324_);
                                            lean_dec(v_n_6257_);
                                            lean_dec(v_a_6252_);
                                            lean_dec_ref(v_bs_6221_);
                                            lean_dec(v_j_6220_);
                                            lean_dec_ref(v_fixedArgs_6217_);
                                            lean_dec_ref(v_a_6216_);
                                            lean_dec_ref(v_preDefs_6215_);
                                            lean_dec_ref(v_a_6213_);
                                            lean_dec_ref(v_a_6212_);
                                            v_a_6368_ = lean_ctor_get(v___x_6346_, 0);
                                            v_isSharedCheck_6375_ =
                                                (!lean_is_exclusive(v___x_6346_)) as u8;
                                            if v_isSharedCheck_6375_ == 0 {
                                                v___x_6370_ = v___x_6346_;
                                                v_isShared_6371_ = v_isSharedCheck_6375_;
                                                state = 15;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6368_);
                                                lean_dec(v___x_6346_);
                                                v___x_6370_ = lean_box(0);
                                                v_isShared_6371_ = v_isSharedCheck_6375_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6339_);
                                        lean_dec(v_a_6324_);
                                        lean_dec(v_n_6257_);
                                        lean_dec(v_a_6252_);
                                        lean_dec_ref(v_bs_6221_);
                                        lean_dec(v_j_6220_);
                                        lean_dec_ref(v_fixedArgs_6217_);
                                        lean_dec_ref(v_a_6216_);
                                        lean_dec_ref(v_preDefs_6215_);
                                        lean_dec_ref(v_a_6213_);
                                        lean_dec_ref(v_a_6212_);
                                        v_a_6376_ = lean_ctor_get(v___x_6346_, 0);
                                        v_isSharedCheck_6383_ =
                                            (!lean_is_exclusive(v___x_6346_)) as u8;
                                        if v_isSharedCheck_6383_ == 0 {
                                            v___x_6378_ = v___x_6346_;
                                            v_isShared_6379_ = v_isSharedCheck_6383_;
                                            state = 17;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6376_);
                                            lean_dec(v___x_6346_);
                                            v___x_6378_ = lean_box(0);
                                            v_isShared_6379_ = v_isSharedCheck_6383_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_n_6257_);
                                    lean_dec(v_a_6252_);
                                    lean_dec_ref(v_bs_6221_);
                                    lean_dec(v_j_6220_);
                                    lean_dec_ref(v_fixedArgs_6217_);
                                    lean_dec_ref(v_a_6216_);
                                    lean_dec_ref(v_preDefs_6215_);
                                    lean_dec_ref(v_a_6213_);
                                    lean_dec_ref(v_a_6212_);
                                    v_a_6384_ = lean_ctor_get(v___x_6323_, 0);
                                    v_isSharedCheck_6391_ = (!lean_is_exclusive(v___x_6323_)) as u8;
                                    if v_isSharedCheck_6391_ == 0 {
                                        v___x_6386_ = v___x_6323_;
                                        v_isShared_6387_ = v_isSharedCheck_6391_;
                                        state = 19;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6384_);
                                        lean_dec(v___x_6323_);
                                        v___x_6386_ = lean_box(0);
                                        v_isShared_6387_ = v_isSharedCheck_6391_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_bs_6221_);
                            lean_dec(v_j_6220_);
                            lean_dec(v_i_6219_);
                            lean_dec_ref(v_fixedArgs_6217_);
                            lean_dec_ref(v_a_6216_);
                            lean_dec_ref(v_preDefs_6215_);
                            lean_dec_ref(v_a_6213_);
                            lean_dec_ref(v_a_6212_);
                            v_a_6392_ = lean_ctor_get(v___x_6251_, 0);
                            v_isSharedCheck_6399_ = (!lean_is_exclusive(v___x_6251_)) as u8;
                            if v_isSharedCheck_6399_ == 0 {
                                v___x_6394_ = v___x_6251_;
                                v_isShared_6395_ = v_isSharedCheck_6399_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_6392_);
                                lean_dec(v___x_6251_);
                                v___x_6394_ = lean_box(0);
                                v_isShared_6395_ = v_isSharedCheck_6399_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v___x_6235_, 1);
                        lean_dec_ref(v_bs_6221_);
                        lean_dec(v_j_6220_);
                        lean_dec(v_i_6219_);
                        lean_dec_ref(v_fixedArgs_6217_);
                        lean_dec_ref(v_a_6216_);
                        lean_dec_ref(v_preDefs_6215_);
                        lean_dec_ref(v_a_6213_);
                        lean_dec_ref(v_a_6212_);
                        v_a_6400_ = lean_ctor_get(v___x_6236_, 0);
                        v_isSharedCheck_6407_ = (!lean_is_exclusive(v___x_6236_)) as u8;
                        if v_isSharedCheck_6407_ == 0 {
                            v___x_6402_ = v___x_6236_;
                            v_isShared_6403_ = v_isSharedCheck_6407_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_6400_);
                            lean_dec(v___x_6236_);
                            v___x_6402_ = lean_box(0);
                            v_isShared_6403_ = v_isSharedCheck_6407_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6260_ = lean_nat_add(v_j_6220_, v_one_6256_);
                lean_dec(v_j_6220_);
                v___x_6261_ = lean_array_push(v_bs_6221_, v_a_6259_);
                v_i_6219_ = v_n_6257_;
                v_j_6220_ = v___x_6260_;
                v_bs_6221_ = v___x_6261_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6267_ = 1;
                lean_inc(v_a_6252_);
                if v_isShared_6266_ == 0 {
                    lean_ctor_set(v___x_6265_, 0, v_a_6252_);
                    v___x_6269_ = v___x_6265_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6320_, 0, v_a_6252_);
                    v___x_6269_ = v_reuseFailAlloc_6320_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6270_ = lean_box(0);
                v___x_6271_ = lean_box((v___x_6267_) as usize);
                v___x_6272_ = lean_box((v___x_6267_) as usize);
                v___x_6273_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_6273_, 0, v_val_6263_);
                lean_closure_set(v___x_6273_, 1, v___x_6269_);
                lean_closure_set(v___x_6273_, 2, v___x_6271_);
                lean_closure_set(v___x_6273_, 3, v___x_6272_);
                lean_closure_set(v___x_6273_, 4, v___x_6270_);
                v___x_6274_ = 1;
                v___x_6275_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_6273_,
                        v___x_6274_,
                        v___y_6222_,
                        v___y_6223_,
                        v___y_6224_,
                        v___y_6225_,
                        v___y_6226_,
                        v___y_6227_,
                    );
                if lean_obj_tag(v___x_6275_) == 0 {
                    v_a_6276_ = lean_ctor_get(v___x_6275_, 0);
                    lean_inc(v_a_6276_);
                    lean_dec_ref_known(v___x_6275_, 1);
                    v___x_6277_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_a_6276_, v___y_6225_);
                    v_a_6278_ = lean_ctor_get(v___x_6277_, 0);
                    lean_inc_n(v_a_6278_, 2);
                    lean_dec_ref(v___x_6277_);
                    v___x_6279_ = l_Lean_Meta_getMVars(
                        v_a_6278_,
                        v___y_6224_,
                        v___y_6225_,
                        v___y_6226_,
                        v___y_6227_,
                    );
                    if lean_obj_tag(v___x_6279_) == 0 {
                        v_a_6280_ = lean_ctor_get(v___x_6279_, 0);
                        lean_inc(v_a_6280_);
                        lean_dec_ref_known(v___x_6279_, 1);
                        v___x_6281_ = lean_array_get_size(v_a_6280_);
                        v___x_6282_ = lean_nat_dec_eq(v___x_6281_, v_zero_6229_);
                        if v___x_6282_ == 0 {
                            lean_dec(v_a_6278_);
                            v___x_6283_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                                v_a_6280_,
                                v___x_6270_,
                                v___y_6222_,
                                v___y_6223_,
                                v___y_6224_,
                                v___y_6225_,
                                v___y_6226_,
                                v___y_6227_,
                            );
                            lean_dec(v_a_6280_);
                            if lean_obj_tag(v___x_6283_) == 0 {
                                lean_dec_ref_known(v___x_6283_, 1);
                                lean_inc(v_a_6252_);
                                v___x_6284_ = l_Lean_Meta_mkSorry(
                                    v_a_6252_,
                                    v___x_6267_,
                                    v___y_6224_,
                                    v___y_6225_,
                                    v___y_6226_,
                                    v___y_6227_,
                                );
                                if lean_obj_tag(v___x_6284_) == 0 {
                                    v_a_6285_ = lean_ctor_get(v___x_6284_, 0);
                                    lean_inc(v_a_6285_);
                                    lean_dec_ref_known(v___x_6284_, 1);
                                    v___x_6286_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_6286_, 0, v_a_6252_);
                                    lean_ctor_set(v___x_6286_, 1, v_a_6285_);
                                    v_a_6259_ = v___x_6286_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_n_6257_);
                                    lean_dec(v_a_6252_);
                                    lean_dec_ref(v_bs_6221_);
                                    lean_dec(v_j_6220_);
                                    lean_dec_ref(v_fixedArgs_6217_);
                                    lean_dec_ref(v_a_6216_);
                                    lean_dec_ref(v_preDefs_6215_);
                                    lean_dec_ref(v_a_6213_);
                                    lean_dec_ref(v_a_6212_);
                                    v_a_6287_ = lean_ctor_get(v___x_6284_, 0);
                                    v_isSharedCheck_6294_ = (!lean_is_exclusive(v___x_6284_)) as u8;
                                    if v_isSharedCheck_6294_ == 0 {
                                        v___x_6289_ = v___x_6284_;
                                        v_isShared_6290_ = v_isSharedCheck_6294_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6287_);
                                        lean_dec(v___x_6284_);
                                        v___x_6289_ = lean_box(0);
                                        v_isShared_6290_ = v_isSharedCheck_6294_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_n_6257_);
                                lean_dec(v_a_6252_);
                                lean_dec_ref(v_bs_6221_);
                                lean_dec(v_j_6220_);
                                lean_dec_ref(v_fixedArgs_6217_);
                                lean_dec_ref(v_a_6216_);
                                lean_dec_ref(v_preDefs_6215_);
                                lean_dec_ref(v_a_6213_);
                                lean_dec_ref(v_a_6212_);
                                v_a_6295_ = lean_ctor_get(v___x_6283_, 0);
                                v_isSharedCheck_6302_ = (!lean_is_exclusive(v___x_6283_)) as u8;
                                if v_isSharedCheck_6302_ == 0 {
                                    v___x_6297_ = v___x_6283_;
                                    v_isShared_6298_ = v_isSharedCheck_6302_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_6295_);
                                    lean_dec(v___x_6283_);
                                    v___x_6297_ = lean_box(0);
                                    v_isShared_6298_ = v_isSharedCheck_6302_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6280_);
                            v___x_6303_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_6303_, 0, v_a_6252_);
                            lean_ctor_set(v___x_6303_, 1, v_a_6278_);
                            v_a_6259_ = v___x_6303_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6278_);
                        lean_dec(v_n_6257_);
                        lean_dec(v_a_6252_);
                        lean_dec_ref(v_bs_6221_);
                        lean_dec(v_j_6220_);
                        lean_dec_ref(v_fixedArgs_6217_);
                        lean_dec_ref(v_a_6216_);
                        lean_dec_ref(v_preDefs_6215_);
                        lean_dec_ref(v_a_6213_);
                        lean_dec_ref(v_a_6212_);
                        v_a_6304_ = lean_ctor_get(v___x_6279_, 0);
                        v_isSharedCheck_6311_ = (!lean_is_exclusive(v___x_6279_)) as u8;
                        if v_isSharedCheck_6311_ == 0 {
                            v___x_6306_ = v___x_6279_;
                            v_isShared_6307_ = v_isSharedCheck_6311_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6304_);
                            lean_dec(v___x_6279_);
                            v___x_6306_ = lean_box(0);
                            v_isShared_6307_ = v_isSharedCheck_6311_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_n_6257_);
                    lean_dec(v_a_6252_);
                    lean_dec_ref(v_bs_6221_);
                    lean_dec(v_j_6220_);
                    lean_dec_ref(v_fixedArgs_6217_);
                    lean_dec_ref(v_a_6216_);
                    lean_dec_ref(v_preDefs_6215_);
                    lean_dec_ref(v_a_6213_);
                    lean_dec_ref(v_a_6212_);
                    v_a_6312_ = lean_ctor_get(v___x_6275_, 0);
                    v_isSharedCheck_6319_ = (!lean_is_exclusive(v___x_6275_)) as u8;
                    if v_isSharedCheck_6319_ == 0 {
                        v___x_6314_ = v___x_6275_;
                        v_isShared_6315_ = v_isSharedCheck_6319_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6312_);
                        lean_dec(v___x_6275_);
                        v___x_6314_ = lean_box(0);
                        v_isShared_6315_ = v_isSharedCheck_6319_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_6290_ == 0 {
                    v___x_6292_ = v___x_6289_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6293_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6293_, 0, v_a_6287_);
                    v___x_6292_ = v_reuseFailAlloc_6293_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6292_;
            }
            6 => {
                if v_isShared_6298_ == 0 {
                    v___x_6300_ = v___x_6297_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6301_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6301_, 0, v_a_6295_);
                    v___x_6300_ = v_reuseFailAlloc_6301_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6300_;
            }
            8 => {
                if v_isShared_6307_ == 0 {
                    v___x_6309_ = v___x_6306_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_a_6304_);
                    v___x_6309_ = v_reuseFailAlloc_6310_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6309_;
            }
            10 => {
                if v_isShared_6315_ == 0 {
                    v___x_6317_ = v___x_6314_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6318_, 0, v_a_6312_);
                    v___x_6317_ = v_reuseFailAlloc_6318_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6317_;
            }
            12 => {
                v___x_6332_ =
                    l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(
                        v_a_6324_,
                        v___y_6329_,
                    );
                v_a_6333_ = lean_ctor_get(v___x_6332_, 0);
                lean_inc(v_a_6333_);
                lean_dec_ref(v___x_6332_);
                v___x_6334_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6334_, 0, v_a_6252_);
                lean_ctor_set(v___x_6334_, 1, v_a_6333_);
                v_a_6259_ = v___x_6334_;
                state = 1;
                continue;
            }
            13 => {
                if v_isShared_6363_ == 0 {
                    v___x_6365_ = v___x_6362_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6366_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6366_, 0, v_a_6360_);
                    v___x_6365_ = v_reuseFailAlloc_6366_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6365_;
            }
            15 => {
                if v_isShared_6371_ == 0 {
                    lean_ctor_set_tag(v___x_6370_, 1);
                    v___x_6373_ = v___x_6370_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6374_, 0, v_a_6368_);
                    v___x_6373_ = v_reuseFailAlloc_6374_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6373_;
            }
            17 => {
                if v_isShared_6379_ == 0 {
                    v___x_6381_ = v___x_6378_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6382_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_a_6376_);
                    v___x_6381_ = v_reuseFailAlloc_6382_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6381_;
            }
            19 => {
                if v_isShared_6387_ == 0 {
                    v___x_6389_ = v___x_6386_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6390_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6390_, 0, v_a_6384_);
                    v___x_6389_ = v_reuseFailAlloc_6390_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6389_;
            }
            21 => {
                if v_isShared_6395_ == 0 {
                    v___x_6397_ = v___x_6394_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6398_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6398_, 0, v_a_6392_);
                    v___x_6397_ = v_reuseFailAlloc_6398_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6397_;
            }
            23 => {
                if v_isShared_6403_ == 0 {
                    v___x_6405_ = v___x_6402_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6406_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6406_, 0, v_a_6400_);
                    v___x_6405_ = v_reuseFailAlloc_6406_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6408_: *mut LeanObject = *_args.add(0);
    let mut v_a_6409_: *mut LeanObject = *_args.add(1);
    let mut v_a_6410_: *mut LeanObject = *_args.add(2);
    let mut v_a_6411_: *mut LeanObject = *_args.add(3);
    let mut v_a_6412_: *mut LeanObject = *_args.add(4);
    let mut v_hints_6413_: *mut LeanObject = *_args.add(5);
    let mut v_preDefs_6414_: *mut LeanObject = *_args.add(6);
    let mut v_a_6415_: *mut LeanObject = *_args.add(7);
    let mut v_fixedArgs_6416_: *mut LeanObject = *_args.add(8);
    let mut v_as_6417_: *mut LeanObject = *_args.add(9);
    let mut v_i_6418_: *mut LeanObject = *_args.add(10);
    let mut v_j_6419_: *mut LeanObject = *_args.add(11);
    let mut v_bs_6420_: *mut LeanObject = *_args.add(12);
    let mut v___y_6421_: *mut LeanObject = *_args.add(13);
    let mut v___y_6422_: *mut LeanObject = *_args.add(14);
    let mut v___y_6423_: *mut LeanObject = *_args.add(15);
    let mut v___y_6424_: *mut LeanObject = *_args.add(16);
    let mut v___y_6425_: *mut LeanObject = *_args.add(17);
    let mut v___y_6426_: *mut LeanObject = *_args.add(18);
    let mut v___y_6427_: *mut LeanObject = *_args.add(19);
    let mut v_res_6428_: *mut LeanObject = core::ptr::null_mut();
    v_res_6428_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(
        v_a_6408_,
        v_a_6409_,
        v_a_6410_,
        v_a_6411_,
        v_a_6412_,
        v_hints_6413_,
        v_preDefs_6414_,
        v_a_6415_,
        v_fixedArgs_6416_,
        v_as_6417_,
        v_i_6418_,
        v_j_6419_,
        v_bs_6420_,
        v___y_6421_,
        v___y_6422_,
        v___y_6423_,
        v___y_6424_,
        v___y_6425_,
        v___y_6426_,
    );
    lean_dec(v___y_6426_);
    lean_dec_ref(v___y_6425_);
    lean_dec(v___y_6424_);
    lean_dec_ref(v___y_6423_);
    lean_dec(v___y_6422_);
    lean_dec_ref(v___y_6421_);
    lean_dec_ref(v_as_6417_);
    lean_dec_ref(v_hints_6413_);
    lean_dec_ref(v_a_6410_);
    lean_dec_ref(v_a_6409_);
    lean_dec_ref(v_a_6408_);
    return v_res_6428_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19(
    mut v_a_6429_: *mut LeanObject,
    mut v_a_6430_: *mut LeanObject,
    mut v_a_6431_: *mut LeanObject,
    mut v_a_6432_: *mut LeanObject,
    mut v_a_6433_: *mut LeanObject,
    mut v_hints_6434_: *mut LeanObject,
    mut v_preDefs_6435_: *mut LeanObject,
    mut v_a_6436_: *mut LeanObject,
    mut v_fixedArgs_6437_: *mut LeanObject,
    mut v_as_6438_: *mut LeanObject,
    mut v_i_6439_: *mut LeanObject,
    mut v_j_6440_: *mut LeanObject,
    mut v_inv_6441_: *mut LeanObject,
    mut v_bs_6442_: *mut LeanObject,
    mut v___y_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
    mut v___y_6445_: *mut LeanObject,
    mut v___y_6446_: *mut LeanObject,
    mut v___y_6447_: *mut LeanObject,
    mut v___y_6448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    v___x_6450_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(
        v_a_6429_,
        v_a_6430_,
        v_a_6431_,
        v_a_6432_,
        v_a_6433_,
        v_hints_6434_,
        v_preDefs_6435_,
        v_a_6436_,
        v_fixedArgs_6437_,
        v_as_6438_,
        v_i_6439_,
        v_j_6440_,
        v_bs_6442_,
        v___y_6443_,
        v___y_6444_,
        v___y_6445_,
        v___y_6446_,
        v___y_6447_,
        v___y_6448_,
    );
    return v___x_6450_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6451_: *mut LeanObject = *_args.add(0);
    let mut v_a_6452_: *mut LeanObject = *_args.add(1);
    let mut v_a_6453_: *mut LeanObject = *_args.add(2);
    let mut v_a_6454_: *mut LeanObject = *_args.add(3);
    let mut v_a_6455_: *mut LeanObject = *_args.add(4);
    let mut v_hints_6456_: *mut LeanObject = *_args.add(5);
    let mut v_preDefs_6457_: *mut LeanObject = *_args.add(6);
    let mut v_a_6458_: *mut LeanObject = *_args.add(7);
    let mut v_fixedArgs_6459_: *mut LeanObject = *_args.add(8);
    let mut v_as_6460_: *mut LeanObject = *_args.add(9);
    let mut v_i_6461_: *mut LeanObject = *_args.add(10);
    let mut v_j_6462_: *mut LeanObject = *_args.add(11);
    let mut v_inv_6463_: *mut LeanObject = *_args.add(12);
    let mut v_bs_6464_: *mut LeanObject = *_args.add(13);
    let mut v___y_6465_: *mut LeanObject = *_args.add(14);
    let mut v___y_6466_: *mut LeanObject = *_args.add(15);
    let mut v___y_6467_: *mut LeanObject = *_args.add(16);
    let mut v___y_6468_: *mut LeanObject = *_args.add(17);
    let mut v___y_6469_: *mut LeanObject = *_args.add(18);
    let mut v___y_6470_: *mut LeanObject = *_args.add(19);
    let mut v___y_6471_: *mut LeanObject = *_args.add(20);
    let mut v_res_6472_: *mut LeanObject = core::ptr::null_mut();
    v_res_6472_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19(
        v_a_6451_,
        v_a_6452_,
        v_a_6453_,
        v_a_6454_,
        v_a_6455_,
        v_hints_6456_,
        v_preDefs_6457_,
        v_a_6458_,
        v_fixedArgs_6459_,
        v_as_6460_,
        v_i_6461_,
        v_j_6462_,
        v_inv_6463_,
        v_bs_6464_,
        v___y_6465_,
        v___y_6466_,
        v___y_6467_,
        v___y_6468_,
        v___y_6469_,
        v___y_6470_,
    );
    lean_dec(v___y_6470_);
    lean_dec_ref(v___y_6469_);
    lean_dec(v___y_6468_);
    lean_dec_ref(v___y_6467_);
    lean_dec(v___y_6466_);
    lean_dec_ref(v___y_6465_);
    lean_dec_ref(v_as_6460_);
    lean_dec_ref(v_hints_6456_);
    lean_dec_ref(v_a_6453_);
    lean_dec_ref(v_a_6452_);
    lean_dec_ref(v_a_6451_);
    return v_res_6472_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(
    mut v___x_6473_: *mut LeanObject,
    mut v___x_6474_: *mut LeanObject,
    mut v___y_6475_: *mut LeanObject,
    mut v___x_6476_: *mut LeanObject,
    mut v_j_6477_: *mut LeanObject,
    mut v_a_6478_: *mut LeanObject,
    mut v_isZero_6479_: u8,
    mut v___x_6480_: u8,
    mut v___x_6481_: u8,
    mut v_ref_6482_: *mut LeanObject,
    mut v_kind_6483_: u8,
    mut v_levelParams_6484_: *mut LeanObject,
    mut v_modifiers_6485_: *mut LeanObject,
    mut v_declName_6486_: *mut LeanObject,
    mut v_binders_6487_: *mut LeanObject,
    mut v_numSectionVars_6488_: *mut LeanObject,
    mut v_type_6489_: *mut LeanObject,
    mut v_termination_6490_: *mut LeanObject,
    mut v_params_6491_: *mut LeanObject,
    mut v_x_6492_: *mut LeanObject,
    mut v___y_6493_: *mut LeanObject,
    mut v___y_6494_: *mut LeanObject,
    mut v___y_6495_: *mut LeanObject,
    mut v___y_6496_: *mut LeanObject,
    mut v___y_6497_: *mut LeanObject,
    mut v___y_6498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6512_: u8 = 0;
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6517_: u8 = 0;
    let mut v_a_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6521_: u8 = 0;
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6525_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6500_ =
                    l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_6473_, v_params_6491_);
                v___x_6501_ =
                    l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_6473_, v_params_6491_);
                v___x_6502_ = lean_box(0);
                v___x_6503_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(v___x_6474_, v___x_6502_);
                v___x_6504_ = l_Lean_mkConst(v___y_6475_, v___x_6503_);
                v___x_6505_ = l_Lean_mkAppN(v___x_6504_, v___x_6500_);
                lean_dec_ref(v___x_6500_);
                v___x_6506_ =
                    l_Lean_Meta_PProdN_proj(v___x_6476_, v_j_6477_, v_a_6478_, v___x_6505_);
                v___x_6507_ = l_Lean_mkAppN(v___x_6506_, v___x_6501_);
                lean_dec_ref(v___x_6501_);
                v___x_6508_ = l_Lean_Meta_mkLambdaFVars(
                    v_params_6491_,
                    v___x_6507_,
                    v_isZero_6479_,
                    v___x_6480_,
                    v___x_6480_,
                    v___x_6480_,
                    v___x_6481_,
                    v___y_6495_,
                    v___y_6496_,
                    v___y_6497_,
                    v___y_6498_,
                );
                if lean_obj_tag(v___x_6508_) == 0 {
                    v_a_6509_ = lean_ctor_get(v___x_6508_, 0);
                    v_isSharedCheck_6517_ = (!lean_is_exclusive(v___x_6508_)) as u8;
                    if v_isSharedCheck_6517_ == 0 {
                        v___x_6511_ = v___x_6508_;
                        v_isShared_6512_ = v_isSharedCheck_6517_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6509_);
                        lean_dec(v___x_6508_);
                        v___x_6511_ = lean_box(0);
                        v_isShared_6512_ = v_isSharedCheck_6517_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_termination_6490_);
                    lean_dec_ref(v_type_6489_);
                    lean_dec(v_numSectionVars_6488_);
                    lean_dec(v_binders_6487_);
                    lean_dec(v_declName_6486_);
                    lean_dec_ref(v_modifiers_6485_);
                    lean_dec(v_levelParams_6484_);
                    lean_dec(v_ref_6482_);
                    v_a_6518_ = lean_ctor_get(v___x_6508_, 0);
                    v_isSharedCheck_6525_ = (!lean_is_exclusive(v___x_6508_)) as u8;
                    if v_isSharedCheck_6525_ == 0 {
                        v___x_6520_ = v___x_6508_;
                        v_isShared_6521_ = v_isSharedCheck_6525_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6518_);
                        lean_dec(v___x_6508_);
                        v___x_6520_ = lean_box(0);
                        v_isShared_6521_ = v_isSharedCheck_6525_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6513_ = lean_alloc_ctor(0, 9, (1) as u32);
                lean_ctor_set(v___x_6513_, 0, v_ref_6482_);
                lean_ctor_set(v___x_6513_, 1, v_levelParams_6484_);
                lean_ctor_set(v___x_6513_, 2, v_modifiers_6485_);
                lean_ctor_set(v___x_6513_, 3, v_declName_6486_);
                lean_ctor_set(v___x_6513_, 4, v_binders_6487_);
                lean_ctor_set(v___x_6513_, 5, v_numSectionVars_6488_);
                lean_ctor_set(v___x_6513_, 6, v_type_6489_);
                lean_ctor_set(v___x_6513_, 7, v_a_6509_);
                lean_ctor_set(v___x_6513_, 8, v_termination_6490_);
                lean_ctor_set_uint8(
                    v___x_6513_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                    v_kind_6483_,
                );
                if v_isShared_6512_ == 0 {
                    lean_ctor_set(v___x_6511_, 0, v___x_6513_);
                    v___x_6515_ = v___x_6511_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6516_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6516_, 0, v___x_6513_);
                    v___x_6515_ = v_reuseFailAlloc_6516_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6515_;
            }
            3 => {
                if v_isShared_6521_ == 0 {
                    v___x_6523_ = v___x_6520_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6524_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6524_, 0, v_a_6518_);
                    v___x_6523_ = v_reuseFailAlloc_6524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6526_: *mut LeanObject = *_args.add(0);
    let mut v___x_6527_: *mut LeanObject = *_args.add(1);
    let mut v___y_6528_: *mut LeanObject = *_args.add(2);
    let mut v___x_6529_: *mut LeanObject = *_args.add(3);
    let mut v_j_6530_: *mut LeanObject = *_args.add(4);
    let mut v_a_6531_: *mut LeanObject = *_args.add(5);
    let mut v_isZero_6532_: *mut LeanObject = *_args.add(6);
    let mut v___x_6533_: *mut LeanObject = *_args.add(7);
    let mut v___x_6534_: *mut LeanObject = *_args.add(8);
    let mut v_ref_6535_: *mut LeanObject = *_args.add(9);
    let mut v_kind_6536_: *mut LeanObject = *_args.add(10);
    let mut v_levelParams_6537_: *mut LeanObject = *_args.add(11);
    let mut v_modifiers_6538_: *mut LeanObject = *_args.add(12);
    let mut v_declName_6539_: *mut LeanObject = *_args.add(13);
    let mut v_binders_6540_: *mut LeanObject = *_args.add(14);
    let mut v_numSectionVars_6541_: *mut LeanObject = *_args.add(15);
    let mut v_type_6542_: *mut LeanObject = *_args.add(16);
    let mut v_termination_6543_: *mut LeanObject = *_args.add(17);
    let mut v_params_6544_: *mut LeanObject = *_args.add(18);
    let mut v_x_6545_: *mut LeanObject = *_args.add(19);
    let mut v___y_6546_: *mut LeanObject = *_args.add(20);
    let mut v___y_6547_: *mut LeanObject = *_args.add(21);
    let mut v___y_6548_: *mut LeanObject = *_args.add(22);
    let mut v___y_6549_: *mut LeanObject = *_args.add(23);
    let mut v___y_6550_: *mut LeanObject = *_args.add(24);
    let mut v___y_6551_: *mut LeanObject = *_args.add(25);
    let mut v___y_6552_: *mut LeanObject = *_args.add(26);
    let mut v_isZero_boxed_6553_: u8 = 0;
    let mut v___x_56987__boxed_6554_: u8 = 0;
    let mut v___x_56988__boxed_6555_: u8 = 0;
    let mut v_kind_boxed_6556_: u8 = 0;
    let mut v_res_6557_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_6553_ = (lean_unbox(v_isZero_6532_) as u8);
    v___x_56987__boxed_6554_ = (lean_unbox(v___x_6533_) as u8);
    v___x_56988__boxed_6555_ = (lean_unbox(v___x_6534_) as u8);
    v_kind_boxed_6556_ = (lean_unbox(v_kind_6536_) as u8);
    v_res_6557_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(
            v___x_6526_,
            v___x_6527_,
            v___y_6528_,
            v___x_6529_,
            v_j_6530_,
            v_a_6531_,
            v_isZero_boxed_6553_,
            v___x_56987__boxed_6554_,
            v___x_56988__boxed_6555_,
            v_ref_6535_,
            v_kind_boxed_6556_,
            v_levelParams_6537_,
            v_modifiers_6538_,
            v_declName_6539_,
            v_binders_6540_,
            v_numSectionVars_6541_,
            v_type_6542_,
            v_termination_6543_,
            v_params_6544_,
            v_x_6545_,
            v___y_6546_,
            v___y_6547_,
            v___y_6548_,
            v___y_6549_,
            v___y_6550_,
            v___y_6551_,
        );
    lean_dec(v___y_6551_);
    lean_dec_ref(v___y_6550_);
    lean_dec(v___y_6549_);
    lean_dec_ref(v___y_6548_);
    lean_dec(v___y_6547_);
    lean_dec_ref(v___y_6546_);
    lean_dec_ref(v_x_6545_);
    lean_dec_ref(v_params_6544_);
    lean_dec(v_j_6530_);
    lean_dec(v___x_6529_);
    lean_dec_ref(v___x_6526_);
    return v_res_6557_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(
    mut v___x_6558_: *mut LeanObject,
    mut v___x_6559_: *mut LeanObject,
    mut v___y_6560_: *mut LeanObject,
    mut v___x_6561_: *mut LeanObject,
    mut v_a_6562_: *mut LeanObject,
    mut v_as_6563_: *mut LeanObject,
    mut v_i_6564_: *mut LeanObject,
    mut v_j_6565_: *mut LeanObject,
    mut v_bs_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
    mut v___y_6568_: *mut LeanObject,
    mut v___y_6569_: *mut LeanObject,
    mut v___y_6570_: *mut LeanObject,
    mut v___y_6571_: *mut LeanObject,
    mut v___y_6572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6575_: u8 = 0;
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_6579_: u8 = 0;
    let mut v_levelParams_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termination_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: u8 = 0;
    let mut v___x_6589_: u8 = 0;
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6608_: u8 = 0;
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6574_ = lean_unsigned_to_nat(0);
                v_isZero_6575_ = lean_nat_dec_eq(v_i_6564_, v_zero_6574_);
                if v_isZero_6575_ == 1 {
                    lean_dec(v_j_6565_);
                    lean_dec(v_i_6564_);
                    lean_dec_ref(v_a_6562_);
                    lean_dec(v___x_6561_);
                    lean_dec(v___y_6560_);
                    lean_dec(v___x_6559_);
                    v___x_6576_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6576_, 0, v_bs_6566_);
                    return v___x_6576_;
                } else {
                    v___x_6577_ = lean_array_fget_borrowed(v_as_6563_, v_j_6565_);
                    v_ref_6578_ = lean_ctor_get(v___x_6577_, 0);
                    v_kind_6579_ = lean_ctor_get_uint8(
                        v___x_6577_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                    );
                    v_levelParams_6580_ = lean_ctor_get(v___x_6577_, 1);
                    v_modifiers_6581_ = lean_ctor_get(v___x_6577_, 2);
                    v_declName_6582_ = lean_ctor_get(v___x_6577_, 3);
                    v_binders_6583_ = lean_ctor_get(v___x_6577_, 4);
                    v_numSectionVars_6584_ = lean_ctor_get(v___x_6577_, 5);
                    v_type_6585_ = lean_ctor_get(v___x_6577_, 6);
                    v_termination_6586_ = lean_ctor_get(v___x_6577_, 8);
                    v___x_6587_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
                    v___x_6588_ = 1;
                    v___x_6589_ = 1;
                    v___x_6590_ = lean_array_get_borrowed(v___x_6587_, v___x_6558_, v_j_6565_);
                    v___x_6591_ = lean_box((v_isZero_6575_) as usize);
                    v___x_6592_ = lean_box((v___x_6588_) as usize);
                    v___x_6593_ = lean_box((v___x_6589_) as usize);
                    v___x_6594_ = lean_box((v_kind_6579_) as usize);
                    lean_inc_ref(v_termination_6586_);
                    lean_inc_ref_n(v_type_6585_, 2);
                    lean_inc(v_numSectionVars_6584_);
                    lean_inc(v_binders_6583_);
                    lean_inc(v_declName_6582_);
                    lean_inc_ref(v_modifiers_6581_);
                    lean_inc(v_levelParams_6580_);
                    lean_inc(v_ref_6578_);
                    lean_inc_ref(v_a_6562_);
                    lean_inc(v_j_6565_);
                    lean_inc(v___x_6561_);
                    lean_inc(v___y_6560_);
                    lean_inc(v___x_6559_);
                    lean_inc(v___x_6590_);
                    v___f_6595_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed as *mut core::ffi::c_void, 27, 18);
                    lean_closure_set(v___f_6595_, 0, v___x_6590_);
                    lean_closure_set(v___f_6595_, 1, v___x_6559_);
                    lean_closure_set(v___f_6595_, 2, v___y_6560_);
                    lean_closure_set(v___f_6595_, 3, v___x_6561_);
                    lean_closure_set(v___f_6595_, 4, v_j_6565_);
                    lean_closure_set(v___f_6595_, 5, v_a_6562_);
                    lean_closure_set(v___f_6595_, 6, v___x_6591_);
                    lean_closure_set(v___f_6595_, 7, v___x_6592_);
                    lean_closure_set(v___f_6595_, 8, v___x_6593_);
                    lean_closure_set(v___f_6595_, 9, v_ref_6578_);
                    lean_closure_set(v___f_6595_, 10, v___x_6594_);
                    lean_closure_set(v___f_6595_, 11, v_levelParams_6580_);
                    lean_closure_set(v___f_6595_, 12, v_modifiers_6581_);
                    lean_closure_set(v___f_6595_, 13, v_declName_6582_);
                    lean_closure_set(v___f_6595_, 14, v_binders_6583_);
                    lean_closure_set(v___f_6595_, 15, v_numSectionVars_6584_);
                    lean_closure_set(v___f_6595_, 16, v_type_6585_);
                    lean_closure_set(v___f_6595_, 17, v_termination_6586_);
                    v___x_6596_ = lean_array_get_size(v___x_6590_);
                    v___x_6597_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6597_, 0, v___x_6596_);
                    v___x_6598_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_6585_, v___x_6597_, v___f_6595_, v_isZero_6575_, v_isZero_6575_, v___y_6567_, v___y_6568_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
                    if lean_obj_tag(v___x_6598_) == 0 {
                        v_a_6599_ = lean_ctor_get(v___x_6598_, 0);
                        lean_inc(v_a_6599_);
                        lean_dec_ref_known(v___x_6598_, 1);
                        v_one_6600_ = lean_unsigned_to_nat(1);
                        v_n_6601_ = lean_nat_sub(v_i_6564_, v_one_6600_);
                        lean_dec(v_i_6564_);
                        v___x_6602_ = lean_nat_add(v_j_6565_, v_one_6600_);
                        lean_dec(v_j_6565_);
                        v___x_6603_ = lean_array_push(v_bs_6566_, v_a_6599_);
                        v_i_6564_ = v_n_6601_;
                        v_j_6565_ = v___x_6602_;
                        v_bs_6566_ = v___x_6603_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_6566_);
                        lean_dec(v_j_6565_);
                        lean_dec(v_i_6564_);
                        lean_dec_ref(v_a_6562_);
                        lean_dec(v___x_6561_);
                        lean_dec(v___y_6560_);
                        lean_dec(v___x_6559_);
                        v_a_6605_ = lean_ctor_get(v___x_6598_, 0);
                        v_isSharedCheck_6612_ = (!lean_is_exclusive(v___x_6598_)) as u8;
                        if v_isSharedCheck_6612_ == 0 {
                            v___x_6607_ = v___x_6598_;
                            v_isShared_6608_ = v_isSharedCheck_6612_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6605_);
                            lean_dec(v___x_6598_);
                            v___x_6607_ = lean_box(0);
                            v_isShared_6608_ = v_isSharedCheck_6612_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6608_ == 0 {
                    v___x_6610_ = v___x_6607_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6611_, 0, v_a_6605_);
                    v___x_6610_ = v_reuseFailAlloc_6611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6610_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___boxed(
    mut v___x_6613_: *mut LeanObject,
    mut v___x_6614_: *mut LeanObject,
    mut v___y_6615_: *mut LeanObject,
    mut v___x_6616_: *mut LeanObject,
    mut v_a_6617_: *mut LeanObject,
    mut v_as_6618_: *mut LeanObject,
    mut v_i_6619_: *mut LeanObject,
    mut v_j_6620_: *mut LeanObject,
    mut v_bs_6621_: *mut LeanObject,
    mut v___y_6622_: *mut LeanObject,
    mut v___y_6623_: *mut LeanObject,
    mut v___y_6624_: *mut LeanObject,
    mut v___y_6625_: *mut LeanObject,
    mut v___y_6626_: *mut LeanObject,
    mut v___y_6627_: *mut LeanObject,
    mut v___y_6628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6629_: *mut LeanObject = core::ptr::null_mut();
    v_res_6629_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(
        v___x_6613_,
        v___x_6614_,
        v___y_6615_,
        v___x_6616_,
        v_a_6617_,
        v_as_6618_,
        v_i_6619_,
        v_j_6620_,
        v_bs_6621_,
        v___y_6622_,
        v___y_6623_,
        v___y_6624_,
        v___y_6625_,
        v___y_6626_,
        v___y_6627_,
    );
    lean_dec(v___y_6627_);
    lean_dec_ref(v___y_6626_);
    lean_dec(v___y_6625_);
    lean_dec_ref(v___y_6624_);
    lean_dec(v___y_6623_);
    lean_dec_ref(v___y_6622_);
    lean_dec_ref(v_as_6618_);
    lean_dec_ref(v___x_6613_);
    return v_res_6629_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(
    mut v_sz_6630_: usize,
    mut v_i_6631_: usize,
    mut v_bs_6632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6633_: u8 = 0;
    let mut v_v_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixpointType_6635_: u8 = 0;
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: usize = 0;
    let mut v___x_6639_: usize = 0;
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6633_ = lean_usize_dec_lt(v_i_6631_, v_sz_6630_);
                if v___x_6633_ == 0 {
                    return v_bs_6632_;
                } else {
                    v_v_6634_ = lean_array_uget_borrowed(v_bs_6632_, v_i_6631_);
                    v_fixpointType_6635_ = lean_ctor_get_uint8(
                        v_v_6634_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___x_6636_ = lean_unsigned_to_nat(0);
                    v_bs_x27_6637_ = lean_array_uset(v_bs_6632_, v_i_6631_, v___x_6636_);
                    v___x_6638_ = 1usize;
                    v___x_6639_ = lean_usize_add(v_i_6631_, v___x_6638_);
                    v___x_6640_ = lean_box((v_fixpointType_6635_) as usize);
                    v___x_6641_ = lean_array_uset(v_bs_x27_6637_, v_i_6631_, v___x_6640_);
                    v_i_6631_ = v___x_6639_;
                    v_bs_6632_ = v___x_6641_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___boxed(
    mut v_sz_6643_: *mut LeanObject,
    mut v_i_6644_: *mut LeanObject,
    mut v_bs_6645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6646_: usize = 0;
    let mut v_i_boxed_6647_: usize = 0;
    let mut v_res_6648_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6646_ = lean_unbox_usize(v_sz_6643_);
    lean_dec(v_sz_6643_);
    v_i_boxed_6647_ = lean_unbox_usize(v_i_6644_);
    lean_dec(v_i_6644_);
    v_res_6648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(v_sz_boxed_6646_, v_i_boxed_6647_, v_bs_6645_);
    return v_res_6648_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(
    mut v___y_6649_: *mut LeanObject,
    mut v_isExporting_6650_: u8,
    mut v___x_6651_: *mut LeanObject,
    mut v___y_6652_: *mut LeanObject,
    mut v___x_6653_: *mut LeanObject,
    mut v_a_x3f_6654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6667_: u8 = 0;
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6679_: u8 = 0;
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6686_: u8 = 0;
    let mut v_unused_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6689_: u8 = 0;
    let mut v_unused_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6656_ = lean_st_ref_take(v___y_6649_);
                v_env_6657_ = lean_ctor_get(v___x_6656_, 0);
                v_nextMacroScope_6658_ = lean_ctor_get(v___x_6656_, 1);
                v_ngen_6659_ = lean_ctor_get(v___x_6656_, 2);
                v_auxDeclNGen_6660_ = lean_ctor_get(v___x_6656_, 3);
                v_traceState_6661_ = lean_ctor_get(v___x_6656_, 4);
                v_messages_6662_ = lean_ctor_get(v___x_6656_, 6);
                v_infoState_6663_ = lean_ctor_get(v___x_6656_, 7);
                v_snapshotTasks_6664_ = lean_ctor_get(v___x_6656_, 8);
                v_isSharedCheck_6689_ = (!lean_is_exclusive(v___x_6656_)) as u8;
                if v_isSharedCheck_6689_ == 0 {
                    v_unused_6690_ = lean_ctor_get(v___x_6656_, 5);
                    lean_dec(v_unused_6690_);
                    v___x_6666_ = v___x_6656_;
                    v_isShared_6667_ = v_isSharedCheck_6689_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6664_);
                    lean_inc(v_infoState_6663_);
                    lean_inc(v_messages_6662_);
                    lean_inc(v_traceState_6661_);
                    lean_inc(v_auxDeclNGen_6660_);
                    lean_inc(v_ngen_6659_);
                    lean_inc(v_nextMacroScope_6658_);
                    lean_inc(v_env_6657_);
                    lean_dec(v___x_6656_);
                    v___x_6666_ = lean_box(0);
                    v_isShared_6667_ = v_isSharedCheck_6689_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6668_ = l_Lean_Environment_setExporting(v_env_6657_, v_isExporting_6650_);
                if v_isShared_6667_ == 0 {
                    lean_ctor_set(v___x_6666_, 5, v___x_6651_);
                    lean_ctor_set(v___x_6666_, 0, v___x_6668_);
                    v___x_6670_ = v___x_6666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6688_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6688_, 0, v___x_6668_);
                    lean_ctor_set(v_reuseFailAlloc_6688_, 1, v_nextMacroScope_6658_);
                    lean_ctor_set(v_reuseFailAlloc_6688_, 2, v_ngen_6659_);
                    lean_ctor_set(v_reuseFailAlloc_6688_, 3, v_auxDeclNGen_6660_);
                    lean_ctor_set(v_reuseFailAlloc_6688_, 4, v_traceState_6661_);
                    lean_ctor_set(v_reuseFailAlloc_6688_, 5, v___x_6651_);
                    lean_ctor_set(v_reuseFailAlloc_6688_, 6, v_messages_6662_);
                    lean_ctor_set(v_reuseFailAlloc_6688_, 7, v_infoState_6663_);
                    lean_ctor_set(v_reuseFailAlloc_6688_, 8, v_snapshotTasks_6664_);
                    v___x_6670_ = v_reuseFailAlloc_6688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6671_ = lean_st_ref_set(v___y_6649_, v___x_6670_);
                v___x_6672_ = lean_st_ref_take(v___y_6652_);
                v_mctx_6673_ = lean_ctor_get(v___x_6672_, 0);
                v_zetaDeltaFVarIds_6674_ = lean_ctor_get(v___x_6672_, 2);
                v_postponed_6675_ = lean_ctor_get(v___x_6672_, 3);
                v_diag_6676_ = lean_ctor_get(v___x_6672_, 4);
                v_isSharedCheck_6686_ = (!lean_is_exclusive(v___x_6672_)) as u8;
                if v_isSharedCheck_6686_ == 0 {
                    v_unused_6687_ = lean_ctor_get(v___x_6672_, 1);
                    lean_dec(v_unused_6687_);
                    v___x_6678_ = v___x_6672_;
                    v_isShared_6679_ = v_isSharedCheck_6686_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_6676_);
                    lean_inc(v_postponed_6675_);
                    lean_inc(v_zetaDeltaFVarIds_6674_);
                    lean_inc(v_mctx_6673_);
                    lean_dec(v___x_6672_);
                    v___x_6678_ = lean_box(0);
                    v_isShared_6679_ = v_isSharedCheck_6686_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6679_ == 0 {
                    lean_ctor_set(v___x_6678_, 1, v___x_6653_);
                    v___x_6681_ = v___x_6678_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6685_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6685_, 0, v_mctx_6673_);
                    lean_ctor_set(v_reuseFailAlloc_6685_, 1, v___x_6653_);
                    lean_ctor_set(v_reuseFailAlloc_6685_, 2, v_zetaDeltaFVarIds_6674_);
                    lean_ctor_set(v_reuseFailAlloc_6685_, 3, v_postponed_6675_);
                    lean_ctor_set(v_reuseFailAlloc_6685_, 4, v_diag_6676_);
                    v___x_6681_ = v_reuseFailAlloc_6685_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6682_ = lean_st_ref_set(v___y_6652_, v___x_6681_);
                v___x_6683_ = lean_box(0);
                v___x_6684_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6684_, 0, v___x_6683_);
                return v___x_6684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0___boxed(
    mut v___y_6691_: *mut LeanObject,
    mut v_isExporting_6692_: *mut LeanObject,
    mut v___x_6693_: *mut LeanObject,
    mut v___y_6694_: *mut LeanObject,
    mut v___x_6695_: *mut LeanObject,
    mut v_a_x3f_6696_: *mut LeanObject,
    mut v___y_6697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_6698_: u8 = 0;
    let mut v_res_6699_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_6698_ = (lean_unbox(v_isExporting_6692_) as u8);
    v_res_6699_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_6691_, v_isExporting_boxed_6698_, v___x_6693_, v___y_6694_, v___x_6695_, v_a_x3f_6696_);
    lean_dec(v_a_x3f_6696_);
    lean_dec(v___y_6694_);
    lean_dec(v___y_6691_);
    return v_res_6699_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(
    mut v_x_6700_: *mut LeanObject,
    mut v_isExporting_6701_: u8,
    mut v___y_6702_: *mut LeanObject,
    mut v___y_6703_: *mut LeanObject,
    mut v___y_6704_: *mut LeanObject,
    mut v___y_6705_: *mut LeanObject,
    mut v___y_6706_: *mut LeanObject,
    mut v___y_6707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_6711_: u8 = 0;
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6723_: u8 = 0;
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6736_: u8 = 0;
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6745_: u8 = 0;
    let mut v___x_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6751_: u8 = 0;
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6755_: u8 = 0;
    let mut v_unused_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6758_: u8 = 0;
    let mut v_a_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6764_: u8 = 0;
    let mut v___x_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6768_: u8 = 0;
    let mut v_unused_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6771_: u8 = 0;
    let mut v_unused_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6774_: u8 = 0;
    let mut v_unused_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6709_ = lean_st_ref_get(v___y_6707_);
                v_env_6710_ = lean_ctor_get(v___x_6709_, 0);
                lean_inc_ref(v_env_6710_);
                lean_dec(v___x_6709_);
                v_isExporting_6711_ = lean_ctor_get_uint8(
                    v_env_6710_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_6710_);
                v___x_6712_ = lean_st_ref_take(v___y_6707_);
                v_env_6713_ = lean_ctor_get(v___x_6712_, 0);
                v_nextMacroScope_6714_ = lean_ctor_get(v___x_6712_, 1);
                v_ngen_6715_ = lean_ctor_get(v___x_6712_, 2);
                v_auxDeclNGen_6716_ = lean_ctor_get(v___x_6712_, 3);
                v_traceState_6717_ = lean_ctor_get(v___x_6712_, 4);
                v_messages_6718_ = lean_ctor_get(v___x_6712_, 6);
                v_infoState_6719_ = lean_ctor_get(v___x_6712_, 7);
                v_snapshotTasks_6720_ = lean_ctor_get(v___x_6712_, 8);
                v_isSharedCheck_6774_ = (!lean_is_exclusive(v___x_6712_)) as u8;
                if v_isSharedCheck_6774_ == 0 {
                    v_unused_6775_ = lean_ctor_get(v___x_6712_, 5);
                    lean_dec(v_unused_6775_);
                    v___x_6722_ = v___x_6712_;
                    v_isShared_6723_ = v_isSharedCheck_6774_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6720_);
                    lean_inc(v_infoState_6719_);
                    lean_inc(v_messages_6718_);
                    lean_inc(v_traceState_6717_);
                    lean_inc(v_auxDeclNGen_6716_);
                    lean_inc(v_ngen_6715_);
                    lean_inc(v_nextMacroScope_6714_);
                    lean_inc(v_env_6713_);
                    lean_dec(v___x_6712_);
                    v___x_6722_ = lean_box(0);
                    v_isShared_6723_ = v_isSharedCheck_6774_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6724_ = l_Lean_Environment_setExporting(v_env_6713_, v_isExporting_6701_);
                v___x_6725_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
                if v_isShared_6723_ == 0 {
                    lean_ctor_set(v___x_6722_, 5, v___x_6725_);
                    lean_ctor_set(v___x_6722_, 0, v___x_6724_);
                    v___x_6727_ = v___x_6722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6773_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6773_, 0, v___x_6724_);
                    lean_ctor_set(v_reuseFailAlloc_6773_, 1, v_nextMacroScope_6714_);
                    lean_ctor_set(v_reuseFailAlloc_6773_, 2, v_ngen_6715_);
                    lean_ctor_set(v_reuseFailAlloc_6773_, 3, v_auxDeclNGen_6716_);
                    lean_ctor_set(v_reuseFailAlloc_6773_, 4, v_traceState_6717_);
                    lean_ctor_set(v_reuseFailAlloc_6773_, 5, v___x_6725_);
                    lean_ctor_set(v_reuseFailAlloc_6773_, 6, v_messages_6718_);
                    lean_ctor_set(v_reuseFailAlloc_6773_, 7, v_infoState_6719_);
                    lean_ctor_set(v_reuseFailAlloc_6773_, 8, v_snapshotTasks_6720_);
                    v___x_6727_ = v_reuseFailAlloc_6773_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6728_ = lean_st_ref_set(v___y_6707_, v___x_6727_);
                v___x_6729_ = lean_st_ref_take(v___y_6705_);
                v_mctx_6730_ = lean_ctor_get(v___x_6729_, 0);
                v_zetaDeltaFVarIds_6731_ = lean_ctor_get(v___x_6729_, 2);
                v_postponed_6732_ = lean_ctor_get(v___x_6729_, 3);
                v_diag_6733_ = lean_ctor_get(v___x_6729_, 4);
                v_isSharedCheck_6771_ = (!lean_is_exclusive(v___x_6729_)) as u8;
                if v_isSharedCheck_6771_ == 0 {
                    v_unused_6772_ = lean_ctor_get(v___x_6729_, 1);
                    lean_dec(v_unused_6772_);
                    v___x_6735_ = v___x_6729_;
                    v_isShared_6736_ = v_isSharedCheck_6771_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_6733_);
                    lean_inc(v_postponed_6732_);
                    lean_inc(v_zetaDeltaFVarIds_6731_);
                    lean_inc(v_mctx_6730_);
                    lean_dec(v___x_6729_);
                    v___x_6735_ = lean_box(0);
                    v_isShared_6736_ = v_isSharedCheck_6771_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6737_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
                if v_isShared_6736_ == 0 {
                    lean_ctor_set(v___x_6735_, 1, v___x_6737_);
                    v___x_6739_ = v___x_6735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6770_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6770_, 0, v_mctx_6730_);
                    lean_ctor_set(v_reuseFailAlloc_6770_, 1, v___x_6737_);
                    lean_ctor_set(v_reuseFailAlloc_6770_, 2, v_zetaDeltaFVarIds_6731_);
                    lean_ctor_set(v_reuseFailAlloc_6770_, 3, v_postponed_6732_);
                    lean_ctor_set(v_reuseFailAlloc_6770_, 4, v_diag_6733_);
                    v___x_6739_ = v_reuseFailAlloc_6770_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6740_ = lean_st_ref_set(v___y_6705_, v___x_6739_);
                lean_inc(v___y_6707_);
                lean_inc_ref(v___y_6706_);
                lean_inc(v___y_6705_);
                lean_inc_ref(v___y_6704_);
                lean_inc(v___y_6703_);
                lean_inc_ref(v___y_6702_);
                v_r_6741_ = lean_apply_7(
                    v_x_6700_,
                    v___y_6702_,
                    v___y_6703_,
                    v___y_6704_,
                    v___y_6705_,
                    v___y_6706_,
                    v___y_6707_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_6741_) == 0 {
                    v_a_6742_ = lean_ctor_get(v_r_6741_, 0);
                    v_isSharedCheck_6758_ = (!lean_is_exclusive(v_r_6741_)) as u8;
                    if v_isSharedCheck_6758_ == 0 {
                        v___x_6744_ = v_r_6741_;
                        v_isShared_6745_ = v_isSharedCheck_6758_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6742_);
                        lean_dec(v_r_6741_);
                        v___x_6744_ = lean_box(0);
                        v_isShared_6745_ = v_isSharedCheck_6758_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_6759_ = lean_ctor_get(v_r_6741_, 0);
                    lean_inc(v_a_6759_);
                    lean_dec_ref_known(v_r_6741_, 1);
                    v___x_6760_ = lean_box(0);
                    v___x_6761_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_6707_, v_isExporting_6711_, v___x_6725_, v___y_6705_, v___x_6737_, v___x_6760_);
                    v_isSharedCheck_6768_ = (!lean_is_exclusive(v___x_6761_)) as u8;
                    if v_isSharedCheck_6768_ == 0 {
                        v_unused_6769_ = lean_ctor_get(v___x_6761_, 0);
                        lean_dec(v_unused_6769_);
                        v___x_6763_ = v___x_6761_;
                        v_isShared_6764_ = v_isSharedCheck_6768_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_6761_);
                        v___x_6763_ = lean_box(0);
                        v_isShared_6764_ = v_isSharedCheck_6768_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_6742_);
                if v_isShared_6745_ == 0 {
                    lean_ctor_set_tag(v___x_6744_, 1);
                    v___x_6747_ = v___x_6744_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6757_, 0, v_a_6742_);
                    v___x_6747_ = v_reuseFailAlloc_6757_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6748_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_6707_, v_isExporting_6711_, v___x_6725_, v___y_6705_, v___x_6737_, v___x_6747_);
                lean_dec_ref(v___x_6747_);
                v_isSharedCheck_6755_ = (!lean_is_exclusive(v___x_6748_)) as u8;
                if v_isSharedCheck_6755_ == 0 {
                    v_unused_6756_ = lean_ctor_get(v___x_6748_, 0);
                    lean_dec(v_unused_6756_);
                    v___x_6750_ = v___x_6748_;
                    v_isShared_6751_ = v_isSharedCheck_6755_;
                    state = 7;
                    continue;
                } else {
                    lean_dec(v___x_6748_);
                    v___x_6750_ = lean_box(0);
                    v_isShared_6751_ = v_isSharedCheck_6755_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6751_ == 0 {
                    lean_ctor_set(v___x_6750_, 0, v_a_6742_);
                    v___x_6753_ = v___x_6750_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6754_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6754_, 0, v_a_6742_);
                    v___x_6753_ = v_reuseFailAlloc_6754_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6753_;
            }
            9 => {
                if v_isShared_6764_ == 0 {
                    lean_ctor_set_tag(v___x_6763_, 1);
                    lean_ctor_set(v___x_6763_, 0, v_a_6759_);
                    v___x_6766_ = v___x_6763_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6767_, 0, v_a_6759_);
                    v___x_6766_ = v_reuseFailAlloc_6767_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___boxed(
    mut v_x_6776_: *mut LeanObject,
    mut v_isExporting_6777_: *mut LeanObject,
    mut v___y_6778_: *mut LeanObject,
    mut v___y_6779_: *mut LeanObject,
    mut v___y_6780_: *mut LeanObject,
    mut v___y_6781_: *mut LeanObject,
    mut v___y_6782_: *mut LeanObject,
    mut v___y_6783_: *mut LeanObject,
    mut v___y_6784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_6785_: u8 = 0;
    let mut v_res_6786_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_6785_ = (lean_unbox(v_isExporting_6777_) as u8);
    v_res_6786_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_6776_, v_isExporting_boxed_6785_, v___y_6778_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_, v___y_6783_);
    lean_dec(v___y_6783_);
    lean_dec_ref(v___y_6782_);
    lean_dec(v___y_6781_);
    lean_dec_ref(v___y_6780_);
    lean_dec(v___y_6779_);
    lean_dec_ref(v___y_6778_);
    return v_res_6786_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(
    mut v_x_6787_: *mut LeanObject,
    mut v_when_6788_: u8,
    mut v___y_6789_: *mut LeanObject,
    mut v___y_6790_: *mut LeanObject,
    mut v___y_6791_: *mut LeanObject,
    mut v___y_6792_: *mut LeanObject,
    mut v___y_6793_: *mut LeanObject,
    mut v___y_6794_: *mut LeanObject,
) -> *mut LeanObject {
    if v_when_6788_ == 0 {
        let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_6794_);
        lean_inc_ref(v___y_6793_);
        lean_inc(v___y_6792_);
        lean_inc_ref(v___y_6791_);
        lean_inc(v___y_6790_);
        lean_inc_ref(v___y_6789_);
        v___x_6796_ = lean_apply_7(
            v_x_6787_,
            v___y_6789_,
            v___y_6790_,
            v___y_6791_,
            v___y_6792_,
            v___y_6793_,
            v___y_6794_,
            lean_box(0),
        );
        return v___x_6796_;
    } else {
        let mut v___x_6797_: u8 = 0;
        let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
        v___x_6797_ = 0;
        v___x_6798_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_6787_, v___x_6797_, v___y_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_);
        return v___x_6798_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg___boxed(
    mut v_x_6799_: *mut LeanObject,
    mut v_when_6800_: *mut LeanObject,
    mut v___y_6801_: *mut LeanObject,
    mut v___y_6802_: *mut LeanObject,
    mut v___y_6803_: *mut LeanObject,
    mut v___y_6804_: *mut LeanObject,
    mut v___y_6805_: *mut LeanObject,
    mut v___y_6806_: *mut LeanObject,
    mut v___y_6807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_6808_: u8 = 0;
    let mut v_res_6809_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_6808_ = (lean_unbox(v_when_6800_) as u8);
    v_res_6809_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(
        v_x_6799_,
        v_when_boxed_6808_,
        v___y_6801_,
        v___y_6802_,
        v___y_6803_,
        v___y_6804_,
        v___y_6805_,
        v___y_6806_,
    );
    lean_dec(v___y_6806_);
    lean_dec_ref(v___y_6805_);
    lean_dec(v___y_6804_);
    lean_dec_ref(v___y_6803_);
    lean_dec(v___y_6802_);
    lean_dec_ref(v___y_6801_);
    return v_res_6809_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(
    mut v_env_6810_: *mut LeanObject,
    mut v___y_6811_: *mut LeanObject,
    mut v___y_6812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6824_: u8 = 0;
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6836_: u8 = 0;
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6844_: u8 = 0;
    let mut v_unused_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6847_: u8 = 0;
    let mut v_unused_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6814_ = lean_st_ref_take(v___y_6812_);
                v_nextMacroScope_6815_ = lean_ctor_get(v___x_6814_, 1);
                v_ngen_6816_ = lean_ctor_get(v___x_6814_, 2);
                v_auxDeclNGen_6817_ = lean_ctor_get(v___x_6814_, 3);
                v_traceState_6818_ = lean_ctor_get(v___x_6814_, 4);
                v_messages_6819_ = lean_ctor_get(v___x_6814_, 6);
                v_infoState_6820_ = lean_ctor_get(v___x_6814_, 7);
                v_snapshotTasks_6821_ = lean_ctor_get(v___x_6814_, 8);
                v_isSharedCheck_6847_ = (!lean_is_exclusive(v___x_6814_)) as u8;
                if v_isSharedCheck_6847_ == 0 {
                    v_unused_6848_ = lean_ctor_get(v___x_6814_, 5);
                    lean_dec(v_unused_6848_);
                    v_unused_6849_ = lean_ctor_get(v___x_6814_, 0);
                    lean_dec(v_unused_6849_);
                    v___x_6823_ = v___x_6814_;
                    v_isShared_6824_ = v_isSharedCheck_6847_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6821_);
                    lean_inc(v_infoState_6820_);
                    lean_inc(v_messages_6819_);
                    lean_inc(v_traceState_6818_);
                    lean_inc(v_auxDeclNGen_6817_);
                    lean_inc(v_ngen_6816_);
                    lean_inc(v_nextMacroScope_6815_);
                    lean_dec(v___x_6814_);
                    v___x_6823_ = lean_box(0);
                    v_isShared_6824_ = v_isSharedCheck_6847_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6825_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
                if v_isShared_6824_ == 0 {
                    lean_ctor_set(v___x_6823_, 5, v___x_6825_);
                    lean_ctor_set(v___x_6823_, 0, v_env_6810_);
                    v___x_6827_ = v___x_6823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6846_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6846_, 0, v_env_6810_);
                    lean_ctor_set(v_reuseFailAlloc_6846_, 1, v_nextMacroScope_6815_);
                    lean_ctor_set(v_reuseFailAlloc_6846_, 2, v_ngen_6816_);
                    lean_ctor_set(v_reuseFailAlloc_6846_, 3, v_auxDeclNGen_6817_);
                    lean_ctor_set(v_reuseFailAlloc_6846_, 4, v_traceState_6818_);
                    lean_ctor_set(v_reuseFailAlloc_6846_, 5, v___x_6825_);
                    lean_ctor_set(v_reuseFailAlloc_6846_, 6, v_messages_6819_);
                    lean_ctor_set(v_reuseFailAlloc_6846_, 7, v_infoState_6820_);
                    lean_ctor_set(v_reuseFailAlloc_6846_, 8, v_snapshotTasks_6821_);
                    v___x_6827_ = v_reuseFailAlloc_6846_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6828_ = lean_st_ref_set(v___y_6812_, v___x_6827_);
                v___x_6829_ = lean_st_ref_take(v___y_6811_);
                v_mctx_6830_ = lean_ctor_get(v___x_6829_, 0);
                v_zetaDeltaFVarIds_6831_ = lean_ctor_get(v___x_6829_, 2);
                v_postponed_6832_ = lean_ctor_get(v___x_6829_, 3);
                v_diag_6833_ = lean_ctor_get(v___x_6829_, 4);
                v_isSharedCheck_6844_ = (!lean_is_exclusive(v___x_6829_)) as u8;
                if v_isSharedCheck_6844_ == 0 {
                    v_unused_6845_ = lean_ctor_get(v___x_6829_, 1);
                    lean_dec(v_unused_6845_);
                    v___x_6835_ = v___x_6829_;
                    v_isShared_6836_ = v_isSharedCheck_6844_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_6833_);
                    lean_inc(v_postponed_6832_);
                    lean_inc(v_zetaDeltaFVarIds_6831_);
                    lean_inc(v_mctx_6830_);
                    lean_dec(v___x_6829_);
                    v___x_6835_ = lean_box(0);
                    v_isShared_6836_ = v_isSharedCheck_6844_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6837_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
                if v_isShared_6836_ == 0 {
                    lean_ctor_set(v___x_6835_, 1, v___x_6837_);
                    v___x_6839_ = v___x_6835_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6843_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 0, v_mctx_6830_);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 1, v___x_6837_);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 2, v_zetaDeltaFVarIds_6831_);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 3, v_postponed_6832_);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 4, v_diag_6833_);
                    v___x_6839_ = v_reuseFailAlloc_6843_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6840_ = lean_st_ref_set(v___y_6811_, v___x_6839_);
                v___x_6841_ = lean_box(0);
                v___x_6842_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6842_, 0, v___x_6841_);
                return v___x_6842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg___boxed(
    mut v_env_6850_: *mut LeanObject,
    mut v___y_6851_: *mut LeanObject,
    mut v___y_6852_: *mut LeanObject,
    mut v___y_6853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6854_: *mut LeanObject = core::ptr::null_mut();
    v_res_6854_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_6850_, v___y_6851_, v___y_6852_);
    lean_dec(v___y_6852_);
    lean_dec(v___y_6851_);
    return v_res_6854_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(
    mut v_env_6855_: *mut LeanObject,
    mut v_x_6856_: *mut LeanObject,
    mut v___y_6857_: *mut LeanObject,
    mut v___y_6858_: *mut LeanObject,
    mut v___y_6859_: *mut LeanObject,
    mut v___y_6860_: *mut LeanObject,
    mut v___y_6861_: *mut LeanObject,
    mut v___y_6862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6871_: u8 = 0;
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6875_: u8 = 0;
    let mut v_unused_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6883_: u8 = 0;
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6887_: u8 = 0;
    let mut v_unused_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6864_ = lean_st_ref_get(v___y_6862_);
                v_env_6865_ = lean_ctor_get(v___x_6864_, 0);
                lean_inc_ref(v_env_6865_);
                lean_dec(v___x_6864_);
                v___x_6877_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_6855_, v___y_6860_, v___y_6862_);
                lean_dec_ref(v___x_6877_);
                lean_inc(v___y_6862_);
                lean_inc_ref(v___y_6861_);
                lean_inc(v___y_6860_);
                lean_inc_ref(v___y_6859_);
                lean_inc(v___y_6858_);
                lean_inc_ref(v___y_6857_);
                v___x_6878_ = lean_apply_7(
                    v_x_6856_,
                    v___y_6857_,
                    v___y_6858_,
                    v___y_6859_,
                    v___y_6860_,
                    v___y_6861_,
                    v___y_6862_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6878_) == 0 {
                    v_a_6879_ = lean_ctor_get(v___x_6878_, 0);
                    lean_inc(v_a_6879_);
                    lean_dec_ref_known(v___x_6878_, 1);
                    v___x_6880_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_6865_, v___y_6860_, v___y_6862_);
                    v_isSharedCheck_6887_ = (!lean_is_exclusive(v___x_6880_)) as u8;
                    if v_isSharedCheck_6887_ == 0 {
                        v_unused_6888_ = lean_ctor_get(v___x_6880_, 0);
                        lean_dec(v_unused_6888_);
                        v___x_6882_ = v___x_6880_;
                        v_isShared_6883_ = v_isSharedCheck_6887_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_6880_);
                        v___x_6882_ = lean_box(0);
                        v_isShared_6883_ = v_isSharedCheck_6887_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_6889_ = lean_ctor_get(v___x_6878_, 0);
                    lean_inc(v_a_6889_);
                    lean_dec_ref_known(v___x_6878_, 1);
                    v_a_6867_ = v_a_6889_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6868_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_6865_, v___y_6860_, v___y_6862_);
                v_isSharedCheck_6875_ = (!lean_is_exclusive(v___x_6868_)) as u8;
                if v_isSharedCheck_6875_ == 0 {
                    v_unused_6876_ = lean_ctor_get(v___x_6868_, 0);
                    lean_dec(v_unused_6876_);
                    v___x_6870_ = v___x_6868_;
                    v_isShared_6871_ = v_isSharedCheck_6875_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_6868_);
                    v___x_6870_ = lean_box(0);
                    v_isShared_6871_ = v_isSharedCheck_6875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6871_ == 0 {
                    lean_ctor_set_tag(v___x_6870_, 1);
                    lean_ctor_set(v___x_6870_, 0, v_a_6867_);
                    v___x_6873_ = v___x_6870_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6874_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6874_, 0, v_a_6867_);
                    v___x_6873_ = v_reuseFailAlloc_6874_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6873_;
            }
            4 => {
                if v_isShared_6883_ == 0 {
                    lean_ctor_set(v___x_6882_, 0, v_a_6879_);
                    v___x_6885_ = v___x_6882_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6886_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6886_, 0, v_a_6879_);
                    v___x_6885_ = v_reuseFailAlloc_6886_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6885_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg___boxed(
    mut v_env_6890_: *mut LeanObject,
    mut v_x_6891_: *mut LeanObject,
    mut v___y_6892_: *mut LeanObject,
    mut v___y_6893_: *mut LeanObject,
    mut v___y_6894_: *mut LeanObject,
    mut v___y_6895_: *mut LeanObject,
    mut v___y_6896_: *mut LeanObject,
    mut v___y_6897_: *mut LeanObject,
    mut v___y_6898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6899_: *mut LeanObject = core::ptr::null_mut();
    v_res_6899_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(
        v_env_6890_,
        v_x_6891_,
        v___y_6892_,
        v___y_6893_,
        v___y_6894_,
        v___y_6895_,
        v___y_6896_,
        v___y_6897_,
    );
    lean_dec(v___y_6897_);
    lean_dec_ref(v___y_6896_);
    lean_dec(v___y_6895_);
    lean_dec_ref(v___y_6894_);
    lean_dec(v___y_6893_);
    lean_dec_ref(v___y_6892_);
    return v_res_6899_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(
    mut v_as_6900_: *mut LeanObject,
    mut v_i_6901_: usize,
    mut v_stop_6902_: usize,
    mut v_b_6903_: *mut LeanObject,
    mut v___y_6904_: *mut LeanObject,
    mut v___y_6905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6907_: u8 = 0;
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: usize = 0;
    let mut v___x_6912_: usize = 0;
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6907_ = lean_usize_dec_eq(v_i_6901_, v_stop_6902_);
                if v___x_6907_ == 0 {
                    v___x_6908_ = lean_array_uget_borrowed(v_as_6900_, v_i_6901_);
                    v___x_6909_ =
                        l_Lean_Elab_addAsAxiom___redArg(v___x_6908_, v___y_6904_, v___y_6905_);
                    if lean_obj_tag(v___x_6909_) == 0 {
                        v_a_6910_ = lean_ctor_get(v___x_6909_, 0);
                        lean_inc(v_a_6910_);
                        lean_dec_ref_known(v___x_6909_, 1);
                        v___x_6911_ = 1usize;
                        v___x_6912_ = lean_usize_add(v_i_6901_, v___x_6911_);
                        v_i_6901_ = v___x_6912_;
                        v_b_6903_ = v_a_6910_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6909_;
                    }
                } else {
                    v___x_6914_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6914_, 0, v_b_6903_);
                    return v___x_6914_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg___boxed(
    mut v_as_6915_: *mut LeanObject,
    mut v_i_6916_: *mut LeanObject,
    mut v_stop_6917_: *mut LeanObject,
    mut v_b_6918_: *mut LeanObject,
    mut v___y_6919_: *mut LeanObject,
    mut v___y_6920_: *mut LeanObject,
    mut v___y_6921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6922_: usize = 0;
    let mut v_stop_boxed_6923_: usize = 0;
    let mut v_res_6924_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6922_ = lean_unbox_usize(v_i_6916_);
    lean_dec(v_i_6916_);
    v_stop_boxed_6923_ = lean_unbox_usize(v_stop_6917_);
    lean_dec(v_stop_6917_);
    v_res_6924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_as_6915_, v_i_boxed_6922_, v_stop_boxed_6923_, v_b_6918_, v___y_6919_, v___y_6920_);
    lean_dec(v___y_6920_);
    lean_dec_ref(v___y_6919_);
    lean_dec_ref(v_as_6915_);
    return v_res_6924_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(
    mut v___x_6925_: *mut LeanObject,
    mut v___x_6926_: *mut LeanObject,
    mut v___x_6927_: *mut LeanObject,
    mut v_a_6928_: *mut LeanObject,
    mut v_f_6929_: *mut LeanObject,
    mut v_a_6930_: *mut LeanObject,
    mut v_preDefs_6931_: *mut LeanObject,
    mut v___y_6932_: *mut LeanObject,
    mut v___y_6933_: *mut LeanObject,
    mut v___y_6934_: *mut LeanObject,
    mut v___y_6935_: *mut LeanObject,
    mut v___y_6936_: *mut LeanObject,
    mut v___y_6937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6945_: u8 = 0;
    let mut v___x_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6949_: u8 = 0;
    let mut v___x_6950_: u8 = 0;
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: u8 = 0;
    let mut v___x_6955_: u8 = 0;
    let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: usize = 0;
    let mut v___x_6958_: usize = 0;
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: usize = 0;
    let mut v___x_6961_: usize = 0;
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6950_ = lean_nat_dec_lt(v___x_6925_, v___x_6926_);
                if v___x_6950_ == 0 {
                    v___x_6951_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_6927_, v_a_6928_, v_f_6929_, v_a_6930_, v___y_6934_, v___y_6935_, v___y_6936_, v___y_6937_);
                    return v___x_6951_;
                } else {
                    v___x_6952_ = lean_box(0);
                    v___x_6953_ = lean_array_get_size(v_preDefs_6931_);
                    v___x_6954_ = lean_nat_dec_le(v___x_6926_, v___x_6953_);
                    if v___x_6954_ == 0 {
                        v___x_6955_ = lean_nat_dec_lt(v___x_6925_, v___x_6953_);
                        if v___x_6955_ == 0 {
                            v___x_6956_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_6927_, v_a_6928_, v_f_6929_, v_a_6930_, v___y_6934_, v___y_6935_, v___y_6936_, v___y_6937_);
                            return v___x_6956_;
                        } else {
                            v___x_6957_ = 0usize;
                            v___x_6958_ = lean_usize_of_nat(v___x_6953_);
                            v___x_6959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_preDefs_6931_, v___x_6957_, v___x_6958_, v___x_6952_, v___y_6936_, v___y_6937_);
                            v___y_6940_ = v___x_6959_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_6960_ = 0usize;
                        v___x_6961_ = lean_usize_of_nat(v___x_6926_);
                        v___x_6962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_preDefs_6931_, v___x_6960_, v___x_6961_, v___x_6952_, v___y_6936_, v___y_6937_);
                        v___y_6940_ = v___x_6962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_6940_) == 0 {
                    lean_dec_ref_known(v___y_6940_, 1);
                    v___x_6941_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_6927_, v_a_6928_, v_f_6929_, v_a_6930_, v___y_6934_, v___y_6935_, v___y_6936_, v___y_6937_);
                    return v___x_6941_;
                } else {
                    lean_dec_ref(v_f_6929_);
                    lean_dec_ref(v_a_6928_);
                    lean_dec_ref(v___x_6927_);
                    v_a_6942_ = lean_ctor_get(v___y_6940_, 0);
                    v_isSharedCheck_6949_ = (!lean_is_exclusive(v___y_6940_)) as u8;
                    if v_isSharedCheck_6949_ == 0 {
                        v___x_6944_ = v___y_6940_;
                        v_isShared_6945_ = v_isSharedCheck_6949_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6942_);
                        lean_dec(v___y_6940_);
                        v___x_6944_ = lean_box(0);
                        v_isShared_6945_ = v_isSharedCheck_6949_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6945_ == 0 {
                    v___x_6947_ = v___x_6944_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6948_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6948_, 0, v_a_6942_);
                    v___x_6947_ = v_reuseFailAlloc_6948_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed(
    mut v___x_6963_: *mut LeanObject,
    mut v___x_6964_: *mut LeanObject,
    mut v___x_6965_: *mut LeanObject,
    mut v_a_6966_: *mut LeanObject,
    mut v_f_6967_: *mut LeanObject,
    mut v_a_6968_: *mut LeanObject,
    mut v_preDefs_6969_: *mut LeanObject,
    mut v___y_6970_: *mut LeanObject,
    mut v___y_6971_: *mut LeanObject,
    mut v___y_6972_: *mut LeanObject,
    mut v___y_6973_: *mut LeanObject,
    mut v___y_6974_: *mut LeanObject,
    mut v___y_6975_: *mut LeanObject,
    mut v___y_6976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6977_: *mut LeanObject = core::ptr::null_mut();
    v_res_6977_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(
            v___x_6963_,
            v___x_6964_,
            v___x_6965_,
            v_a_6966_,
            v_f_6967_,
            v_a_6968_,
            v_preDefs_6969_,
            v___y_6970_,
            v___y_6971_,
            v___y_6972_,
            v___y_6973_,
            v___y_6974_,
            v___y_6975_,
        );
    lean_dec(v___y_6975_);
    lean_dec_ref(v___y_6974_);
    lean_dec(v___y_6973_);
    lean_dec_ref(v___y_6972_);
    lean_dec(v___y_6971_);
    lean_dec_ref(v___y_6970_);
    lean_dec_ref(v_preDefs_6969_);
    lean_dec_ref(v_a_6968_);
    lean_dec(v___x_6964_);
    lean_dec(v___x_6963_);
    return v_res_6977_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(
    mut v___x_6978_: *mut LeanObject,
    mut v___x_6979_: *mut LeanObject,
    mut v___x_6980_: *mut LeanObject,
    mut v_a_6981_: *mut LeanObject,
    mut v_a_6982_: *mut LeanObject,
    mut v_preDefs_6983_: *mut LeanObject,
    mut v_isZero_6984_: u8,
    mut v_f_6985_: *mut LeanObject,
    mut v___y_6986_: *mut LeanObject,
    mut v___y_6987_: *mut LeanObject,
    mut v___y_6988_: *mut LeanObject,
    mut v___y_6989_: *mut LeanObject,
    mut v___y_6990_: *mut LeanObject,
    mut v___y_6991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    v___x_6993_ = lean_st_ref_get(v___y_6991_);
    v_env_6994_ = lean_ctor_get(v___x_6993_, 0);
    lean_inc_ref(v_env_6994_);
    lean_dec(v___x_6993_);
    lean_inc_ref(v_f_6985_);
    v___f_6995_ = lean_alloc_closure(
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        14,
        7,
    );
    lean_closure_set(v___f_6995_, 0, v___x_6978_);
    lean_closure_set(v___f_6995_, 1, v___x_6979_);
    lean_closure_set(v___f_6995_, 2, v___x_6980_);
    lean_closure_set(v___f_6995_, 3, v_a_6981_);
    lean_closure_set(v___f_6995_, 4, v_f_6985_);
    lean_closure_set(v___f_6995_, 5, v_a_6982_);
    lean_closure_set(v___f_6995_, 6, v_preDefs_6983_);
    v___x_6996_ = l_Lean_Environment_unlockAsync(v_env_6994_);
    v___x_6997_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(
        v___x_6996_,
        v___f_6995_,
        v___y_6986_,
        v___y_6987_,
        v___y_6988_,
        v___y_6989_,
        v___y_6990_,
        v___y_6991_,
    );
    if lean_obj_tag(v___x_6997_) == 0 {
        let mut v_a_6998_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6999_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7002_: u8 = 0;
        let mut v___x_7003_: u8 = 0;
        let mut v___x_7004_: *mut LeanObject = core::ptr::null_mut();
        v_a_6998_ = lean_ctor_get(v___x_6997_, 0);
        lean_inc(v_a_6998_);
        lean_dec_ref_known(v___x_6997_, 1);
        v___x_6999_ = lean_unsigned_to_nat(1);
        v___x_7000_ = lean_mk_empty_array_with_capacity(v___x_6999_);
        v___x_7001_ = lean_array_push(v___x_7000_, v_f_6985_);
        v___x_7002_ = 1;
        v___x_7003_ = 1;
        v___x_7004_ = l_Lean_Meta_mkLambdaFVars(
            v___x_7001_,
            v_a_6998_,
            v_isZero_6984_,
            v___x_7002_,
            v_isZero_6984_,
            v___x_7002_,
            v___x_7003_,
            v___y_6988_,
            v___y_6989_,
            v___y_6990_,
            v___y_6991_,
        );
        lean_dec_ref(v___x_7001_);
        return v___x_7004_;
    } else {
        lean_dec_ref(v_f_6985_);
        return v___x_6997_;
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed(
    mut v___x_7005_: *mut LeanObject,
    mut v___x_7006_: *mut LeanObject,
    mut v___x_7007_: *mut LeanObject,
    mut v_a_7008_: *mut LeanObject,
    mut v_a_7009_: *mut LeanObject,
    mut v_preDefs_7010_: *mut LeanObject,
    mut v_isZero_7011_: *mut LeanObject,
    mut v_f_7012_: *mut LeanObject,
    mut v___y_7013_: *mut LeanObject,
    mut v___y_7014_: *mut LeanObject,
    mut v___y_7015_: *mut LeanObject,
    mut v___y_7016_: *mut LeanObject,
    mut v___y_7017_: *mut LeanObject,
    mut v___y_7018_: *mut LeanObject,
    mut v___y_7019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_7020_: u8 = 0;
    let mut v_res_7021_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_7020_ = (lean_unbox(v_isZero_7011_) as u8);
    v_res_7021_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(
            v___x_7005_,
            v___x_7006_,
            v___x_7007_,
            v_a_7008_,
            v_a_7009_,
            v_preDefs_7010_,
            v_isZero_boxed_7020_,
            v_f_7012_,
            v___y_7013_,
            v___y_7014_,
            v___y_7015_,
            v___y_7016_,
            v___y_7017_,
            v___y_7018_,
        );
    lean_dec(v___y_7018_);
    lean_dec_ref(v___y_7017_);
    lean_dec(v___y_7016_);
    lean_dec_ref(v___y_7015_);
    lean_dec(v___y_7014_);
    lean_dec_ref(v___y_7013_);
    return v_res_7021_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(
    mut v_k_7022_: *mut LeanObject,
    mut v___y_7023_: *mut LeanObject,
    mut v___y_7024_: *mut LeanObject,
    mut v_b_7025_: *mut LeanObject,
    mut v___y_7026_: *mut LeanObject,
    mut v___y_7027_: *mut LeanObject,
    mut v___y_7028_: *mut LeanObject,
    mut v___y_7029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_7029_);
    lean_inc_ref(v___y_7028_);
    lean_inc(v___y_7027_);
    lean_inc_ref(v___y_7026_);
    lean_inc(v___y_7024_);
    lean_inc_ref(v___y_7023_);
    v___x_7031_ = lean_apply_8(
        v_k_7022_,
        v_b_7025_,
        v___y_7023_,
        v___y_7024_,
        v___y_7026_,
        v___y_7027_,
        v___y_7028_,
        v___y_7029_,
        lean_box(0),
    );
    return v___x_7031_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed(
    mut v_k_7032_: *mut LeanObject,
    mut v___y_7033_: *mut LeanObject,
    mut v___y_7034_: *mut LeanObject,
    mut v_b_7035_: *mut LeanObject,
    mut v___y_7036_: *mut LeanObject,
    mut v___y_7037_: *mut LeanObject,
    mut v___y_7038_: *mut LeanObject,
    mut v___y_7039_: *mut LeanObject,
    mut v___y_7040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7041_: *mut LeanObject = core::ptr::null_mut();
    v_res_7041_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(v_k_7032_, v___y_7033_, v___y_7034_, v_b_7035_, v___y_7036_, v___y_7037_, v___y_7038_, v___y_7039_);
    lean_dec(v___y_7039_);
    lean_dec_ref(v___y_7038_);
    lean_dec(v___y_7037_);
    lean_dec_ref(v___y_7036_);
    lean_dec(v___y_7034_);
    lean_dec_ref(v___y_7033_);
    return v_res_7041_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(
    mut v_name_7042_: *mut LeanObject,
    mut v_bi_7043_: u8,
    mut v_type_7044_: *mut LeanObject,
    mut v_k_7045_: *mut LeanObject,
    mut v_kind_7046_: u8,
    mut v___y_7047_: *mut LeanObject,
    mut v___y_7048_: *mut LeanObject,
    mut v___y_7049_: *mut LeanObject,
    mut v___y_7050_: *mut LeanObject,
    mut v___y_7051_: *mut LeanObject,
    mut v___y_7052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7059_: u8 = 0;
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_7048_);
                lean_inc_ref(v___y_7047_);
                v___f_7054_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                lean_closure_set(v___f_7054_, 0, v_k_7045_);
                lean_closure_set(v___f_7054_, 1, v___y_7047_);
                lean_closure_set(v___f_7054_, 2, v___y_7048_);
                v___x_7055_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_7042_,
                    v_bi_7043_,
                    v_type_7044_,
                    v___f_7054_,
                    v_kind_7046_,
                    v___y_7049_,
                    v___y_7050_,
                    v___y_7051_,
                    v___y_7052_,
                );
                if lean_obj_tag(v___x_7055_) == 0 {
                    return v___x_7055_;
                } else {
                    v_a_7056_ = lean_ctor_get(v___x_7055_, 0);
                    v_isSharedCheck_7063_ = (!lean_is_exclusive(v___x_7055_)) as u8;
                    if v_isSharedCheck_7063_ == 0 {
                        v___x_7058_ = v___x_7055_;
                        v_isShared_7059_ = v_isSharedCheck_7063_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7056_);
                        lean_dec(v___x_7055_);
                        v___x_7058_ = lean_box(0);
                        v_isShared_7059_ = v_isSharedCheck_7063_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7059_ == 0 {
                    v___x_7061_ = v___x_7058_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7062_, 0, v_a_7056_);
                    v___x_7061_ = v_reuseFailAlloc_7062_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___boxed(
    mut v_name_7064_: *mut LeanObject,
    mut v_bi_7065_: *mut LeanObject,
    mut v_type_7066_: *mut LeanObject,
    mut v_k_7067_: *mut LeanObject,
    mut v_kind_7068_: *mut LeanObject,
    mut v___y_7069_: *mut LeanObject,
    mut v___y_7070_: *mut LeanObject,
    mut v___y_7071_: *mut LeanObject,
    mut v___y_7072_: *mut LeanObject,
    mut v___y_7073_: *mut LeanObject,
    mut v___y_7074_: *mut LeanObject,
    mut v___y_7075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_7076_: u8 = 0;
    let mut v_kind_boxed_7077_: u8 = 0;
    let mut v_res_7078_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_7076_ = (lean_unbox(v_bi_7065_) as u8);
    v_kind_boxed_7077_ = (lean_unbox(v_kind_7068_) as u8);
    v_res_7078_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_7064_, v_bi_boxed_7076_, v_type_7066_, v_k_7067_, v_kind_boxed_7077_, v___y_7069_, v___y_7070_, v___y_7071_, v___y_7072_, v___y_7073_, v___y_7074_);
    lean_dec(v___y_7074_);
    lean_dec_ref(v___y_7073_);
    lean_dec(v___y_7072_);
    lean_dec_ref(v___y_7071_);
    lean_dec(v___y_7070_);
    lean_dec_ref(v___y_7069_);
    return v_res_7078_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(
    mut v_name_7079_: *mut LeanObject,
    mut v_type_7080_: *mut LeanObject,
    mut v_k_7081_: *mut LeanObject,
    mut v___y_7082_: *mut LeanObject,
    mut v___y_7083_: *mut LeanObject,
    mut v___y_7084_: *mut LeanObject,
    mut v___y_7085_: *mut LeanObject,
    mut v___y_7086_: *mut LeanObject,
    mut v___y_7087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7089_: u8 = 0;
    let mut v___x_7090_: u8 = 0;
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    v___x_7089_ = 0;
    v___x_7090_ = 0;
    v___x_7091_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_7079_, v___x_7089_, v_type_7080_, v_k_7081_, v___x_7090_, v___y_7082_, v___y_7083_, v___y_7084_, v___y_7085_, v___y_7086_, v___y_7087_);
    return v___x_7091_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg___boxed(
    mut v_name_7092_: *mut LeanObject,
    mut v_type_7093_: *mut LeanObject,
    mut v_k_7094_: *mut LeanObject,
    mut v___y_7095_: *mut LeanObject,
    mut v___y_7096_: *mut LeanObject,
    mut v___y_7097_: *mut LeanObject,
    mut v___y_7098_: *mut LeanObject,
    mut v___y_7099_: *mut LeanObject,
    mut v___y_7100_: *mut LeanObject,
    mut v___y_7101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7102_: *mut LeanObject = core::ptr::null_mut();
    v_res_7102_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(
        v_name_7092_,
        v_type_7093_,
        v_k_7094_,
        v___y_7095_,
        v___y_7096_,
        v___y_7097_,
        v___y_7098_,
        v___y_7099_,
        v___y_7100_,
    );
    lean_dec(v___y_7100_);
    lean_dec_ref(v___y_7099_);
    lean_dec(v___y_7098_);
    lean_dec_ref(v___y_7097_);
    lean_dec(v___y_7096_);
    lean_dec_ref(v___y_7095_);
    return v_res_7102_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(
    mut v___x_7106_: *mut LeanObject,
    mut v_fixedArgs_7107_: *mut LeanObject,
    mut v___x_7108_: *mut LeanObject,
    mut v_a_7109_: *mut LeanObject,
    mut v___x_7110_: *mut LeanObject,
    mut v_preDefs_7111_: *mut LeanObject,
    mut v_a_7112_: *mut LeanObject,
    mut v_as_7113_: *mut LeanObject,
    mut v_i_7114_: *mut LeanObject,
    mut v_j_7115_: *mut LeanObject,
    mut v_bs_7116_: *mut LeanObject,
    mut v___y_7117_: *mut LeanObject,
    mut v___y_7118_: *mut LeanObject,
    mut v___y_7119_: *mut LeanObject,
    mut v___y_7120_: *mut LeanObject,
    mut v___y_7121_: *mut LeanObject,
    mut v___y_7122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7125_: u8 = 0;
    let mut v___x_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7141_: u8 = 0;
    let mut v___x_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7145_: u8 = 0;
    let mut v___x_7146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7158_: u8 = 0;
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7124_ = lean_unsigned_to_nat(0);
                v_isZero_7125_ = lean_nat_dec_eq(v_i_7114_, v_zero_7124_);
                if v_isZero_7125_ == 1 {
                    lean_dec(v_j_7115_);
                    lean_dec(v_i_7114_);
                    lean_dec_ref(v_a_7112_);
                    lean_dec_ref(v_preDefs_7111_);
                    lean_dec(v___x_7110_);
                    lean_dec_ref(v_a_7109_);
                    lean_dec_ref(v___x_7108_);
                    lean_dec_ref(v_fixedArgs_7107_);
                    v___x_7126_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7126_, 0, v_bs_7116_);
                    return v___x_7126_;
                } else {
                    v___x_7127_ = lean_array_fget_borrowed(v_as_7113_, v_j_7115_);
                    v_value_7128_ = lean_ctor_get(v___x_7127_, 7);
                    v___x_7129_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
                    v_one_7130_ = lean_unsigned_to_nat(1);
                    v_n_7131_ = lean_nat_sub(v_i_7114_, v_one_7130_);
                    lean_dec(v_i_7114_);
                    v___x_7146_ = lean_array_get_borrowed(v___x_7129_, v___x_7106_, v_j_7115_);
                    lean_inc_ref(v_fixedArgs_7107_);
                    lean_inc_ref(v_value_7128_);
                    lean_inc(v___x_7146_);
                    v___x_7147_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(
                        v___x_7146_,
                        v_value_7128_,
                        v_fixedArgs_7107_,
                        v___y_7119_,
                        v___y_7120_,
                        v___y_7121_,
                        v___y_7122_,
                    );
                    if lean_obj_tag(v___x_7147_) == 0 {
                        v_a_7148_ = lean_ctor_get(v___x_7147_, 0);
                        lean_inc(v_a_7148_);
                        lean_dec_ref_known(v___x_7147_, 1);
                        v___x_7149_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1;
                        v___x_7150_ =
                            l_Lean_Core_mkFreshUserName(v___x_7149_, v___y_7121_, v___y_7122_);
                        if lean_obj_tag(v___x_7150_) == 0 {
                            v_a_7151_ = lean_ctor_get(v___x_7150_, 0);
                            lean_inc(v_a_7151_);
                            lean_dec_ref_known(v___x_7150_, 1);
                            v___x_7152_ = lean_box((v_isZero_7125_) as usize);
                            lean_inc_ref(v_preDefs_7111_);
                            lean_inc_ref(v_a_7109_);
                            lean_inc_ref(v___x_7108_);
                            lean_inc(v___x_7110_);
                            v___f_7153_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed as *mut core::ffi::c_void, 15, 7);
                            lean_closure_set(v___f_7153_, 0, v_zero_7124_);
                            lean_closure_set(v___f_7153_, 1, v___x_7110_);
                            lean_closure_set(v___f_7153_, 2, v___x_7108_);
                            lean_closure_set(v___f_7153_, 3, v_a_7109_);
                            lean_closure_set(v___f_7153_, 4, v_a_7148_);
                            lean_closure_set(v___f_7153_, 5, v_preDefs_7111_);
                            lean_closure_set(v___f_7153_, 6, v___x_7152_);
                            lean_inc_ref(v_a_7112_);
                            v___x_7154_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_a_7151_, v_a_7112_, v___f_7153_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
                            v___y_7133_ = v___x_7154_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_7148_);
                            lean_dec(v_n_7131_);
                            lean_dec_ref(v_bs_7116_);
                            lean_dec(v_j_7115_);
                            lean_dec_ref(v_a_7112_);
                            lean_dec_ref(v_preDefs_7111_);
                            lean_dec(v___x_7110_);
                            lean_dec_ref(v_a_7109_);
                            lean_dec_ref(v___x_7108_);
                            lean_dec_ref(v_fixedArgs_7107_);
                            v_a_7155_ = lean_ctor_get(v___x_7150_, 0);
                            v_isSharedCheck_7162_ = (!lean_is_exclusive(v___x_7150_)) as u8;
                            if v_isSharedCheck_7162_ == 0 {
                                v___x_7157_ = v___x_7150_;
                                v_isShared_7158_ = v_isSharedCheck_7162_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_7155_);
                                lean_dec(v___x_7150_);
                                v___x_7157_ = lean_box(0);
                                v_isShared_7158_ = v_isSharedCheck_7162_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___y_7133_ = v___x_7147_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_7133_) == 0 {
                    v_a_7134_ = lean_ctor_get(v___y_7133_, 0);
                    lean_inc(v_a_7134_);
                    lean_dec_ref_known(v___y_7133_, 1);
                    v___x_7135_ = lean_nat_add(v_j_7115_, v_one_7130_);
                    lean_dec(v_j_7115_);
                    v___x_7136_ = lean_array_push(v_bs_7116_, v_a_7134_);
                    v_i_7114_ = v_n_7131_;
                    v_j_7115_ = v___x_7135_;
                    v_bs_7116_ = v___x_7136_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_n_7131_);
                    lean_dec_ref(v_bs_7116_);
                    lean_dec(v_j_7115_);
                    lean_dec_ref(v_a_7112_);
                    lean_dec_ref(v_preDefs_7111_);
                    lean_dec(v___x_7110_);
                    lean_dec_ref(v_a_7109_);
                    lean_dec_ref(v___x_7108_);
                    lean_dec_ref(v_fixedArgs_7107_);
                    v_a_7138_ = lean_ctor_get(v___y_7133_, 0);
                    v_isSharedCheck_7145_ = (!lean_is_exclusive(v___y_7133_)) as u8;
                    if v_isSharedCheck_7145_ == 0 {
                        v___x_7140_ = v___y_7133_;
                        v_isShared_7141_ = v_isSharedCheck_7145_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7138_);
                        lean_dec(v___y_7133_);
                        v___x_7140_ = lean_box(0);
                        v_isShared_7141_ = v_isSharedCheck_7145_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7141_ == 0 {
                    v___x_7143_ = v___x_7140_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7144_, 0, v_a_7138_);
                    v___x_7143_ = v_reuseFailAlloc_7144_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7143_;
            }
            4 => {
                if v_isShared_7158_ == 0 {
                    v___x_7160_ = v___x_7157_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7161_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7161_, 0, v_a_7155_);
                    v___x_7160_ = v_reuseFailAlloc_7161_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7163_: *mut LeanObject = *_args.add(0);
    let mut v_fixedArgs_7164_: *mut LeanObject = *_args.add(1);
    let mut v___x_7165_: *mut LeanObject = *_args.add(2);
    let mut v_a_7166_: *mut LeanObject = *_args.add(3);
    let mut v___x_7167_: *mut LeanObject = *_args.add(4);
    let mut v_preDefs_7168_: *mut LeanObject = *_args.add(5);
    let mut v_a_7169_: *mut LeanObject = *_args.add(6);
    let mut v_as_7170_: *mut LeanObject = *_args.add(7);
    let mut v_i_7171_: *mut LeanObject = *_args.add(8);
    let mut v_j_7172_: *mut LeanObject = *_args.add(9);
    let mut v_bs_7173_: *mut LeanObject = *_args.add(10);
    let mut v___y_7174_: *mut LeanObject = *_args.add(11);
    let mut v___y_7175_: *mut LeanObject = *_args.add(12);
    let mut v___y_7176_: *mut LeanObject = *_args.add(13);
    let mut v___y_7177_: *mut LeanObject = *_args.add(14);
    let mut v___y_7178_: *mut LeanObject = *_args.add(15);
    let mut v___y_7179_: *mut LeanObject = *_args.add(16);
    let mut v___y_7180_: *mut LeanObject = *_args.add(17);
    let mut v_res_7181_: *mut LeanObject = core::ptr::null_mut();
    v_res_7181_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(
        v___x_7163_,
        v_fixedArgs_7164_,
        v___x_7165_,
        v_a_7166_,
        v___x_7167_,
        v_preDefs_7168_,
        v_a_7169_,
        v_as_7170_,
        v_i_7171_,
        v_j_7172_,
        v_bs_7173_,
        v___y_7174_,
        v___y_7175_,
        v___y_7176_,
        v___y_7177_,
        v___y_7178_,
        v___y_7179_,
    );
    lean_dec(v___y_7179_);
    lean_dec_ref(v___y_7178_);
    lean_dec(v___y_7177_);
    lean_dec_ref(v___y_7176_);
    lean_dec(v___y_7175_);
    lean_dec_ref(v___y_7174_);
    lean_dec_ref(v_as_7170_);
    lean_dec_ref(v___x_7163_);
    return v_res_7181_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16(
    mut v___x_7182_: *mut LeanObject,
    mut v_fixedArgs_7183_: *mut LeanObject,
    mut v___x_7184_: *mut LeanObject,
    mut v_a_7185_: *mut LeanObject,
    mut v___x_7186_: *mut LeanObject,
    mut v_preDefs_7187_: *mut LeanObject,
    mut v_a_7188_: *mut LeanObject,
    mut v_as_7189_: *mut LeanObject,
    mut v_i_7190_: *mut LeanObject,
    mut v_j_7191_: *mut LeanObject,
    mut v_inv_7192_: *mut LeanObject,
    mut v_bs_7193_: *mut LeanObject,
    mut v___y_7194_: *mut LeanObject,
    mut v___y_7195_: *mut LeanObject,
    mut v___y_7196_: *mut LeanObject,
    mut v___y_7197_: *mut LeanObject,
    mut v___y_7198_: *mut LeanObject,
    mut v___y_7199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7201_: *mut LeanObject = core::ptr::null_mut();
    v___x_7201_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(
        v___x_7182_,
        v_fixedArgs_7183_,
        v___x_7184_,
        v_a_7185_,
        v___x_7186_,
        v_preDefs_7187_,
        v_a_7188_,
        v_as_7189_,
        v_i_7190_,
        v_j_7191_,
        v_bs_7193_,
        v___y_7194_,
        v___y_7195_,
        v___y_7196_,
        v___y_7197_,
        v___y_7198_,
        v___y_7199_,
    );
    return v___x_7201_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7202_: *mut LeanObject = *_args.add(0);
    let mut v_fixedArgs_7203_: *mut LeanObject = *_args.add(1);
    let mut v___x_7204_: *mut LeanObject = *_args.add(2);
    let mut v_a_7205_: *mut LeanObject = *_args.add(3);
    let mut v___x_7206_: *mut LeanObject = *_args.add(4);
    let mut v_preDefs_7207_: *mut LeanObject = *_args.add(5);
    let mut v_a_7208_: *mut LeanObject = *_args.add(6);
    let mut v_as_7209_: *mut LeanObject = *_args.add(7);
    let mut v_i_7210_: *mut LeanObject = *_args.add(8);
    let mut v_j_7211_: *mut LeanObject = *_args.add(9);
    let mut v_inv_7212_: *mut LeanObject = *_args.add(10);
    let mut v_bs_7213_: *mut LeanObject = *_args.add(11);
    let mut v___y_7214_: *mut LeanObject = *_args.add(12);
    let mut v___y_7215_: *mut LeanObject = *_args.add(13);
    let mut v___y_7216_: *mut LeanObject = *_args.add(14);
    let mut v___y_7217_: *mut LeanObject = *_args.add(15);
    let mut v___y_7218_: *mut LeanObject = *_args.add(16);
    let mut v___y_7219_: *mut LeanObject = *_args.add(17);
    let mut v___y_7220_: *mut LeanObject = *_args.add(18);
    let mut v_res_7221_: *mut LeanObject = core::ptr::null_mut();
    v_res_7221_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16(
        v___x_7202_,
        v_fixedArgs_7203_,
        v___x_7204_,
        v_a_7205_,
        v___x_7206_,
        v_preDefs_7207_,
        v_a_7208_,
        v_as_7209_,
        v_i_7210_,
        v_j_7211_,
        v_inv_7212_,
        v_bs_7213_,
        v___y_7214_,
        v___y_7215_,
        v___y_7216_,
        v___y_7217_,
        v___y_7218_,
        v___y_7219_,
    );
    lean_dec(v___y_7219_);
    lean_dec_ref(v___y_7218_);
    lean_dec(v___y_7217_);
    lean_dec_ref(v___y_7216_);
    lean_dec(v___y_7215_);
    lean_dec_ref(v___y_7214_);
    lean_dec_ref(v_as_7209_);
    lean_dec_ref(v___x_7202_);
    return v_res_7221_;
}
pub unsafe fn _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut LeanObject = core::ptr::null_mut();
    v___x_7222_ = l_Lean_instInhabitedExpr;
    v___x_7223_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7223_, 0, v___x_7222_);
    lean_ctor_set(v___x_7223_, 1, v___x_7222_);
    return v___x_7223_;
}
pub unsafe fn _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut LeanObject = core::ptr::null_mut();
    v___x_7229_ = l_Lean_Elab_partialFixpoint___lam__0___closed__4;
    v___x_7230_ = l_Lean_stringToMessageData(v___x_7229_);
    return v___x_7230_;
}
pub unsafe fn l_Lean_Elab_partialFixpoint___lam__0(
    mut v_a_7231_: *mut LeanObject,
    mut v_perms_7232_: *mut LeanObject,
    mut v___x_7233_: *mut LeanObject,
    mut v_preDefs_7234_: *mut LeanObject,
    mut v___x_7235_: *mut LeanObject,
    mut v___x_7236_: *mut LeanObject,
    mut v___x_7237_: usize,
    mut v___x_7238_: *mut LeanObject,
    mut v_a_7239_: *mut LeanObject,
    mut v___x_7240_: u8,
    mut v_hints_7241_: *mut LeanObject,
    mut v___x_7242_: *mut LeanObject,
    mut v_docCtx_7243_: *mut LeanObject,
    mut v_sz_7244_: usize,
    mut v_fixedArgs_7245_: *mut LeanObject,
    mut v___y_7246_: *mut LeanObject,
    mut v___y_7247_: *mut LeanObject,
    mut v___y_7248_: *mut LeanObject,
    mut v___y_7249_: *mut LeanObject,
    mut v___y_7250_: *mut LeanObject,
    mut v___y_7251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7262_: usize = 0;
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7284_: u8 = 0;
    let mut v___x_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: u8 = 0;
    let mut v___x_7296_: u8 = 0;
    let mut v___x_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_7302_: u8 = 0;
    let mut v_levelParams_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termination_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7310_: u8 = 0;
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7319_: usize = 0;
    let mut v___x_7320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7326_: u8 = 0;
    let mut v___x_7328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7330_: u8 = 0;
    let mut v_reuseFailAlloc_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7335_: u8 = 0;
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7339_: u8 = 0;
    let mut v_isSharedCheck_7340_: u8 = 0;
    let mut v_unused_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7347_: u8 = 0;
    let mut v___x_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7351_: u8 = 0;
    let mut v_a_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7355_: u8 = 0;
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7359_: u8 = 0;
    let mut v___y_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7367_: u8 = 0;
    let mut v_declName_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: u8 = 0;
    let mut v___x_7381_: u8 = 0;
    let mut v_options_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7383_: u8 = 0;
    let mut v_inheritedTraceOptions_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: u8 = 0;
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7397_: u8 = 0;
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7401_: u8 = 0;
    let mut v_isSharedCheck_7402_: u8 = 0;
    let mut v_unused_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7407_: u8 = 0;
    let mut v___x_7409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7411_: u8 = 0;
    let mut v_a_7412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7415_: u8 = 0;
    let mut v___x_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7419_: u8 = 0;
    let mut v_a_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7423_: u8 = 0;
    let mut v___x_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7427_: u8 = 0;
    let mut v_a_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7431_: u8 = 0;
    let mut v___x_7433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7435_: u8 = 0;
    let mut v_a_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7439_: u8 = 0;
    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7443_: u8 = 0;
    let mut v_a_7444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7447_: u8 = 0;
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7451_: u8 = 0;
    let mut v_a_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7455_: u8 = 0;
    let mut v___x_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7459_: u8 = 0;
    let mut v_a_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7463_: u8 = 0;
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7467_: u8 = 0;
    let mut v_a_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7471_: u8 = 0;
    let mut v___x_7473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7253_ = lean_array_get_size(v_a_7231_);
                v___x_7254_ = lean_mk_empty_array_with_capacity(v___x_7253_);
                lean_inc(v___x_7233_);
                lean_inc_ref(v_fixedArgs_7245_);
                v___x_7255_ =
                    l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(
                        v_perms_7232_,
                        v_fixedArgs_7245_,
                        v_a_7231_,
                        v___x_7253_,
                        v___x_7233_,
                        v___x_7254_,
                        v___y_7248_,
                        v___y_7249_,
                        v___y_7250_,
                        v___y_7251_,
                    );
                if lean_obj_tag(v___x_7255_) == 0 {
                    v_a_7256_ = lean_ctor_get(v___x_7255_, 0);
                    lean_inc(v_a_7256_);
                    lean_dec_ref_known(v___x_7255_, 1);
                    lean_inc_ref(v___x_7236_);
                    lean_inc(v___x_7233_);
                    lean_inc(v___x_7235_);
                    lean_inc_ref(v_fixedArgs_7245_);
                    v___x_7257_ =
                        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(
                            v_perms_7232_,
                            v_fixedArgs_7245_,
                            v_preDefs_7234_,
                            v___x_7235_,
                            v___x_7233_,
                            v___x_7236_,
                            v___y_7248_,
                            v___y_7249_,
                            v___y_7250_,
                            v___y_7251_,
                        );
                    if lean_obj_tag(v___x_7257_) == 0 {
                        v_a_7258_ = lean_ctor_get(v___x_7257_, 0);
                        lean_inc_n(v_a_7258_, 2);
                        lean_dec_ref_known(v___x_7257_, 1);
                        v___x_7259_ = l_Lean_Level_ofNat(v___x_7233_);
                        v___x_7260_ = l_Lean_Meta_PProdN_pack(
                            v___x_7259_,
                            v_a_7258_,
                            v___y_7248_,
                            v___y_7249_,
                            v___y_7250_,
                            v___y_7251_,
                        );
                        if lean_obj_tag(v___x_7260_) == 0 {
                            v_a_7261_ = lean_ctor_get(v___x_7260_, 0);
                            lean_inc(v_a_7261_);
                            lean_dec_ref_known(v___x_7260_, 1);
                            v_sz_7262_ = lean_array_size(v_a_7256_);
                            v___x_7263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(v_sz_7262_, v___x_7237_, v_a_7256_, v___y_7246_, v___y_7247_, v___y_7248_, v___y_7249_, v___y_7250_, v___y_7251_);
                            if lean_obj_tag(v___x_7263_) == 0 {
                                v_a_7264_ = lean_ctor_get(v___x_7263_, 0);
                                lean_inc_n(v_a_7264_, 2);
                                lean_dec_ref_known(v___x_7263_, 1);
                                v___x_7265_ = l_Lean_Meta_mkPackedPPRodInstance(
                                    v_a_7264_,
                                    v___y_7248_,
                                    v___y_7249_,
                                    v___y_7250_,
                                    v___y_7251_,
                                );
                                if lean_obj_tag(v___x_7265_) == 0 {
                                    v_a_7266_ = lean_ctor_get(v___x_7265_, 0);
                                    lean_inc_n(v_a_7266_, 2);
                                    lean_dec_ref_known(v___x_7265_, 1);
                                    v___x_7267_ = lean_box(0);
                                    v___x_7268_ = l_Lean_Meta_toPartialOrder(
                                        v_a_7266_,
                                        v___x_7267_,
                                        v___y_7248_,
                                        v___y_7249_,
                                        v___y_7250_,
                                        v___y_7251_,
                                    );
                                    if lean_obj_tag(v___x_7268_) == 0 {
                                        v_a_7269_ = lean_ctor_get(v___x_7268_, 0);
                                        lean_inc(v_a_7269_);
                                        lean_dec_ref_known(v___x_7268_, 1);
                                        lean_inc(v___x_7233_);
                                        lean_inc(v_a_7261_);
                                        lean_inc_ref_n(v_preDefs_7234_, 2);
                                        lean_inc_n(v___x_7235_, 2);
                                        lean_inc_ref(v_a_7239_);
                                        lean_inc_ref(v_fixedArgs_7245_);
                                        lean_inc_ref(v_perms_7232_);
                                        v___x_7270_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed as *mut core::ffi::c_void, 19, 12);
                                        lean_closure_set(v___x_7270_, 0, v_perms_7232_);
                                        lean_closure_set(v___x_7270_, 1, v_fixedArgs_7245_);
                                        lean_closure_set(v___x_7270_, 2, v___x_7238_);
                                        lean_closure_set(v___x_7270_, 3, v_a_7239_);
                                        lean_closure_set(v___x_7270_, 4, v___x_7235_);
                                        lean_closure_set(v___x_7270_, 5, v_preDefs_7234_);
                                        lean_closure_set(v___x_7270_, 6, v_a_7261_);
                                        lean_closure_set(v___x_7270_, 7, v_preDefs_7234_);
                                        lean_closure_set(v___x_7270_, 8, v___x_7235_);
                                        lean_closure_set(v___x_7270_, 9, v___x_7233_);
                                        lean_closure_set(v___x_7270_, 10, lean_box(0));
                                        lean_closure_set(v___x_7270_, 11, v___x_7236_);
                                        v___x_7271_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_7270_, v___x_7240_, v___y_7246_, v___y_7247_, v___y_7248_, v___y_7249_, v___y_7250_, v___y_7251_);
                                        if lean_obj_tag(v___x_7271_) == 0 {
                                            v_a_7272_ = lean_ctor_get(v___x_7271_, 0);
                                            lean_inc(v_a_7272_);
                                            lean_dec_ref_known(v___x_7271_, 1);
                                            v___x_7273_ =
                                                lean_mk_empty_array_with_capacity(v___x_7235_);
                                            lean_inc_ref(v___x_7273_);
                                            lean_inc(v___x_7233_);
                                            lean_inc(v___x_7235_);
                                            lean_inc_ref(v_fixedArgs_7245_);
                                            lean_inc_ref(v_a_7239_);
                                            lean_inc_ref_n(v_preDefs_7234_, 2);
                                            lean_inc_ref(v_hints_7241_);
                                            lean_inc(v_a_7261_);
                                            v___x_7274_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed as *mut core::ffi::c_void, 21, 14);
                                            lean_closure_set(v___x_7274_, 0, v_a_7258_);
                                            lean_closure_set(v___x_7274_, 1, v_a_7264_);
                                            lean_closure_set(v___x_7274_, 2, v_a_7272_);
                                            lean_closure_set(v___x_7274_, 3, v_a_7261_);
                                            lean_closure_set(v___x_7274_, 4, v_a_7269_);
                                            lean_closure_set(v___x_7274_, 5, v_hints_7241_);
                                            lean_closure_set(v___x_7274_, 6, v_preDefs_7234_);
                                            lean_closure_set(v___x_7274_, 7, v_a_7239_);
                                            lean_closure_set(v___x_7274_, 8, v_fixedArgs_7245_);
                                            lean_closure_set(v___x_7274_, 9, v_preDefs_7234_);
                                            lean_closure_set(v___x_7274_, 10, v___x_7235_);
                                            lean_closure_set(v___x_7274_, 11, v___x_7233_);
                                            lean_closure_set(v___x_7274_, 12, lean_box(0));
                                            lean_closure_set(v___x_7274_, 13, v___x_7273_);
                                            v___x_7275_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_7274_, v___x_7240_, v___y_7246_, v___y_7247_, v___y_7248_, v___y_7249_, v___y_7250_, v___y_7251_);
                                            if lean_obj_tag(v___x_7275_) == 0 {
                                                v_a_7276_ = lean_ctor_get(v___x_7275_, 0);
                                                lean_inc(v_a_7276_);
                                                lean_dec_ref_known(v___x_7275_, 1);
                                                v___x_7277_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_partialFixpoint___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_partialFixpoint___lam__0___closed__0_once), _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0);
                                                v___x_7278_ = l_Lean_Elab_partialFixpoint___lam__0___closed__1;
                                                v___x_7279_ = l_Lean_Meta_PProdN_genMk___redArg(
                                                    v___x_7277_,
                                                    v___x_7278_,
                                                    v_a_7276_,
                                                    v___y_7248_,
                                                    v___y_7249_,
                                                    v___y_7250_,
                                                    v___y_7251_,
                                                );
                                                if lean_obj_tag(v___x_7279_) == 0 {
                                                    v_a_7280_ = lean_ctor_get(v___x_7279_, 0);
                                                    lean_inc(v_a_7280_);
                                                    lean_dec_ref_known(v___x_7279_, 1);
                                                    v_snd_7281_ = lean_ctor_get(v_a_7280_, 1);
                                                    v_isSharedCheck_7402_ =
                                                        (!lean_is_exclusive(v_a_7280_)) as u8;
                                                    if v_isSharedCheck_7402_ == 0 {
                                                        v_unused_7403_ =
                                                            lean_ctor_get(v_a_7280_, 0);
                                                        lean_dec(v_unused_7403_);
                                                        v___x_7283_ = v_a_7280_;
                                                        v_isShared_7284_ = v_isSharedCheck_7402_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_snd_7281_);
                                                        lean_dec(v_a_7280_);
                                                        v___x_7283_ = lean_box(0);
                                                        v_isShared_7284_ = v_isSharedCheck_7402_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_7273_);
                                                    lean_dec(v_a_7266_);
                                                    lean_dec(v_a_7261_);
                                                    lean_dec_ref(v_fixedArgs_7245_);
                                                    lean_dec_ref(v_docCtx_7243_);
                                                    lean_dec_ref(v___x_7242_);
                                                    lean_dec_ref(v_hints_7241_);
                                                    lean_dec_ref(v_a_7239_);
                                                    lean_dec(v___x_7235_);
                                                    lean_dec_ref(v_preDefs_7234_);
                                                    lean_dec(v___x_7233_);
                                                    lean_dec_ref(v_perms_7232_);
                                                    v_a_7404_ = lean_ctor_get(v___x_7279_, 0);
                                                    v_isSharedCheck_7411_ =
                                                        (!lean_is_exclusive(v___x_7279_)) as u8;
                                                    if v_isSharedCheck_7411_ == 0 {
                                                        v___x_7406_ = v___x_7279_;
                                                        v_isShared_7407_ = v_isSharedCheck_7411_;
                                                        state = 18;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_7404_);
                                                        lean_dec(v___x_7279_);
                                                        v___x_7406_ = lean_box(0);
                                                        v_isShared_7407_ = v_isSharedCheck_7411_;
                                                        state = 18;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_7273_);
                                                lean_dec(v_a_7266_);
                                                lean_dec(v_a_7261_);
                                                lean_dec_ref(v_fixedArgs_7245_);
                                                lean_dec_ref(v_docCtx_7243_);
                                                lean_dec_ref(v___x_7242_);
                                                lean_dec_ref(v_hints_7241_);
                                                lean_dec_ref(v_a_7239_);
                                                lean_dec(v___x_7235_);
                                                lean_dec_ref(v_preDefs_7234_);
                                                lean_dec(v___x_7233_);
                                                lean_dec_ref(v_perms_7232_);
                                                v_a_7412_ = lean_ctor_get(v___x_7275_, 0);
                                                v_isSharedCheck_7419_ =
                                                    (!lean_is_exclusive(v___x_7275_)) as u8;
                                                if v_isSharedCheck_7419_ == 0 {
                                                    v___x_7414_ = v___x_7275_;
                                                    v_isShared_7415_ = v_isSharedCheck_7419_;
                                                    state = 20;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7412_);
                                                    lean_dec(v___x_7275_);
                                                    v___x_7414_ = lean_box(0);
                                                    v_isShared_7415_ = v_isSharedCheck_7419_;
                                                    state = 20;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_7269_);
                                            lean_dec(v_a_7266_);
                                            lean_dec(v_a_7264_);
                                            lean_dec(v_a_7261_);
                                            lean_dec(v_a_7258_);
                                            lean_dec_ref(v_fixedArgs_7245_);
                                            lean_dec_ref(v_docCtx_7243_);
                                            lean_dec_ref(v___x_7242_);
                                            lean_dec_ref(v_hints_7241_);
                                            lean_dec_ref(v_a_7239_);
                                            lean_dec(v___x_7235_);
                                            lean_dec_ref(v_preDefs_7234_);
                                            lean_dec(v___x_7233_);
                                            lean_dec_ref(v_perms_7232_);
                                            v_a_7420_ = lean_ctor_get(v___x_7271_, 0);
                                            v_isSharedCheck_7427_ =
                                                (!lean_is_exclusive(v___x_7271_)) as u8;
                                            if v_isSharedCheck_7427_ == 0 {
                                                v___x_7422_ = v___x_7271_;
                                                v_isShared_7423_ = v_isSharedCheck_7427_;
                                                state = 22;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7420_);
                                                lean_dec(v___x_7271_);
                                                v___x_7422_ = lean_box(0);
                                                v_isShared_7423_ = v_isSharedCheck_7427_;
                                                state = 22;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_7266_);
                                        lean_dec(v_a_7264_);
                                        lean_dec(v_a_7261_);
                                        lean_dec(v_a_7258_);
                                        lean_dec_ref(v_fixedArgs_7245_);
                                        lean_dec_ref(v_docCtx_7243_);
                                        lean_dec_ref(v___x_7242_);
                                        lean_dec_ref(v_hints_7241_);
                                        lean_dec_ref(v_a_7239_);
                                        lean_dec_ref(v___x_7238_);
                                        lean_dec_ref(v___x_7236_);
                                        lean_dec(v___x_7235_);
                                        lean_dec_ref(v_preDefs_7234_);
                                        lean_dec(v___x_7233_);
                                        lean_dec_ref(v_perms_7232_);
                                        v_a_7428_ = lean_ctor_get(v___x_7268_, 0);
                                        v_isSharedCheck_7435_ =
                                            (!lean_is_exclusive(v___x_7268_)) as u8;
                                        if v_isSharedCheck_7435_ == 0 {
                                            v___x_7430_ = v___x_7268_;
                                            v_isShared_7431_ = v_isSharedCheck_7435_;
                                            state = 24;
                                            continue;
                                        } else {
                                            lean_inc(v_a_7428_);
                                            lean_dec(v___x_7268_);
                                            v___x_7430_ = lean_box(0);
                                            v_isShared_7431_ = v_isSharedCheck_7435_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_7264_);
                                    lean_dec(v_a_7261_);
                                    lean_dec(v_a_7258_);
                                    lean_dec_ref(v_fixedArgs_7245_);
                                    lean_dec_ref(v_docCtx_7243_);
                                    lean_dec_ref(v___x_7242_);
                                    lean_dec_ref(v_hints_7241_);
                                    lean_dec_ref(v_a_7239_);
                                    lean_dec_ref(v___x_7238_);
                                    lean_dec_ref(v___x_7236_);
                                    lean_dec(v___x_7235_);
                                    lean_dec_ref(v_preDefs_7234_);
                                    lean_dec(v___x_7233_);
                                    lean_dec_ref(v_perms_7232_);
                                    v_a_7436_ = lean_ctor_get(v___x_7265_, 0);
                                    v_isSharedCheck_7443_ = (!lean_is_exclusive(v___x_7265_)) as u8;
                                    if v_isSharedCheck_7443_ == 0 {
                                        v___x_7438_ = v___x_7265_;
                                        v_isShared_7439_ = v_isSharedCheck_7443_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7436_);
                                        lean_dec(v___x_7265_);
                                        v___x_7438_ = lean_box(0);
                                        v_isShared_7439_ = v_isSharedCheck_7443_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_7261_);
                                lean_dec(v_a_7258_);
                                lean_dec_ref(v_fixedArgs_7245_);
                                lean_dec_ref(v_docCtx_7243_);
                                lean_dec_ref(v___x_7242_);
                                lean_dec_ref(v_hints_7241_);
                                lean_dec_ref(v_a_7239_);
                                lean_dec_ref(v___x_7238_);
                                lean_dec_ref(v___x_7236_);
                                lean_dec(v___x_7235_);
                                lean_dec_ref(v_preDefs_7234_);
                                lean_dec(v___x_7233_);
                                lean_dec_ref(v_perms_7232_);
                                v_a_7444_ = lean_ctor_get(v___x_7263_, 0);
                                v_isSharedCheck_7451_ = (!lean_is_exclusive(v___x_7263_)) as u8;
                                if v_isSharedCheck_7451_ == 0 {
                                    v___x_7446_ = v___x_7263_;
                                    v_isShared_7447_ = v_isSharedCheck_7451_;
                                    state = 28;
                                    continue;
                                } else {
                                    lean_inc(v_a_7444_);
                                    lean_dec(v___x_7263_);
                                    v___x_7446_ = lean_box(0);
                                    v_isShared_7447_ = v_isSharedCheck_7451_;
                                    state = 28;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_7258_);
                            lean_dec(v_a_7256_);
                            lean_dec_ref(v_fixedArgs_7245_);
                            lean_dec_ref(v_docCtx_7243_);
                            lean_dec_ref(v___x_7242_);
                            lean_dec_ref(v_hints_7241_);
                            lean_dec_ref(v_a_7239_);
                            lean_dec_ref(v___x_7238_);
                            lean_dec_ref(v___x_7236_);
                            lean_dec(v___x_7235_);
                            lean_dec_ref(v_preDefs_7234_);
                            lean_dec(v___x_7233_);
                            lean_dec_ref(v_perms_7232_);
                            v_a_7452_ = lean_ctor_get(v___x_7260_, 0);
                            v_isSharedCheck_7459_ = (!lean_is_exclusive(v___x_7260_)) as u8;
                            if v_isSharedCheck_7459_ == 0 {
                                v___x_7454_ = v___x_7260_;
                                v_isShared_7455_ = v_isSharedCheck_7459_;
                                state = 30;
                                continue;
                            } else {
                                lean_inc(v_a_7452_);
                                lean_dec(v___x_7260_);
                                v___x_7454_ = lean_box(0);
                                v_isShared_7455_ = v_isSharedCheck_7459_;
                                state = 30;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_7256_);
                        lean_dec_ref(v_fixedArgs_7245_);
                        lean_dec_ref(v_docCtx_7243_);
                        lean_dec_ref(v___x_7242_);
                        lean_dec_ref(v_hints_7241_);
                        lean_dec_ref(v_a_7239_);
                        lean_dec_ref(v___x_7238_);
                        lean_dec_ref(v___x_7236_);
                        lean_dec(v___x_7235_);
                        lean_dec_ref(v_preDefs_7234_);
                        lean_dec(v___x_7233_);
                        lean_dec_ref(v_perms_7232_);
                        v_a_7460_ = lean_ctor_get(v___x_7257_, 0);
                        v_isSharedCheck_7467_ = (!lean_is_exclusive(v___x_7257_)) as u8;
                        if v_isSharedCheck_7467_ == 0 {
                            v___x_7462_ = v___x_7257_;
                            v_isShared_7463_ = v_isSharedCheck_7467_;
                            state = 32;
                            continue;
                        } else {
                            lean_inc(v_a_7460_);
                            lean_dec(v___x_7257_);
                            v___x_7462_ = lean_box(0);
                            v_isShared_7463_ = v_isSharedCheck_7467_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_fixedArgs_7245_);
                    lean_dec_ref(v_docCtx_7243_);
                    lean_dec_ref(v___x_7242_);
                    lean_dec_ref(v_hints_7241_);
                    lean_dec_ref(v_a_7239_);
                    lean_dec_ref(v___x_7238_);
                    lean_dec_ref(v___x_7236_);
                    lean_dec(v___x_7235_);
                    lean_dec_ref(v_preDefs_7234_);
                    lean_dec(v___x_7233_);
                    lean_dec_ref(v_perms_7232_);
                    v_a_7468_ = lean_ctor_get(v___x_7255_, 0);
                    v_isSharedCheck_7475_ = (!lean_is_exclusive(v___x_7255_)) as u8;
                    if v_isSharedCheck_7475_ == 0 {
                        v___x_7470_ = v___x_7255_;
                        v_isShared_7471_ = v_isSharedCheck_7475_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_a_7468_);
                        lean_dec(v___x_7255_);
                        v___x_7470_ = lean_box(0);
                        v_isShared_7471_ = v_isSharedCheck_7475_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_7261_);
                v___x_7285_ = l_Lean_Meta_mkFixOfMonFun(
                    v_a_7261_,
                    v_a_7266_,
                    v_snd_7281_,
                    v___y_7248_,
                    v___y_7249_,
                    v___y_7250_,
                    v___y_7251_,
                );
                if lean_obj_tag(v___x_7285_) == 0 {
                    v_a_7286_ = lean_ctor_get(v___x_7285_, 0);
                    lean_inc(v_a_7286_);
                    lean_dec_ref_known(v___x_7285_, 1);
                    v_options_7382_ = lean_ctor_get(v___y_7250_, 2);
                    v_hasTrace_7383_ = lean_ctor_get_uint8(
                        v_options_7382_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_7383_ == 0 {
                        lean_del_object(v___x_7283_);
                        v___y_7373_ = v___y_7246_;
                        v___y_7374_ = v___y_7247_;
                        v___y_7375_ = v___y_7248_;
                        v___y_7376_ = v___y_7249_;
                        v___y_7377_ = v___y_7250_;
                        v___y_7378_ = v___y_7251_;
                        state = 14;
                        continue;
                    } else {
                        v_inheritedTraceOptions_7384_ = lean_ctor_get(v___y_7250_, 13);
                        v___x_7385_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7;
                        v___x_7386_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
                        v___x_7387_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_7384_,
                            v_options_7382_,
                            v___x_7386_,
                        );
                        if v___x_7387_ == 0 {
                            lean_del_object(v___x_7283_);
                            v___y_7373_ = v___y_7246_;
                            v___y_7374_ = v___y_7247_;
                            v___y_7375_ = v___y_7248_;
                            v___y_7376_ = v___y_7249_;
                            v___y_7377_ = v___y_7250_;
                            v___y_7378_ = v___y_7251_;
                            state = 14;
                            continue;
                        } else {
                            v___x_7388_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_partialFixpoint___lam__0___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_partialFixpoint___lam__0___closed__5_once
                                ),
                                _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5,
                            );
                            lean_inc(v_a_7286_);
                            v___x_7389_ = l_Lean_MessageData_ofExpr(v_a_7286_);
                            if v_isShared_7284_ == 0 {
                                lean_ctor_set_tag(v___x_7283_, 7);
                                lean_ctor_set(v___x_7283_, 1, v___x_7389_);
                                lean_ctor_set(v___x_7283_, 0, v___x_7388_);
                                v___x_7391_ = v___x_7283_;
                                state = 15;
                                continue;
                            } else {
                                v_reuseFailAlloc_7393_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7393_, 0, v___x_7388_);
                                lean_ctor_set(v_reuseFailAlloc_7393_, 1, v___x_7389_);
                                v___x_7391_ = v_reuseFailAlloc_7393_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_7283_);
                    lean_dec_ref(v___x_7273_);
                    lean_dec(v_a_7261_);
                    lean_dec_ref(v_fixedArgs_7245_);
                    lean_dec_ref(v_docCtx_7243_);
                    lean_dec_ref(v___x_7242_);
                    lean_dec_ref(v_hints_7241_);
                    lean_dec_ref(v_a_7239_);
                    lean_dec(v___x_7235_);
                    lean_dec_ref(v_preDefs_7234_);
                    lean_dec(v___x_7233_);
                    lean_dec_ref(v_perms_7232_);
                    v_a_7394_ = lean_ctor_get(v___x_7285_, 0);
                    v_isSharedCheck_7401_ = (!lean_is_exclusive(v___x_7285_)) as u8;
                    if v_isSharedCheck_7401_ == 0 {
                        v___x_7396_ = v___x_7285_;
                        v_isShared_7397_ = v_isSharedCheck_7401_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_7394_);
                        lean_dec(v___x_7285_);
                        v___x_7396_ = lean_box(0);
                        v_isShared_7397_ = v_isSharedCheck_7401_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7295_ = 0;
                v___x_7296_ = 1;
                lean_inc(v_a_7261_);
                v___x_7297_ = l_Lean_Meta_mkForallFVars(
                    v_fixedArgs_7245_,
                    v_a_7261_,
                    v___x_7295_,
                    v___x_7240_,
                    v___x_7240_,
                    v___x_7296_,
                    v___y_7292_,
                    v___y_7288_,
                    v___y_7291_,
                    v___y_7290_,
                );
                if lean_obj_tag(v___x_7297_) == 0 {
                    v_a_7298_ = lean_ctor_get(v___x_7297_, 0);
                    lean_inc(v_a_7298_);
                    lean_dec_ref_known(v___x_7297_, 1);
                    v___x_7299_ = l_Lean_Meta_mkLambdaFVars(
                        v_fixedArgs_7245_,
                        v_a_7286_,
                        v___x_7295_,
                        v___x_7240_,
                        v___x_7295_,
                        v___x_7240_,
                        v___x_7296_,
                        v___y_7292_,
                        v___y_7288_,
                        v___y_7291_,
                        v___y_7290_,
                    );
                    lean_dec_ref(v_fixedArgs_7245_);
                    if lean_obj_tag(v___x_7299_) == 0 {
                        v_a_7300_ = lean_ctor_get(v___x_7299_, 0);
                        lean_inc(v_a_7300_);
                        lean_dec_ref_known(v___x_7299_, 1);
                        v_ref_7301_ = lean_ctor_get(v___x_7242_, 0);
                        v_kind_7302_ = lean_ctor_get_uint8(
                            v___x_7242_,
                            (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                        );
                        v_levelParams_7303_ = lean_ctor_get(v___x_7242_, 1);
                        v_modifiers_7304_ = lean_ctor_get(v___x_7242_, 2);
                        v_binders_7305_ = lean_ctor_get(v___x_7242_, 4);
                        v_numSectionVars_7306_ = lean_ctor_get(v___x_7242_, 5);
                        v_termination_7307_ = lean_ctor_get(v___x_7242_, 8);
                        v_isSharedCheck_7340_ = (!lean_is_exclusive(v___x_7242_)) as u8;
                        if v_isSharedCheck_7340_ == 0 {
                            v_unused_7341_ = lean_ctor_get(v___x_7242_, 7);
                            lean_dec(v_unused_7341_);
                            v_unused_7342_ = lean_ctor_get(v___x_7242_, 6);
                            lean_dec(v_unused_7342_);
                            v_unused_7343_ = lean_ctor_get(v___x_7242_, 3);
                            lean_dec(v_unused_7343_);
                            v___x_7309_ = v___x_7242_;
                            v_isShared_7310_ = v_isSharedCheck_7340_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_termination_7307_);
                            lean_inc(v_numSectionVars_7306_);
                            lean_inc(v_binders_7305_);
                            lean_inc(v_modifiers_7304_);
                            lean_inc(v_levelParams_7303_);
                            lean_inc(v_ref_7301_);
                            lean_dec(v___x_7242_);
                            v___x_7309_ = lean_box(0);
                            v_isShared_7310_ = v_isSharedCheck_7340_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_7298_);
                        lean_dec(v___y_7294_);
                        lean_dec_ref(v___x_7273_);
                        lean_dec(v_a_7261_);
                        lean_dec_ref(v_docCtx_7243_);
                        lean_dec_ref(v___x_7242_);
                        lean_dec_ref(v_hints_7241_);
                        lean_dec_ref(v_a_7239_);
                        lean_dec(v___x_7235_);
                        lean_dec_ref(v_preDefs_7234_);
                        lean_dec(v___x_7233_);
                        lean_dec_ref(v_perms_7232_);
                        v_a_7344_ = lean_ctor_get(v___x_7299_, 0);
                        v_isSharedCheck_7351_ = (!lean_is_exclusive(v___x_7299_)) as u8;
                        if v_isSharedCheck_7351_ == 0 {
                            v___x_7346_ = v___x_7299_;
                            v_isShared_7347_ = v_isSharedCheck_7351_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_7344_);
                            lean_dec(v___x_7299_);
                            v___x_7346_ = lean_box(0);
                            v_isShared_7347_ = v_isSharedCheck_7351_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_7294_);
                    lean_dec(v_a_7286_);
                    lean_dec_ref(v___x_7273_);
                    lean_dec(v_a_7261_);
                    lean_dec_ref(v_fixedArgs_7245_);
                    lean_dec_ref(v_docCtx_7243_);
                    lean_dec_ref(v___x_7242_);
                    lean_dec_ref(v_hints_7241_);
                    lean_dec_ref(v_a_7239_);
                    lean_dec(v___x_7235_);
                    lean_dec_ref(v_preDefs_7234_);
                    lean_dec(v___x_7233_);
                    lean_dec_ref(v_perms_7232_);
                    v_a_7352_ = lean_ctor_get(v___x_7297_, 0);
                    v_isSharedCheck_7359_ = (!lean_is_exclusive(v___x_7297_)) as u8;
                    if v_isSharedCheck_7359_ == 0 {
                        v___x_7354_ = v___x_7297_;
                        v_isShared_7355_ = v_isSharedCheck_7359_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_7352_);
                        lean_dec(v___x_7297_);
                        v___x_7354_ = lean_box(0);
                        v_isShared_7355_ = v_isSharedCheck_7359_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v___x_7235_);
                lean_inc(v___y_7294_);
                lean_inc(v_levelParams_7303_);
                v___x_7311_ =
                    l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(
                        v_perms_7232_,
                        v_levelParams_7303_,
                        v___y_7294_,
                        v___x_7235_,
                        v_a_7261_,
                        v_preDefs_7234_,
                        v___x_7235_,
                        v___x_7233_,
                        v___x_7273_,
                        v___y_7293_,
                        v___y_7289_,
                        v___y_7292_,
                        v___y_7288_,
                        v___y_7291_,
                        v___y_7290_,
                    );
                lean_dec_ref(v_perms_7232_);
                if lean_obj_tag(v___x_7311_) == 0 {
                    v_a_7312_ = lean_ctor_get(v___x_7311_, 0);
                    lean_inc(v_a_7312_);
                    lean_dec_ref_known(v___x_7311_, 1);
                    lean_inc(v___y_7294_);
                    if v_isShared_7310_ == 0 {
                        lean_ctor_set(v___x_7309_, 7, v_a_7300_);
                        lean_ctor_set(v___x_7309_, 6, v_a_7298_);
                        lean_ctor_set(v___x_7309_, 3, v___y_7294_);
                        v___x_7314_ = v___x_7309_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7331_ = lean_alloc_ctor(0, 9, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7331_, 0, v_ref_7301_);
                        lean_ctor_set(v_reuseFailAlloc_7331_, 1, v_levelParams_7303_);
                        lean_ctor_set(v_reuseFailAlloc_7331_, 2, v_modifiers_7304_);
                        lean_ctor_set(v_reuseFailAlloc_7331_, 3, v___y_7294_);
                        lean_ctor_set(v_reuseFailAlloc_7331_, 4, v_binders_7305_);
                        lean_ctor_set(v_reuseFailAlloc_7331_, 5, v_numSectionVars_7306_);
                        lean_ctor_set(v_reuseFailAlloc_7331_, 6, v_a_7298_);
                        lean_ctor_set(v_reuseFailAlloc_7331_, 7, v_a_7300_);
                        lean_ctor_set(v_reuseFailAlloc_7331_, 8, v_termination_7307_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_7331_,
                            (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                            v_kind_7302_,
                        );
                        v___x_7314_ = v_reuseFailAlloc_7331_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7309_);
                    lean_dec_ref(v_termination_7307_);
                    lean_dec(v_numSectionVars_7306_);
                    lean_dec(v_binders_7305_);
                    lean_dec_ref(v_modifiers_7304_);
                    lean_dec(v_levelParams_7303_);
                    lean_dec(v_ref_7301_);
                    lean_dec(v_a_7300_);
                    lean_dec(v_a_7298_);
                    lean_dec(v___y_7294_);
                    lean_dec_ref(v_docCtx_7243_);
                    lean_dec_ref(v_hints_7241_);
                    lean_dec_ref(v_a_7239_);
                    lean_dec_ref(v_preDefs_7234_);
                    v_a_7332_ = lean_ctor_get(v___x_7311_, 0);
                    v_isSharedCheck_7339_ = (!lean_is_exclusive(v___x_7311_)) as u8;
                    if v_isSharedCheck_7339_ == 0 {
                        v___x_7334_ = v___x_7311_;
                        v_isShared_7335_ = v_isSharedCheck_7339_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_7332_);
                        lean_dec(v___x_7311_);
                        v___x_7334_ = lean_box(0);
                        v_isShared_7335_ = v_isSharedCheck_7339_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                lean_inc_ref(v_preDefs_7234_);
                lean_inc_ref(v_docCtx_7243_);
                v___x_7315_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(
                    v_docCtx_7243_,
                    v_preDefs_7234_,
                    v_a_7312_,
                    v___x_7314_,
                    v___x_7240_,
                    v___y_7293_,
                    v___y_7289_,
                    v___y_7292_,
                    v___y_7288_,
                    v___y_7291_,
                    v___y_7290_,
                );
                lean_dec(v_a_7312_);
                if lean_obj_tag(v___x_7315_) == 0 {
                    lean_dec_ref_known(v___x_7315_, 1);
                    lean_inc_ref(v_preDefs_7234_);
                    v___x_7316_ = l_Lean_Elab_addAndCompilePartialRec(
                        v_docCtx_7243_,
                        v_preDefs_7234_,
                        v___y_7293_,
                        v___y_7289_,
                        v___y_7292_,
                        v___y_7288_,
                        v___y_7291_,
                        v___y_7290_,
                    );
                    if lean_obj_tag(v___x_7316_) == 0 {
                        lean_dec_ref_known(v___x_7316_, 1);
                        v___x_7317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_7244_, v___x_7237_, v_preDefs_7234_, v___y_7292_, v___y_7288_, v___y_7291_, v___y_7290_);
                        if lean_obj_tag(v___x_7317_) == 0 {
                            v_a_7318_ = lean_ctor_get(v___x_7317_, 0);
                            lean_inc_n(v_a_7318_, 2);
                            lean_dec_ref_known(v___x_7317_, 1);
                            v_sz_7319_ = lean_array_size(v_hints_7241_);
                            v___x_7320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(v_sz_7319_, v___x_7237_, v_hints_7241_);
                            v___x_7321_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(
                                v_a_7318_,
                                v___y_7294_,
                                v_a_7239_,
                                v___x_7320_,
                                v___y_7292_,
                                v___y_7288_,
                                v___y_7291_,
                                v___y_7290_,
                            );
                            if lean_obj_tag(v___x_7321_) == 0 {
                                lean_dec_ref_known(v___x_7321_, 1);
                                v___x_7322_ = l_Lean_Elab_Mutual_addPreDefAttributes(
                                    v_a_7318_,
                                    v___y_7293_,
                                    v___y_7289_,
                                    v___y_7292_,
                                    v___y_7288_,
                                    v___y_7291_,
                                    v___y_7290_,
                                );
                                return v___x_7322_;
                            } else {
                                lean_dec(v_a_7318_);
                                return v___x_7321_;
                            }
                        } else {
                            lean_dec(v___y_7294_);
                            lean_dec_ref(v_hints_7241_);
                            lean_dec_ref(v_a_7239_);
                            v_a_7323_ = lean_ctor_get(v___x_7317_, 0);
                            v_isSharedCheck_7330_ = (!lean_is_exclusive(v___x_7317_)) as u8;
                            if v_isSharedCheck_7330_ == 0 {
                                v___x_7325_ = v___x_7317_;
                                v_isShared_7326_ = v_isSharedCheck_7330_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_7323_);
                                lean_dec(v___x_7317_);
                                v___x_7325_ = lean_box(0);
                                v_isShared_7326_ = v_isSharedCheck_7330_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_7294_);
                        lean_dec_ref(v_hints_7241_);
                        lean_dec_ref(v_a_7239_);
                        lean_dec_ref(v_preDefs_7234_);
                        return v___x_7316_;
                    }
                } else {
                    lean_dec(v___y_7294_);
                    lean_dec_ref(v_docCtx_7243_);
                    lean_dec_ref(v_hints_7241_);
                    lean_dec_ref(v_a_7239_);
                    lean_dec_ref(v_preDefs_7234_);
                    return v___x_7315_;
                }
            }
            5 => {
                if v_isShared_7326_ == 0 {
                    v___x_7328_ = v___x_7325_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7329_, 0, v_a_7323_);
                    v___x_7328_ = v_reuseFailAlloc_7329_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7328_;
            }
            7 => {
                if v_isShared_7335_ == 0 {
                    v___x_7337_ = v___x_7334_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7338_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7338_, 0, v_a_7332_);
                    v___x_7337_ = v_reuseFailAlloc_7338_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7337_;
            }
            9 => {
                if v_isShared_7347_ == 0 {
                    v___x_7349_ = v___x_7346_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7350_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7350_, 0, v_a_7344_);
                    v___x_7349_ = v_reuseFailAlloc_7350_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7349_;
            }
            11 => {
                if v_isShared_7355_ == 0 {
                    v___x_7357_ = v___x_7354_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7358_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7358_, 0, v_a_7352_);
                    v___x_7357_ = v_reuseFailAlloc_7358_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7357_;
            }
            13 => {
                if v___y_7367_ == 0 {
                    v_declName_7368_ = lean_ctor_get(v___x_7242_, 3);
                    v___x_7369_ = l_Lean_Elab_partialFixpoint___lam__0___closed__3;
                    lean_inc(v_declName_7368_);
                    v___x_7370_ = l_Lean_Name_append(v_declName_7368_, v___x_7369_);
                    v___y_7288_ = v___y_7361_;
                    v___y_7289_ = v___y_7362_;
                    v___y_7290_ = v___y_7363_;
                    v___y_7291_ = v___y_7365_;
                    v___y_7292_ = v___y_7364_;
                    v___y_7293_ = v___y_7366_;
                    v___y_7294_ = v___x_7370_;
                    state = 2;
                    continue;
                } else {
                    v_declName_7371_ = lean_ctor_get(v___x_7242_, 3);
                    lean_inc(v_declName_7371_);
                    v___y_7288_ = v___y_7361_;
                    v___y_7289_ = v___y_7362_;
                    v___y_7290_ = v___y_7363_;
                    v___y_7291_ = v___y_7365_;
                    v___y_7292_ = v___y_7364_;
                    v___y_7293_ = v___y_7366_;
                    v___y_7294_ = v_declName_7371_;
                    state = 2;
                    continue;
                }
            }
            14 => {
                v___x_7379_ = lean_unsigned_to_nat(1);
                v___x_7380_ = lean_nat_dec_eq(v___x_7235_, v___x_7379_);
                if v___x_7380_ == 0 {
                    v___y_7361_ = v___y_7376_;
                    v___y_7362_ = v___y_7374_;
                    v___y_7363_ = v___y_7378_;
                    v___y_7364_ = v___y_7375_;
                    v___y_7365_ = v___y_7377_;
                    v___y_7366_ = v___y_7373_;
                    v___y_7367_ = v___x_7380_;
                    state = 13;
                    continue;
                } else {
                    lean_inc_ref(v_a_7239_);
                    v___x_7381_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_a_7239_);
                    v___y_7361_ = v___y_7376_;
                    v___y_7362_ = v___y_7374_;
                    v___y_7363_ = v___y_7378_;
                    v___y_7364_ = v___y_7375_;
                    v___y_7365_ = v___y_7377_;
                    v___y_7366_ = v___y_7373_;
                    v___y_7367_ = v___x_7381_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_7392_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(
                    v___x_7385_,
                    v___x_7391_,
                    v___y_7248_,
                    v___y_7249_,
                    v___y_7250_,
                    v___y_7251_,
                );
                if lean_obj_tag(v___x_7392_) == 0 {
                    lean_dec_ref_known(v___x_7392_, 1);
                    v___y_7373_ = v___y_7246_;
                    v___y_7374_ = v___y_7247_;
                    v___y_7375_ = v___y_7248_;
                    v___y_7376_ = v___y_7249_;
                    v___y_7377_ = v___y_7250_;
                    v___y_7378_ = v___y_7251_;
                    state = 14;
                    continue;
                } else {
                    lean_dec(v_a_7286_);
                    lean_dec_ref(v___x_7273_);
                    lean_dec(v_a_7261_);
                    lean_dec_ref(v_fixedArgs_7245_);
                    lean_dec_ref(v_docCtx_7243_);
                    lean_dec_ref(v___x_7242_);
                    lean_dec_ref(v_hints_7241_);
                    lean_dec_ref(v_a_7239_);
                    lean_dec(v___x_7235_);
                    lean_dec_ref(v_preDefs_7234_);
                    lean_dec(v___x_7233_);
                    lean_dec_ref(v_perms_7232_);
                    return v___x_7392_;
                }
            }
            16 => {
                if v_isShared_7397_ == 0 {
                    v___x_7399_ = v___x_7396_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7400_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7400_, 0, v_a_7394_);
                    v___x_7399_ = v_reuseFailAlloc_7400_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7399_;
            }
            18 => {
                if v_isShared_7407_ == 0 {
                    v___x_7409_ = v___x_7406_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7410_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7410_, 0, v_a_7404_);
                    v___x_7409_ = v_reuseFailAlloc_7410_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7409_;
            }
            20 => {
                if v_isShared_7415_ == 0 {
                    v___x_7417_ = v___x_7414_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7418_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7418_, 0, v_a_7412_);
                    v___x_7417_ = v_reuseFailAlloc_7418_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7417_;
            }
            22 => {
                if v_isShared_7423_ == 0 {
                    v___x_7425_ = v___x_7422_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7426_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7426_, 0, v_a_7420_);
                    v___x_7425_ = v_reuseFailAlloc_7426_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7425_;
            }
            24 => {
                if v_isShared_7431_ == 0 {
                    v___x_7433_ = v___x_7430_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7434_, 0, v_a_7428_);
                    v___x_7433_ = v_reuseFailAlloc_7434_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_7433_;
            }
            26 => {
                if v_isShared_7439_ == 0 {
                    v___x_7441_ = v___x_7438_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_7442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7442_, 0, v_a_7436_);
                    v___x_7441_ = v_reuseFailAlloc_7442_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_7441_;
            }
            28 => {
                if v_isShared_7447_ == 0 {
                    v___x_7449_ = v___x_7446_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_7450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7450_, 0, v_a_7444_);
                    v___x_7449_ = v_reuseFailAlloc_7450_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_7449_;
            }
            30 => {
                if v_isShared_7455_ == 0 {
                    v___x_7457_ = v___x_7454_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_7458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7458_, 0, v_a_7452_);
                    v___x_7457_ = v_reuseFailAlloc_7458_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_7457_;
            }
            32 => {
                if v_isShared_7463_ == 0 {
                    v___x_7465_ = v___x_7462_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_7466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7466_, 0, v_a_7460_);
                    v___x_7465_ = v_reuseFailAlloc_7466_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_7465_;
            }
            34 => {
                if v_isShared_7471_ == 0 {
                    v___x_7473_ = v___x_7470_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_7474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7474_, 0, v_a_7468_);
                    v___x_7473_ = v_reuseFailAlloc_7474_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_7473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_partialFixpoint___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7476_: *mut LeanObject = *_args.add(0);
    let mut v_perms_7477_: *mut LeanObject = *_args.add(1);
    let mut v___x_7478_: *mut LeanObject = *_args.add(2);
    let mut v_preDefs_7479_: *mut LeanObject = *_args.add(3);
    let mut v___x_7480_: *mut LeanObject = *_args.add(4);
    let mut v___x_7481_: *mut LeanObject = *_args.add(5);
    let mut v___x_7482_: *mut LeanObject = *_args.add(6);
    let mut v___x_7483_: *mut LeanObject = *_args.add(7);
    let mut v_a_7484_: *mut LeanObject = *_args.add(8);
    let mut v___x_7485_: *mut LeanObject = *_args.add(9);
    let mut v_hints_7486_: *mut LeanObject = *_args.add(10);
    let mut v___x_7487_: *mut LeanObject = *_args.add(11);
    let mut v_docCtx_7488_: *mut LeanObject = *_args.add(12);
    let mut v_sz_7489_: *mut LeanObject = *_args.add(13);
    let mut v_fixedArgs_7490_: *mut LeanObject = *_args.add(14);
    let mut v___y_7491_: *mut LeanObject = *_args.add(15);
    let mut v___y_7492_: *mut LeanObject = *_args.add(16);
    let mut v___y_7493_: *mut LeanObject = *_args.add(17);
    let mut v___y_7494_: *mut LeanObject = *_args.add(18);
    let mut v___y_7495_: *mut LeanObject = *_args.add(19);
    let mut v___y_7496_: *mut LeanObject = *_args.add(20);
    let mut v___y_7497_: *mut LeanObject = *_args.add(21);
    let mut v___x_58021__boxed_7498_: usize = 0;
    let mut v___x_58024__boxed_7499_: u8 = 0;
    let mut v_sz_boxed_7500_: usize = 0;
    let mut v_res_7501_: *mut LeanObject = core::ptr::null_mut();
    v___x_58021__boxed_7498_ = lean_unbox_usize(v___x_7482_);
    lean_dec(v___x_7482_);
    v___x_58024__boxed_7499_ = (lean_unbox(v___x_7485_) as u8);
    v_sz_boxed_7500_ = lean_unbox_usize(v_sz_7489_);
    lean_dec(v_sz_7489_);
    v_res_7501_ = l_Lean_Elab_partialFixpoint___lam__0(
        v_a_7476_,
        v_perms_7477_,
        v___x_7478_,
        v_preDefs_7479_,
        v___x_7480_,
        v___x_7481_,
        v___x_58021__boxed_7498_,
        v___x_7483_,
        v_a_7484_,
        v___x_58024__boxed_7499_,
        v_hints_7486_,
        v___x_7487_,
        v_docCtx_7488_,
        v_sz_boxed_7500_,
        v_fixedArgs_7490_,
        v___y_7491_,
        v___y_7492_,
        v___y_7493_,
        v___y_7494_,
        v___y_7495_,
        v___y_7496_,
    );
    lean_dec(v___y_7496_);
    lean_dec_ref(v___y_7495_);
    lean_dec(v___y_7494_);
    lean_dec_ref(v___y_7493_);
    lean_dec(v___y_7492_);
    lean_dec_ref(v___y_7491_);
    lean_dec_ref(v_a_7476_);
    return v_res_7501_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(
    mut v_as_7502_: *mut LeanObject,
    mut v_i_7503_: usize,
    mut v_stop_7504_: usize,
    mut v_b_7505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: usize = 0;
    let mut v___x_7509_: usize = 0;
    let mut v___x_7511_: u8 = 0;
    let mut v___x_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termination_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_partialFixpoint_x3f_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7511_ = lean_usize_dec_eq(v_i_7503_, v_stop_7504_);
                if v___x_7511_ == 0 {
                    v___x_7512_ = lean_array_uget_borrowed(v_as_7502_, v_i_7503_);
                    v_termination_7513_ = lean_ctor_get(v___x_7512_, 8);
                    v_partialFixpoint_x3f_7514_ = lean_ctor_get(v_termination_7513_, 3);
                    if lean_obj_tag(v_partialFixpoint_x3f_7514_) == 0 {
                        v___y_7507_ = v_b_7505_;
                        state = 1;
                        continue;
                    } else {
                        v_val_7515_ = lean_ctor_get(v_partialFixpoint_x3f_7514_, 0);
                        lean_inc(v_val_7515_);
                        v___x_7516_ = lean_array_push(v_b_7505_, v_val_7515_);
                        v___y_7507_ = v___x_7516_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_7505_;
                }
            }
            1 => {
                v___x_7508_ = 1usize;
                v___x_7509_ = lean_usize_add(v_i_7503_, v___x_7508_);
                v_i_7503_ = v___x_7509_;
                v_b_7505_ = v___y_7507_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0___boxed(
    mut v_as_7517_: *mut LeanObject,
    mut v_i_7518_: *mut LeanObject,
    mut v_stop_7519_: *mut LeanObject,
    mut v_b_7520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7521_: usize = 0;
    let mut v_stop_boxed_7522_: usize = 0;
    let mut v_res_7523_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7521_ = lean_unbox_usize(v_i_7518_);
    lean_dec(v_i_7518_);
    v_stop_boxed_7522_ = lean_unbox_usize(v_stop_7519_);
    lean_dec(v_stop_7519_);
    v_res_7523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_7517_, v_i_boxed_7521_, v_stop_boxed_7522_, v_b_7520_);
    lean_dec_ref(v_as_7517_);
    return v_res_7523_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(
    mut v_as_7526_: *mut LeanObject,
    mut v_start_7527_: *mut LeanObject,
    mut v_stop_7528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: u8 = 0;
    v___x_7529_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0;
    v___x_7530_ = lean_nat_dec_lt(v_start_7527_, v_stop_7528_);
    if v___x_7530_ == 0 {
        return v___x_7529_;
    } else {
        let mut v___x_7531_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7532_: u8 = 0;
        v___x_7531_ = lean_array_get_size(v_as_7526_);
        v___x_7532_ = lean_nat_dec_le(v_stop_7528_, v___x_7531_);
        if v___x_7532_ == 0 {
            let mut v___x_7533_: u8 = 0;
            v___x_7533_ = lean_nat_dec_lt(v_start_7527_, v___x_7531_);
            if v___x_7533_ == 0 {
                return v___x_7529_;
            } else {
                let mut v___x_7534_: usize = 0;
                let mut v___x_7535_: usize = 0;
                let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
                v___x_7534_ = lean_usize_of_nat(v_start_7527_);
                v___x_7535_ = lean_usize_of_nat(v___x_7531_);
                v___x_7536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_7526_, v___x_7534_, v___x_7535_, v___x_7529_);
                return v___x_7536_;
            }
        } else {
            let mut v___x_7537_: usize = 0;
            let mut v___x_7538_: usize = 0;
            let mut v___x_7539_: *mut LeanObject = core::ptr::null_mut();
            v___x_7537_ = lean_usize_of_nat(v_start_7527_);
            v___x_7538_ = lean_usize_of_nat(v_stop_7528_);
            v___x_7539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_7526_, v___x_7537_, v___x_7538_, v___x_7529_);
            return v___x_7539_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___boxed(
    mut v_as_7540_: *mut LeanObject,
    mut v_start_7541_: *mut LeanObject,
    mut v_stop_7542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7543_: *mut LeanObject = core::ptr::null_mut();
    v_res_7543_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(
        v_as_7540_,
        v_start_7541_,
        v_stop_7542_,
    );
    lean_dec(v_stop_7542_);
    lean_dec(v_start_7541_);
    lean_dec_ref(v_as_7540_);
    return v_res_7543_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(
    mut v___x_7544_: u8,
    mut v_as_7545_: *mut LeanObject,
    mut v_i_7546_: usize,
    mut v_stop_7547_: usize,
) -> u8 {
    let mut v___x_7548_: u8 = 0;
    let mut v___x_7549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixpointType_7550_: u8 = 0;
    let mut v___x_7551_: u8 = 0;
    let mut v___y_7553_: u8 = 0;
    let mut v___x_7554_: usize = 0;
    let mut v___x_7555_: usize = 0;
    let mut v___x_7557_: u8 = 0;
    let mut v___x_7558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7548_ = lean_usize_dec_eq(v_i_7546_, v_stop_7547_);
                if v___x_7548_ == 0 {
                    v___x_7549_ = lean_array_uget_borrowed(v_as_7545_, v_i_7546_);
                    v_fixpointType_7550_ = lean_ctor_get_uint8(
                        v___x_7549_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___x_7551_ = 1;
                    v___x_7557_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_7550_);
                    if v___x_7557_ == 0 {
                        v___y_7553_ = v___x_7544_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7553_ = v___x_7548_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_7558_ = 0;
                    return v___x_7558_;
                }
            }
            1 => {
                if v___y_7553_ == 0 {
                    v___x_7554_ = 1usize;
                    v___x_7555_ = lean_usize_add(v_i_7546_, v___x_7554_);
                    v_i_7546_ = v___x_7555_;
                    state = 0;
                    continue;
                } else {
                    return v___x_7551_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33___boxed(
    mut v___x_7559_: *mut LeanObject,
    mut v_as_7560_: *mut LeanObject,
    mut v_i_7561_: *mut LeanObject,
    mut v_stop_7562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_58547__boxed_7563_: u8 = 0;
    let mut v_i_boxed_7564_: usize = 0;
    let mut v_stop_boxed_7565_: usize = 0;
    let mut v_res_7566_: u8 = 0;
    let mut v_r_7567_: *mut LeanObject = core::ptr::null_mut();
    v___x_58547__boxed_7563_ = (lean_unbox(v___x_7559_) as u8);
    v_i_boxed_7564_ = lean_unbox_usize(v_i_7561_);
    lean_dec(v_i_7561_);
    v_stop_boxed_7565_ = lean_unbox_usize(v_stop_7562_);
    lean_dec(v_stop_7562_);
    v_res_7566_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(v___x_58547__boxed_7563_, v_as_7560_, v_i_boxed_7564_, v_stop_boxed_7565_);
    lean_dec_ref(v_as_7560_);
    v_r_7567_ = lean_box((v_res_7566_) as usize);
    return v_r_7567_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(
    mut v___x_7568_: u8,
    mut v_as_7569_: *mut LeanObject,
    mut v_i_7570_: usize,
    mut v_stop_7571_: usize,
) -> u8 {
    let mut v___x_7572_: u8 = 0;
    let mut v___x_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixpointType_7574_: u8 = 0;
    let mut v___x_7575_: u8 = 0;
    let mut v___y_7577_: u8 = 0;
    let mut v___x_7578_: usize = 0;
    let mut v___x_7579_: usize = 0;
    let mut v___x_7580_: u8 = 0;
    let mut v___x_7581_: u8 = 0;
    let mut v___x_7582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7572_ = lean_usize_dec_eq(v_i_7570_, v_stop_7571_);
                if v___x_7572_ == 0 {
                    v___x_7573_ = lean_array_uget_borrowed(v_as_7569_, v_i_7570_);
                    v_fixpointType_7574_ = lean_ctor_get_uint8(
                        v___x_7573_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___x_7575_ = 1;
                    v___x_7581_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_7574_);
                    if v___x_7581_ == 0 {
                        v___y_7577_ = v___x_7568_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7577_ = v___x_7572_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_7582_ = 0;
                    return v___x_7582_;
                }
            }
            1 => {
                if v___y_7577_ == 0 {
                    v___x_7578_ = 1usize;
                    v___x_7579_ = lean_usize_add(v_i_7570_, v___x_7578_);
                    v___x_7580_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(v___x_7568_, v_as_7569_, v___x_7579_, v_stop_7571_);
                    return v___x_7580_;
                } else {
                    return v___x_7575_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27___boxed(
    mut v___x_7583_: *mut LeanObject,
    mut v_as_7584_: *mut LeanObject,
    mut v_i_7585_: *mut LeanObject,
    mut v_stop_7586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_58570__boxed_7587_: u8 = 0;
    let mut v_i_boxed_7588_: usize = 0;
    let mut v_stop_boxed_7589_: usize = 0;
    let mut v_res_7590_: u8 = 0;
    let mut v_r_7591_: *mut LeanObject = core::ptr::null_mut();
    v___x_58570__boxed_7587_ = (lean_unbox(v___x_7583_) as u8);
    v_i_boxed_7588_ = lean_unbox_usize(v_i_7585_);
    lean_dec(v_i_7585_);
    v_stop_boxed_7589_ = lean_unbox_usize(v_stop_7586_);
    lean_dec(v_stop_7586_);
    v_res_7590_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v___x_58570__boxed_7587_, v_as_7584_, v_i_boxed_7588_, v_stop_boxed_7589_);
    lean_dec_ref(v_as_7584_);
    v_r_7591_ = lean_box((v_res_7590_) as usize);
    return v_r_7591_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(
    mut v_sz_7592_: usize,
    mut v_i_7593_: usize,
    mut v_bs_7594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7595_: u8 = 0;
    let mut v_v_7596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_7597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: usize = 0;
    let mut v___x_7601_: usize = 0;
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7595_ = lean_usize_dec_lt(v_i_7593_, v_sz_7592_);
                if v___x_7595_ == 0 {
                    return v_bs_7594_;
                } else {
                    v_v_7596_ = lean_array_uget_borrowed(v_bs_7594_, v_i_7593_);
                    v_declName_7597_ = lean_ctor_get(v_v_7596_, 3);
                    lean_inc(v_declName_7597_);
                    v___x_7598_ = lean_unsigned_to_nat(0);
                    v_bs_x27_7599_ = lean_array_uset(v_bs_7594_, v_i_7593_, v___x_7598_);
                    v___x_7600_ = 1usize;
                    v___x_7601_ = lean_usize_add(v_i_7593_, v___x_7600_);
                    v___x_7602_ = lean_array_uset(v_bs_x27_7599_, v_i_7593_, v_declName_7597_);
                    v_i_7593_ = v___x_7601_;
                    v_bs_7594_ = v___x_7602_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7___boxed(
    mut v_sz_7604_: *mut LeanObject,
    mut v_i_7605_: *mut LeanObject,
    mut v_bs_7606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7607_: usize = 0;
    let mut v_i_boxed_7608_: usize = 0;
    let mut v_res_7609_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7607_ = lean_unbox_usize(v_sz_7604_);
    lean_dec(v_sz_7604_);
    v_i_boxed_7608_ = lean_unbox_usize(v_i_7605_);
    lean_dec(v_i_7605_);
    v_res_7609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(v_sz_boxed_7607_, v_i_boxed_7608_, v_bs_7606_);
    return v_res_7609_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1()
-> *mut LeanObject {
    let mut v___x_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7612_: *mut LeanObject = core::ptr::null_mut();
    v___x_7611_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0;
    v___x_7612_ = l_Lean_stringToMessageData(v___x_7611_);
    return v___x_7612_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3()
-> *mut LeanObject {
    let mut v___x_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: *mut LeanObject = core::ptr::null_mut();
    v___x_7614_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2;
    v___x_7615_ = l_Lean_stringToMessageData(v___x_7614_);
    return v___x_7615_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11()
-> *mut LeanObject {
    let mut v___x_7628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7631_: *mut LeanObject = core::ptr::null_mut();
    v___x_7628_ = lean_box(0);
    v___x_7629_ = lean_unsigned_to_nat(2);
    v___x_7630_ = lean_mk_empty_array_with_capacity(v___x_7629_);
    v___x_7631_ = lean_array_push(v___x_7630_, v___x_7628_);
    return v___x_7631_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(
    mut v_declName_7634_: *mut LeanObject,
    mut v_type_7635_: *mut LeanObject,
    mut v_xs_7636_: *mut LeanObject,
    mut v___x_7637_: *mut LeanObject,
    mut v___x_7638_: *mut LeanObject,
    mut v_____r_7639_: *mut LeanObject,
    mut v___y_7640_: *mut LeanObject,
    mut v___y_7641_: *mut LeanObject,
    mut v___y_7642_: *mut LeanObject,
    mut v___y_7643_: *mut LeanObject,
    mut v___y_7644_: *mut LeanObject,
    mut v___y_7645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7664_: u8 = 0;
    let mut v___x_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7674_: u8 = 0;
    let mut v___x_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7683_: u8 = 0;
    let mut v_reuseFailAlloc_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7647_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1);
                v___x_7648_ = l_Lean_MessageData_ofName(v_declName_7634_);
                v___x_7649_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7649_, 0, v___x_7647_);
                lean_ctor_set(v___x_7649_, 1, v___x_7648_);
                v___x_7650_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3);
                v___x_7651_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7651_, 0, v___x_7649_);
                lean_ctor_set(v___x_7651_, 1, v___x_7650_);
                v___x_7652_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4;
                v___x_7653_ = l_Lean_Elab_mkInhabitantFor(
                    v___x_7651_,
                    v___x_7652_,
                    v_type_7635_,
                    v___y_7642_,
                    v___y_7643_,
                    v___y_7644_,
                    v___y_7645_,
                );
                if lean_obj_tag(v___x_7653_) == 0 {
                    v_a_7654_ = lean_ctor_get(v___x_7653_, 0);
                    lean_inc(v_a_7654_);
                    lean_dec_ref_known(v___x_7653_, 1);
                    v___x_7655_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7;
                    v___x_7656_ = l_Lean_mkAppN(v_a_7654_, v_xs_7636_);
                    v___x_7657_ = lean_unsigned_to_nat(1);
                    v___x_7658_ = lean_mk_empty_array_with_capacity(v___x_7657_);
                    v___x_7659_ = lean_array_push(v___x_7658_, v___x_7656_);
                    v___x_7660_ = l_Lean_Meta_mkAppM(
                        v___x_7655_,
                        v___x_7659_,
                        v___y_7642_,
                        v___y_7643_,
                        v___y_7644_,
                        v___y_7645_,
                    );
                    if lean_obj_tag(v___x_7660_) == 0 {
                        v_a_7661_ = lean_ctor_get(v___x_7660_, 0);
                        v_isSharedCheck_7685_ = (!lean_is_exclusive(v___x_7660_)) as u8;
                        if v_isSharedCheck_7685_ == 0 {
                            v___x_7663_ = v___x_7660_;
                            v_isShared_7664_ = v_isSharedCheck_7685_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7661_);
                            lean_dec(v___x_7660_);
                            v___x_7663_ = lean_box(0);
                            v_isShared_7664_ = v_isSharedCheck_7685_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_7638_);
                        lean_dec_ref(v___x_7637_);
                        return v___x_7660_;
                    }
                } else {
                    lean_dec_ref(v___x_7638_);
                    lean_dec_ref(v___x_7637_);
                    return v___x_7653_;
                }
            }
            1 => {
                v___x_7665_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10;
                if v_isShared_7664_ == 0 {
                    lean_ctor_set_tag(v___x_7663_, 1);
                    v___x_7667_ = v___x_7663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7684_, 0, v_a_7661_);
                    v___x_7667_ = v_reuseFailAlloc_7684_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7668_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11);
                v___x_7669_ = lean_array_push(v___x_7668_, v___x_7667_);
                v___x_7670_ = l_Lean_Meta_mkAppOptM(
                    v___x_7665_,
                    v___x_7669_,
                    v___y_7642_,
                    v___y_7643_,
                    v___y_7644_,
                    v___y_7645_,
                );
                if lean_obj_tag(v___x_7670_) == 0 {
                    v_a_7671_ = lean_ctor_get(v___x_7670_, 0);
                    v_isSharedCheck_7683_ = (!lean_is_exclusive(v___x_7670_)) as u8;
                    if v_isSharedCheck_7683_ == 0 {
                        v___x_7673_ = v___x_7670_;
                        v_isShared_7674_ = v_isSharedCheck_7683_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7671_);
                        lean_dec(v___x_7670_);
                        v___x_7673_ = lean_box(0);
                        v_isShared_7674_ = v_isSharedCheck_7683_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_7638_);
                    lean_dec_ref(v___x_7637_);
                    return v___x_7670_;
                }
            }
            3 => {
                v___x_7675_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12;
                v___x_7676_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13;
                v___x_7677_ =
                    l_Lean_Name_mkStr4(v___x_7637_, v___x_7638_, v___x_7675_, v___x_7676_);
                if v_isShared_7674_ == 0 {
                    lean_ctor_set_tag(v___x_7673_, 1);
                    v___x_7679_ = v___x_7673_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7682_, 0, v_a_7671_);
                    v___x_7679_ = v_reuseFailAlloc_7682_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7680_ = lean_array_push(v___x_7668_, v___x_7679_);
                v___x_7681_ = l_Lean_Meta_mkAppOptM(
                    v___x_7677_,
                    v___x_7680_,
                    v___y_7642_,
                    v___y_7643_,
                    v___y_7644_,
                    v___y_7645_,
                );
                return v___x_7681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed(
    mut v_declName_7686_: *mut LeanObject,
    mut v_type_7687_: *mut LeanObject,
    mut v_xs_7688_: *mut LeanObject,
    mut v___x_7689_: *mut LeanObject,
    mut v___x_7690_: *mut LeanObject,
    mut v_____r_7691_: *mut LeanObject,
    mut v___y_7692_: *mut LeanObject,
    mut v___y_7693_: *mut LeanObject,
    mut v___y_7694_: *mut LeanObject,
    mut v___y_7695_: *mut LeanObject,
    mut v___y_7696_: *mut LeanObject,
    mut v___y_7697_: *mut LeanObject,
    mut v___y_7698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7699_: *mut LeanObject = core::ptr::null_mut();
    v_res_7699_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(
            v_declName_7686_,
            v_type_7687_,
            v_xs_7688_,
            v___x_7689_,
            v___x_7690_,
            v_____r_7691_,
            v___y_7692_,
            v___y_7693_,
            v___y_7694_,
            v___y_7695_,
            v___y_7696_,
            v___y_7697_,
        );
    lean_dec(v___y_7697_);
    lean_dec_ref(v___y_7696_);
    lean_dec(v___y_7695_);
    lean_dec_ref(v___y_7694_);
    lean_dec(v___y_7693_);
    lean_dec_ref(v___y_7692_);
    lean_dec_ref(v_xs_7688_);
    return v_res_7699_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(
    mut v_a_7700_: *mut LeanObject,
    mut v_a_7701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7707_: u8 = 0;
    let mut v___x_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_7700_) == 0 {
                    v___x_7702_ = l_List_reverse___redArg(v_a_7701_);
                    return v___x_7702_;
                } else {
                    v_head_7703_ = lean_ctor_get(v_a_7700_, 0);
                    v_tail_7704_ = lean_ctor_get(v_a_7700_, 1);
                    v_isSharedCheck_7713_ = (!lean_is_exclusive(v_a_7700_)) as u8;
                    if v_isSharedCheck_7713_ == 0 {
                        v___x_7706_ = v_a_7700_;
                        v_isShared_7707_ = v_isSharedCheck_7713_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7704_);
                        lean_inc(v_head_7703_);
                        lean_dec(v_a_7700_);
                        v___x_7706_ = lean_box(0);
                        v_isShared_7707_ = v_isSharedCheck_7713_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7708_ = l_Lean_MessageData_ofExpr(v_head_7703_);
                if v_isShared_7707_ == 0 {
                    lean_ctor_set(v___x_7706_, 1, v_a_7701_);
                    lean_ctor_set(v___x_7706_, 0, v___x_7708_);
                    v___x_7710_ = v___x_7706_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7712_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7712_, 0, v___x_7708_);
                    lean_ctor_set(v_reuseFailAlloc_7712_, 1, v_a_7701_);
                    v___x_7710_ = v_reuseFailAlloc_7712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_7700_ = v_tail_7704_;
                v_a_7701_ = v___x_7710_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1()
-> *mut LeanObject {
    let mut v___x_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7716_: *mut LeanObject = core::ptr::null_mut();
    v___x_7715_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0;
    v___x_7716_ = l_Lean_stringToMessageData(v___x_7715_);
    return v___x_7716_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3()
-> *mut LeanObject {
    let mut v___x_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut LeanObject = core::ptr::null_mut();
    v___x_7718_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2;
    v___x_7719_ = l_Lean_stringToMessageData(v___x_7718_);
    return v___x_7719_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7()
-> *mut LeanObject {
    let mut v___x_7726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut LeanObject = core::ptr::null_mut();
    v___x_7726_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6;
    v___x_7727_ = l_Lean_stringToMessageData(v___x_7726_);
    return v___x_7727_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9()
-> *mut LeanObject {
    let mut v___x_7729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut LeanObject = core::ptr::null_mut();
    v___x_7729_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8;
    v___x_7730_ = l_Lean_stringToMessageData(v___x_7729_);
    return v___x_7730_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11()
-> *mut LeanObject {
    let mut v___x_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut LeanObject = core::ptr::null_mut();
    v___x_7732_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10;
    v___x_7733_ = l_Lean_stringToMessageData(v___x_7732_);
    return v___x_7733_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(
    mut v_isZero_7734_: u8,
    mut v_declName_7735_: *mut LeanObject,
    mut v_type_7736_: *mut LeanObject,
    mut v_fixpointType_7737_: u8,
    mut v___f_7738_: *mut LeanObject,
    mut v___f_7739_: *mut LeanObject,
    mut v_value_7740_: *mut LeanObject,
    mut v_xs_7741_: *mut LeanObject,
    mut v___body_7742_: *mut LeanObject,
    mut v___y_7743_: *mut LeanObject,
    mut v___y_7744_: *mut LeanObject,
    mut v___y_7745_: *mut LeanObject,
    mut v___y_7746_: *mut LeanObject,
    mut v___y_7747_: *mut LeanObject,
    mut v___y_7748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7756_: u8 = 0;
    let mut v___x_7757_: u8 = 0;
    let mut v___x_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7778_: u8 = 0;
    let mut v_cls_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7789_: u8 = 0;
    let mut v_options_7790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7791_: u8 = 0;
    let mut v_inheritedTraceOptions_7792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7794_: u8 = 0;
    let mut v___x_7795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7806_: u8 = 0;
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7810_: u8 = 0;
    let mut v___y_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: u8 = 0;
    let mut v___x_7823_: u8 = 0;
    let mut v___y_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7851_: u8 = 0;
    let mut v___x_7852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7870_: u8 = 0;
    let mut v___x_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_7776_ = lean_ctor_get(v___y_7747_, 2);
                v_inheritedTraceOptions_7777_ = lean_ctor_get(v___y_7747_, 13);
                v_hasTrace_7778_ = lean_ctor_get_uint8(
                    v_options_7776_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_cls_7779_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7;
                if v_hasTrace_7778_ == 0 {
                    lean_dec_ref(v___body_7742_);
                    lean_dec_ref(v_value_7740_);
                    v___y_7825_ = v___y_7743_;
                    v___y_7826_ = v___y_7744_;
                    v___y_7827_ = v___y_7745_;
                    v___y_7828_ = v___y_7746_;
                    v___y_7829_ = v___y_7747_;
                    v___y_7830_ = v___y_7748_;
                    state = 8;
                    continue;
                } else {
                    v___x_7850_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
                    v___x_7851_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_7777_,
                        v_options_7776_,
                        v___x_7850_,
                    );
                    if v___x_7851_ == 0 {
                        lean_dec_ref(v___body_7742_);
                        lean_dec_ref(v_value_7740_);
                        v___y_7825_ = v___y_7743_;
                        v___y_7826_ = v___y_7744_;
                        v___y_7827_ = v___y_7745_;
                        v___y_7828_ = v___y_7746_;
                        v___y_7829_ = v___y_7747_;
                        v___y_7830_ = v___y_7748_;
                        state = 8;
                        continue;
                    } else {
                        v___x_7852_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7);
                        v___x_7853_ = l_Lean_MessageData_ofExpr(v_value_7740_);
                        v___x_7854_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7854_, 0, v___x_7852_);
                        lean_ctor_set(v___x_7854_, 1, v___x_7853_);
                        v___x_7855_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9);
                        v___x_7856_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7856_, 0, v___x_7854_);
                        lean_ctor_set(v___x_7856_, 1, v___x_7855_);
                        lean_inc_ref(v_xs_7741_);
                        v___x_7857_ = lean_array_to_list(v_xs_7741_);
                        v___x_7858_ = lean_box(0);
                        v___x_7859_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(
                            v___x_7857_,
                            v___x_7858_,
                        );
                        v___x_7860_ = l_Lean_MessageData_ofList(v___x_7859_);
                        v___x_7861_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7861_, 0, v___x_7856_);
                        lean_ctor_set(v___x_7861_, 1, v___x_7860_);
                        v___x_7862_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11);
                        v___x_7863_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7863_, 0, v___x_7861_);
                        lean_ctor_set(v___x_7863_, 1, v___x_7862_);
                        v___x_7864_ = l_Lean_MessageData_ofExpr(v___body_7742_);
                        v___x_7865_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7865_, 0, v___x_7863_);
                        lean_ctor_set(v___x_7865_, 1, v___x_7864_);
                        v___x_7866_ =
                            l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(
                                v_cls_7779_,
                                v___x_7865_,
                                v___y_7745_,
                                v___y_7746_,
                                v___y_7747_,
                                v___y_7748_,
                            );
                        if lean_obj_tag(v___x_7866_) == 0 {
                            lean_dec_ref_known(v___x_7866_, 1);
                            v___y_7825_ = v___y_7743_;
                            v___y_7826_ = v___y_7744_;
                            v___y_7827_ = v___y_7745_;
                            v___y_7828_ = v___y_7746_;
                            v___y_7829_ = v___y_7747_;
                            v___y_7830_ = v___y_7748_;
                            state = 8;
                            continue;
                        } else {
                            lean_dec_ref(v_xs_7741_);
                            lean_dec_ref(v___f_7739_);
                            lean_dec_ref(v___f_7738_);
                            lean_dec_ref(v_type_7736_);
                            lean_dec(v_declName_7735_);
                            v_a_7867_ = lean_ctor_get(v___x_7866_, 0);
                            v_isSharedCheck_7874_ = (!lean_is_exclusive(v___x_7866_)) as u8;
                            if v_isSharedCheck_7874_ == 0 {
                                v___x_7869_ = v___x_7866_;
                                v_isShared_7870_ = v_isSharedCheck_7874_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_7867_);
                                lean_dec(v___x_7866_);
                                v___x_7869_ = lean_box(0);
                                v_isShared_7870_ = v_isSharedCheck_7874_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_7756_ = 1;
                v___x_7757_ = 1;
                v___x_7758_ = l_Lean_Meta_mkLambdaFVars(
                    v_xs_7741_,
                    v_inst_7751_,
                    v_isZero_7734_,
                    v___x_7756_,
                    v_isZero_7734_,
                    v___x_7756_,
                    v___x_7757_,
                    v___y_7752_,
                    v___y_7753_,
                    v___y_7754_,
                    v___y_7755_,
                );
                lean_dec_ref(v_xs_7741_);
                return v___x_7758_;
            }
            2 => {
                if lean_obj_tag(v___y_7764_) == 0 {
                    v_a_7765_ = lean_ctor_get(v___y_7764_, 0);
                    lean_inc(v_a_7765_);
                    lean_dec_ref_known(v___y_7764_, 1);
                    v_inst_7751_ = v_a_7765_;
                    v___y_7752_ = v___y_7762_;
                    v___y_7753_ = v___y_7763_;
                    v___y_7754_ = v___y_7760_;
                    v___y_7755_ = v___y_7761_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_xs_7741_);
                    return v___y_7764_;
                }
            }
            3 => {
                v___x_7774_ = lean_box(0);
                lean_inc(v___y_7770_);
                lean_inc_ref(v___y_7769_);
                lean_inc(v___y_7773_);
                lean_inc_ref(v___y_7771_);
                lean_inc(v___y_7772_);
                lean_inc_ref(v___y_7768_);
                v___x_7775_ = lean_apply_8(
                    v___y_7767_,
                    v___x_7774_,
                    v___y_7768_,
                    v___y_7772_,
                    v___y_7771_,
                    v___y_7773_,
                    v___y_7769_,
                    v___y_7770_,
                    lean_box(0),
                );
                v___y_7760_ = v___y_7769_;
                v___y_7761_ = v___y_7770_;
                v___y_7762_ = v___y_7771_;
                v___y_7763_ = v___y_7773_;
                v___y_7764_ = v___x_7775_;
                state = 2;
                continue;
            }
            4 => {
                if v___y_7789_ == 0 {
                    lean_dec_ref(v___y_7783_);
                    v_options_7790_ = lean_ctor_get(v___y_7784_, 2);
                    v_hasTrace_7791_ = lean_ctor_get_uint8(
                        v_options_7790_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_7791_ == 0 {
                        lean_dec(v_declName_7735_);
                        v___y_7767_ = v___y_7781_;
                        v___y_7768_ = v___y_7782_;
                        v___y_7769_ = v___y_7784_;
                        v___y_7770_ = v___y_7785_;
                        v___y_7771_ = v___y_7786_;
                        v___y_7772_ = v___y_7787_;
                        v___y_7773_ = v___y_7788_;
                        state = 3;
                        continue;
                    } else {
                        v_inheritedTraceOptions_7792_ = lean_ctor_get(v___y_7784_, 13);
                        v___x_7793_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
                        v___x_7794_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_7792_,
                            v_options_7790_,
                            v___x_7793_,
                        );
                        if v___x_7794_ == 0 {
                            lean_dec(v_declName_7735_);
                            v___y_7767_ = v___y_7781_;
                            v___y_7768_ = v___y_7782_;
                            v___y_7769_ = v___y_7784_;
                            v___y_7770_ = v___y_7785_;
                            v___y_7771_ = v___y_7786_;
                            v___y_7772_ = v___y_7787_;
                            v___y_7773_ = v___y_7788_;
                            state = 3;
                            continue;
                        } else {
                            v___x_7795_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1);
                            v___x_7796_ = l_Lean_MessageData_ofName(v_declName_7735_);
                            v___x_7797_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_7797_, 0, v___x_7795_);
                            lean_ctor_set(v___x_7797_, 1, v___x_7796_);
                            v___x_7798_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3);
                            v___x_7799_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_7799_, 0, v___x_7797_);
                            lean_ctor_set(v___x_7799_, 1, v___x_7798_);
                            v___x_7800_ =
                                l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(
                                    v_cls_7779_,
                                    v___x_7799_,
                                    v___y_7786_,
                                    v___y_7788_,
                                    v___y_7784_,
                                    v___y_7785_,
                                );
                            if lean_obj_tag(v___x_7800_) == 0 {
                                v_a_7801_ = lean_ctor_get(v___x_7800_, 0);
                                lean_inc(v_a_7801_);
                                lean_dec_ref_known(v___x_7800_, 1);
                                lean_inc(v___y_7785_);
                                lean_inc_ref(v___y_7784_);
                                lean_inc(v___y_7788_);
                                lean_inc_ref(v___y_7786_);
                                lean_inc(v___y_7787_);
                                lean_inc_ref(v___y_7782_);
                                v___x_7802_ = lean_apply_8(
                                    v___y_7781_,
                                    v_a_7801_,
                                    v___y_7782_,
                                    v___y_7787_,
                                    v___y_7786_,
                                    v___y_7788_,
                                    v___y_7784_,
                                    v___y_7785_,
                                    lean_box(0),
                                );
                                v___y_7760_ = v___y_7784_;
                                v___y_7761_ = v___y_7785_;
                                v___y_7762_ = v___y_7786_;
                                v___y_7763_ = v___y_7788_;
                                v___y_7764_ = v___x_7802_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec_ref(v___y_7781_);
                                lean_dec_ref(v_xs_7741_);
                                v_a_7803_ = lean_ctor_get(v___x_7800_, 0);
                                v_isSharedCheck_7810_ = (!lean_is_exclusive(v___x_7800_)) as u8;
                                if v_isSharedCheck_7810_ == 0 {
                                    v___x_7805_ = v___x_7800_;
                                    v_isShared_7806_ = v_isSharedCheck_7810_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_7803_);
                                    lean_dec(v___x_7800_);
                                    v___x_7805_ = lean_box(0);
                                    v_isShared_7806_ = v_isSharedCheck_7810_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7781_);
                    lean_dec_ref(v_xs_7741_);
                    lean_dec(v_declName_7735_);
                    return v___y_7783_;
                }
            }
            5 => {
                if v_isShared_7806_ == 0 {
                    v___x_7808_ = v___x_7805_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7809_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7809_, 0, v_a_7803_);
                    v___x_7808_ = v_reuseFailAlloc_7809_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7808_;
            }
            7 => {
                if lean_obj_tag(v___y_7819_) == 0 {
                    lean_dec_ref(v___y_7812_);
                    lean_dec(v_declName_7735_);
                    v_a_7820_ = lean_ctor_get(v___y_7819_, 0);
                    lean_inc(v_a_7820_);
                    lean_dec_ref_known(v___y_7819_, 1);
                    v_inst_7751_ = v_a_7820_;
                    v___y_7752_ = v___y_7816_;
                    v___y_7753_ = v___y_7818_;
                    v___y_7754_ = v___y_7814_;
                    v___y_7755_ = v___y_7815_;
                    state = 1;
                    continue;
                } else {
                    v_a_7821_ = lean_ctor_get(v___y_7819_, 0);
                    v___x_7822_ = l_Lean_Exception_isInterrupt(v_a_7821_);
                    if v___x_7822_ == 0 {
                        lean_inc(v_a_7821_);
                        v___x_7823_ = l_Lean_Exception_isRuntime(v_a_7821_);
                        v___y_7781_ = v___y_7812_;
                        v___y_7782_ = v___y_7813_;
                        v___y_7783_ = v___y_7819_;
                        v___y_7784_ = v___y_7814_;
                        v___y_7785_ = v___y_7815_;
                        v___y_7786_ = v___y_7816_;
                        v___y_7787_ = v___y_7817_;
                        v___y_7788_ = v___y_7818_;
                        v___y_7789_ = v___x_7823_;
                        state = 4;
                        continue;
                    } else {
                        v___y_7781_ = v___y_7812_;
                        v___y_7782_ = v___y_7813_;
                        v___y_7783_ = v___y_7819_;
                        v___y_7784_ = v___y_7814_;
                        v___y_7785_ = v___y_7815_;
                        v___y_7786_ = v___y_7816_;
                        v___y_7787_ = v___y_7817_;
                        v___y_7788_ = v___y_7818_;
                        v___y_7789_ = v___x_7822_;
                        state = 4;
                        continue;
                    }
                }
            }
            8 => {
                lean_inc_ref(v_type_7736_);
                v___x_7831_ = l_Lean_Meta_instantiateForall(
                    v_type_7736_,
                    v_xs_7741_,
                    v___y_7827_,
                    v___y_7828_,
                    v___y_7829_,
                    v___y_7830_,
                );
                if lean_obj_tag(v___x_7831_) == 0 {
                    match v_fixpointType_7737_ {
                        0 => {
                            lean_dec_ref(v___f_7739_);
                            lean_dec_ref(v___f_7738_);
                            v_a_7832_ = lean_ctor_get(v___x_7831_, 0);
                            lean_inc(v_a_7832_);
                            lean_dec_ref_known(v___x_7831_, 1);
                            v___x_7833_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2;
                            v___x_7834_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3;
                            lean_inc_ref(v_xs_7741_);
                            lean_inc(v_declName_7735_);
                            v___f_7835_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed as *mut core::ffi::c_void, 13, 5);
                            lean_closure_set(v___f_7835_, 0, v_declName_7735_);
                            lean_closure_set(v___f_7835_, 1, v_type_7736_);
                            lean_closure_set(v___f_7835_, 2, v_xs_7741_);
                            lean_closure_set(v___f_7835_, 3, v___x_7833_);
                            lean_closure_set(v___f_7835_, 4, v___x_7834_);
                            v___x_7836_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5;
                            v___x_7837_ = lean_unsigned_to_nat(1);
                            v___x_7838_ = lean_mk_empty_array_with_capacity(v___x_7837_);
                            v___x_7839_ = lean_array_push(v___x_7838_, v_a_7832_);
                            v___x_7840_ = l_Lean_Meta_mkAppM(
                                v___x_7836_,
                                v___x_7839_,
                                v___y_7827_,
                                v___y_7828_,
                                v___y_7829_,
                                v___y_7830_,
                            );
                            if lean_obj_tag(v___x_7840_) == 0 {
                                v_a_7841_ = lean_ctor_get(v___x_7840_, 0);
                                lean_inc(v_a_7841_);
                                lean_dec_ref_known(v___x_7840_, 1);
                                v___x_7842_ = lean_box(0);
                                v___x_7843_ = l_Lean_Meta_synthInstance(
                                    v_a_7841_,
                                    v___x_7842_,
                                    v___y_7827_,
                                    v___y_7828_,
                                    v___y_7829_,
                                    v___y_7830_,
                                );
                                v___y_7812_ = v___f_7835_;
                                v___y_7813_ = v___y_7825_;
                                v___y_7814_ = v___y_7829_;
                                v___y_7815_ = v___y_7830_;
                                v___y_7816_ = v___y_7827_;
                                v___y_7817_ = v___y_7826_;
                                v___y_7818_ = v___y_7828_;
                                v___y_7819_ = v___x_7843_;
                                state = 7;
                                continue;
                            } else {
                                v___y_7812_ = v___f_7835_;
                                v___y_7813_ = v___y_7825_;
                                v___y_7814_ = v___y_7829_;
                                v___y_7815_ = v___y_7830_;
                                v___y_7816_ = v___y_7827_;
                                v___y_7817_ = v___y_7826_;
                                v___y_7818_ = v___y_7828_;
                                v___y_7819_ = v___x_7840_;
                                state = 7;
                                continue;
                            }
                        }
                        1 => {
                            lean_dec_ref(v___f_7739_);
                            lean_dec_ref(v_type_7736_);
                            lean_dec(v_declName_7735_);
                            v_a_7844_ = lean_ctor_get(v___x_7831_, 0);
                            lean_inc(v_a_7844_);
                            lean_dec_ref_known(v___x_7831_, 1);
                            v___x_7845_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_a_7844_, v___f_7738_, v_isZero_7734_, v_isZero_7734_, v___y_7825_, v___y_7826_, v___y_7827_, v___y_7828_, v___y_7829_, v___y_7830_);
                            if lean_obj_tag(v___x_7845_) == 0 {
                                v_a_7846_ = lean_ctor_get(v___x_7845_, 0);
                                lean_inc(v_a_7846_);
                                lean_dec_ref_known(v___x_7845_, 1);
                                v_inst_7751_ = v_a_7846_;
                                v___y_7752_ = v___y_7827_;
                                v___y_7753_ = v___y_7828_;
                                v___y_7754_ = v___y_7829_;
                                v___y_7755_ = v___y_7830_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_xs_7741_);
                                return v___x_7845_;
                            }
                        }
                        _ => {
                            lean_dec_ref(v___f_7738_);
                            lean_dec_ref(v_type_7736_);
                            lean_dec(v_declName_7735_);
                            v_a_7847_ = lean_ctor_get(v___x_7831_, 0);
                            lean_inc(v_a_7847_);
                            lean_dec_ref_known(v___x_7831_, 1);
                            v___x_7848_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_a_7847_, v___f_7739_, v_isZero_7734_, v_isZero_7734_, v___y_7825_, v___y_7826_, v___y_7827_, v___y_7828_, v___y_7829_, v___y_7830_);
                            if lean_obj_tag(v___x_7848_) == 0 {
                                v_a_7849_ = lean_ctor_get(v___x_7848_, 0);
                                lean_inc(v_a_7849_);
                                lean_dec_ref_known(v___x_7848_, 1);
                                v_inst_7751_ = v_a_7849_;
                                v___y_7752_ = v___y_7827_;
                                v___y_7753_ = v___y_7828_;
                                v___y_7754_ = v___y_7829_;
                                v___y_7755_ = v___y_7830_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_xs_7741_);
                                return v___x_7848_;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_xs_7741_);
                    lean_dec_ref(v___f_7739_);
                    lean_dec_ref(v___f_7738_);
                    lean_dec_ref(v_type_7736_);
                    lean_dec(v_declName_7735_);
                    return v___x_7831_;
                }
            }
            9 => {
                if v_isShared_7870_ == 0 {
                    v___x_7872_ = v___x_7869_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7873_, 0, v_a_7867_);
                    v___x_7872_ = v_reuseFailAlloc_7873_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed(
    mut v_isZero_7875_: *mut LeanObject,
    mut v_declName_7876_: *mut LeanObject,
    mut v_type_7877_: *mut LeanObject,
    mut v_fixpointType_7878_: *mut LeanObject,
    mut v___f_7879_: *mut LeanObject,
    mut v___f_7880_: *mut LeanObject,
    mut v_value_7881_: *mut LeanObject,
    mut v_xs_7882_: *mut LeanObject,
    mut v___body_7883_: *mut LeanObject,
    mut v___y_7884_: *mut LeanObject,
    mut v___y_7885_: *mut LeanObject,
    mut v___y_7886_: *mut LeanObject,
    mut v___y_7887_: *mut LeanObject,
    mut v___y_7888_: *mut LeanObject,
    mut v___y_7889_: *mut LeanObject,
    mut v___y_7890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_7891_: u8 = 0;
    let mut v_fixpointType_boxed_7892_: u8 = 0;
    let mut v_res_7893_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_7891_ = (lean_unbox(v_isZero_7875_) as u8);
    v_fixpointType_boxed_7892_ = (lean_unbox(v_fixpointType_7878_) as u8);
    v_res_7893_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(
            v_isZero_boxed_7891_,
            v_declName_7876_,
            v_type_7877_,
            v_fixpointType_boxed_7892_,
            v___f_7879_,
            v___f_7880_,
            v_value_7881_,
            v_xs_7882_,
            v___body_7883_,
            v___y_7884_,
            v___y_7885_,
            v___y_7886_,
            v___y_7887_,
            v___y_7888_,
            v___y_7889_,
        );
    lean_dec(v___y_7889_);
    lean_dec_ref(v___y_7888_);
    lean_dec(v___y_7887_);
    lean_dec_ref(v___y_7886_);
    lean_dec(v___y_7885_);
    lean_dec_ref(v___y_7884_);
    return v_res_7893_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0()
-> *mut LeanObject {
    let mut v___x_7894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7895_: *mut LeanObject = core::ptr::null_mut();
    v___x_7894_ = lean_box(1);
    v___x_7895_ = l_Lean_MessageData_ofFormat(v___x_7894_);
    return v___x_7895_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3()
-> *mut LeanObject {
    let mut v___x_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut LeanObject = core::ptr::null_mut();
    v___x_7899_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2;
    v___x_7900_ = l_Lean_MessageData_ofFormat(v___x_7899_);
    return v___x_7900_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(
    mut v_x_7901_: *mut LeanObject,
    mut v_x_7902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_7903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7907_: u8 = 0;
    let mut v_before_7908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7911_: u8 = 0;
    let mut v___x_7912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7924_: u8 = 0;
    let mut v_unused_7925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7902_) == 0 {
                    return v_x_7901_;
                } else {
                    v_head_7903_ = lean_ctor_get(v_x_7902_, 0);
                    v_tail_7904_ = lean_ctor_get(v_x_7902_, 1);
                    v_isSharedCheck_7926_ = (!lean_is_exclusive(v_x_7902_)) as u8;
                    if v_isSharedCheck_7926_ == 0 {
                        v___x_7906_ = v_x_7902_;
                        v_isShared_7907_ = v_isSharedCheck_7926_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7904_);
                        lean_inc(v_head_7903_);
                        lean_dec(v_x_7902_);
                        v___x_7906_ = lean_box(0);
                        v_isShared_7907_ = v_isSharedCheck_7926_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_7908_ = lean_ctor_get(v_head_7903_, 0);
                v_isSharedCheck_7924_ = (!lean_is_exclusive(v_head_7903_)) as u8;
                if v_isSharedCheck_7924_ == 0 {
                    v_unused_7925_ = lean_ctor_get(v_head_7903_, 1);
                    lean_dec(v_unused_7925_);
                    v___x_7910_ = v_head_7903_;
                    v_isShared_7911_ = v_isSharedCheck_7924_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_7908_);
                    lean_dec(v_head_7903_);
                    v___x_7910_ = lean_box(0);
                    v_isShared_7911_ = v_isSharedCheck_7924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7912_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0);
                if v_isShared_7911_ == 0 {
                    lean_ctor_set_tag(v___x_7910_, 7);
                    lean_ctor_set(v___x_7910_, 1, v___x_7912_);
                    lean_ctor_set(v___x_7910_, 0, v_x_7901_);
                    v___x_7914_ = v___x_7910_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7923_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7923_, 0, v_x_7901_);
                    lean_ctor_set(v_reuseFailAlloc_7923_, 1, v___x_7912_);
                    v___x_7914_ = v_reuseFailAlloc_7923_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7915_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3);
                if v_isShared_7907_ == 0 {
                    lean_ctor_set_tag(v___x_7906_, 7);
                    lean_ctor_set(v___x_7906_, 1, v___x_7915_);
                    lean_ctor_set(v___x_7906_, 0, v___x_7914_);
                    v___x_7917_ = v___x_7906_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7922_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7922_, 0, v___x_7914_);
                    lean_ctor_set(v_reuseFailAlloc_7922_, 1, v___x_7915_);
                    v___x_7917_ = v_reuseFailAlloc_7922_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7918_ = l_Lean_MessageData_ofSyntax(v_before_7908_);
                v___x_7919_ = l_Lean_indentD(v___x_7918_);
                v___x_7920_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7920_, 0, v___x_7917_);
                lean_ctor_set(v___x_7920_, 1, v___x_7919_);
                v_x_7901_ = v___x_7920_;
                v_x_7902_ = v_tail_7904_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(
    mut v_opts_7927_: *mut LeanObject,
    mut v_opt_7928_: *mut LeanObject,
) -> u8 {
    let mut v_name_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_7931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut LeanObject = core::ptr::null_mut();
    v_name_7929_ = lean_ctor_get(v_opt_7928_, 0);
    v_defValue_7930_ = lean_ctor_get(v_opt_7928_, 1);
    v_map_7931_ = lean_ctor_get(v_opts_7927_, 0);
    v___x_7932_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_7931_,
            v_name_7929_,
        );
    if lean_obj_tag(v___x_7932_) == 0 {
        let mut v___x_7933_: u8 = 0;
        v___x_7933_ = (lean_unbox(v_defValue_7930_) as u8);
        return v___x_7933_;
    } else {
        let mut v_val_7934_: *mut LeanObject = core::ptr::null_mut();
        v_val_7934_ = lean_ctor_get(v___x_7932_, 0);
        lean_inc(v_val_7934_);
        lean_dec_ref_known(v___x_7932_, 1);
        if lean_obj_tag(v_val_7934_) == 1 {
            let mut v_v_7935_: u8 = 0;
            v_v_7935_ = lean_ctor_get_uint8(v_val_7934_, 0 as u32);
            lean_dec_ref_known(v_val_7934_, 0);
            return v_v_7935_;
        } else {
            let mut v___x_7936_: u8 = 0;
            lean_dec(v_val_7934_);
            v___x_7936_ = (lean_unbox(v_defValue_7930_) as u8);
            return v___x_7936_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10___boxed(
    mut v_opts_7937_: *mut LeanObject,
    mut v_opt_7938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7939_: u8 = 0;
    let mut v_r_7940_: *mut LeanObject = core::ptr::null_mut();
    v_res_7939_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(v_opts_7937_, v_opt_7938_);
    lean_dec_ref(v_opt_7938_);
    lean_dec_ref(v_opts_7937_);
    v_r_7940_ = lean_box((v_res_7939_) as usize);
    return v_r_7940_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut LeanObject = core::ptr::null_mut();
    v___x_7944_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1;
    v___x_7945_ = l_Lean_MessageData_ofFormat(v___x_7944_);
    return v___x_7945_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(
    mut v_msgData_7946_: *mut LeanObject,
    mut v_macroStack_7947_: *mut LeanObject,
    mut v___y_7948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_7950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7952_: u8 = 0;
    let mut v___x_7953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_7956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7959_: u8 = 0;
    let mut v___x_7960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7971_: u8 = 0;
    let mut v_unused_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_7950_ = lean_ctor_get(v___y_7948_, 2);
                v___x_7951_ = l_Lean_Elab_pp_macroStack;
                v___x_7952_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(v_options_7950_, v___x_7951_);
                if v___x_7952_ == 0 {
                    lean_dec(v_macroStack_7947_);
                    v___x_7953_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7953_, 0, v_msgData_7946_);
                    return v___x_7953_;
                } else {
                    if lean_obj_tag(v_macroStack_7947_) == 0 {
                        v___x_7954_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7954_, 0, v_msgData_7946_);
                        return v___x_7954_;
                    } else {
                        v_head_7955_ = lean_ctor_get(v_macroStack_7947_, 0);
                        lean_inc(v_head_7955_);
                        v_after_7956_ = lean_ctor_get(v_head_7955_, 1);
                        v_isSharedCheck_7971_ = (!lean_is_exclusive(v_head_7955_)) as u8;
                        if v_isSharedCheck_7971_ == 0 {
                            v_unused_7972_ = lean_ctor_get(v_head_7955_, 0);
                            lean_dec(v_unused_7972_);
                            v___x_7958_ = v_head_7955_;
                            v_isShared_7959_ = v_isSharedCheck_7971_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_7956_);
                            lean_dec(v_head_7955_);
                            v___x_7958_ = lean_box(0);
                            v_isShared_7959_ = v_isSharedCheck_7971_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7960_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0);
                if v_isShared_7959_ == 0 {
                    lean_ctor_set_tag(v___x_7958_, 7);
                    lean_ctor_set(v___x_7958_, 1, v___x_7960_);
                    lean_ctor_set(v___x_7958_, 0, v_msgData_7946_);
                    v___x_7962_ = v___x_7958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7970_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7970_, 0, v_msgData_7946_);
                    lean_ctor_set(v_reuseFailAlloc_7970_, 1, v___x_7960_);
                    v___x_7962_ = v_reuseFailAlloc_7970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7963_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2);
                v___x_7964_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7964_, 0, v___x_7962_);
                lean_ctor_set(v___x_7964_, 1, v___x_7963_);
                v___x_7965_ = l_Lean_MessageData_ofSyntax(v_after_7956_);
                v___x_7966_ = l_Lean_indentD(v___x_7965_);
                v_msgData_7967_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_7967_, 0, v___x_7964_);
                lean_ctor_set(v_msgData_7967_, 1, v___x_7966_);
                v___x_7968_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(v_msgData_7967_, v_macroStack_7947_);
                v___x_7969_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7969_, 0, v___x_7968_);
                return v___x_7969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___boxed(
    mut v_msgData_7973_: *mut LeanObject,
    mut v_macroStack_7974_: *mut LeanObject,
    mut v___y_7975_: *mut LeanObject,
    mut v___y_7976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7977_: *mut LeanObject = core::ptr::null_mut();
    v_res_7977_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_7973_, v_macroStack_7974_, v___y_7975_);
    lean_dec_ref(v___y_7975_);
    return v_res_7977_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(
    mut v_msg_7978_: *mut LeanObject,
    mut v___y_7979_: *mut LeanObject,
    mut v___y_7980_: *mut LeanObject,
    mut v___y_7981_: *mut LeanObject,
    mut v___y_7982_: *mut LeanObject,
    mut v___y_7983_: *mut LeanObject,
    mut v___y_7984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7995_: u8 = 0;
    let mut v___x_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7986_ = lean_ctor_get(v___y_7983_, 5);
                v___x_7987_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_7978_, v___y_7981_, v___y_7982_, v___y_7983_, v___y_7984_);
                v_a_7988_ = lean_ctor_get(v___x_7987_, 0);
                lean_inc(v_a_7988_);
                lean_dec_ref(v___x_7987_);
                v_macroStack_7989_ = lean_ctor_get(v___y_7979_, 1);
                v___x_7990_ = l_Lean_Elab_getBetterRef(v_ref_7986_, v_macroStack_7989_);
                lean_inc(v_macroStack_7989_);
                v___x_7991_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_a_7988_, v_macroStack_7989_, v___y_7983_);
                v_a_7992_ = lean_ctor_get(v___x_7991_, 0);
                v_isSharedCheck_8000_ = (!lean_is_exclusive(v___x_7991_)) as u8;
                if v_isSharedCheck_8000_ == 0 {
                    v___x_7994_ = v___x_7991_;
                    v_isShared_7995_ = v_isSharedCheck_8000_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7992_);
                    lean_dec(v___x_7991_);
                    v___x_7994_ = lean_box(0);
                    v_isShared_7995_ = v_isSharedCheck_8000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7996_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7996_, 0, v___x_7990_);
                lean_ctor_set(v___x_7996_, 1, v_a_7992_);
                if v_isShared_7995_ == 0 {
                    lean_ctor_set_tag(v___x_7994_, 1);
                    lean_ctor_set(v___x_7994_, 0, v___x_7996_);
                    v___x_7998_ = v___x_7994_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7999_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7999_, 0, v___x_7996_);
                    v___x_7998_ = v_reuseFailAlloc_7999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg___boxed(
    mut v_msg_8001_: *mut LeanObject,
    mut v___y_8002_: *mut LeanObject,
    mut v___y_8003_: *mut LeanObject,
    mut v___y_8004_: *mut LeanObject,
    mut v___y_8005_: *mut LeanObject,
    mut v___y_8006_: *mut LeanObject,
    mut v___y_8007_: *mut LeanObject,
    mut v___y_8008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8009_: *mut LeanObject = core::ptr::null_mut();
    v_res_8009_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(
        v_msg_8001_,
        v___y_8002_,
        v___y_8003_,
        v___y_8004_,
        v___y_8005_,
        v___y_8006_,
        v___y_8007_,
    );
    lean_dec(v___y_8007_);
    lean_dec_ref(v___y_8006_);
    lean_dec(v___y_8005_);
    lean_dec_ref(v___y_8004_);
    lean_dec(v___y_8003_);
    lean_dec_ref(v___y_8002_);
    return v_res_8009_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3()
-> *mut LeanObject {
    let mut v___x_8017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut LeanObject = core::ptr::null_mut();
    v___x_8017_ = lean_box(0);
    v___x_8018_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2;
    v___x_8019_ = l_Lean_mkConst(v___x_8018_, v___x_8017_);
    return v___x_8019_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5()
-> *mut LeanObject {
    let mut v___x_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: *mut LeanObject = core::ptr::null_mut();
    v___x_8021_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4;
    v___x_8022_ = l_Lean_stringToMessageData(v___x_8021_);
    return v___x_8022_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(
    mut v_xs_8023_: *mut LeanObject,
    mut v_e_8024_: *mut LeanObject,
    mut v___y_8025_: *mut LeanObject,
    mut v___y_8026_: *mut LeanObject,
    mut v___y_8027_: *mut LeanObject,
    mut v___y_8028_: *mut LeanObject,
    mut v___y_8029_: *mut LeanObject,
    mut v___y_8030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8035_: u8 = 0;
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8041_: u8 = 0;
    let mut v___x_8043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8035_ = l_Lean_Expr_isProp(v_e_8024_);
                if v___x_8035_ == 0 {
                    lean_dec_ref(v_xs_8023_);
                    v___x_8036_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5);
                    v___x_8037_ =
                        l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(
                            v___x_8036_,
                            v___y_8025_,
                            v___y_8026_,
                            v___y_8027_,
                            v___y_8028_,
                            v___y_8029_,
                            v___y_8030_,
                        );
                    v_a_8038_ = lean_ctor_get(v___x_8037_, 0);
                    v_isSharedCheck_8045_ = (!lean_is_exclusive(v___x_8037_)) as u8;
                    if v_isSharedCheck_8045_ == 0 {
                        v___x_8040_ = v___x_8037_;
                        v_isShared_8041_ = v_isSharedCheck_8045_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8038_);
                        lean_dec(v___x_8037_);
                        v___x_8040_ = lean_box(0);
                        v_isShared_8041_ = v_isSharedCheck_8045_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8033_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3);
                v___x_8034_ = l_Lean_Meta_mkInstPiOfInstsForall(
                    v_xs_8023_,
                    v___x_8033_,
                    v___y_8027_,
                    v___y_8028_,
                    v___y_8029_,
                    v___y_8030_,
                );
                return v___x_8034_;
            }
            2 => {
                if v_isShared_8041_ == 0 {
                    v___x_8043_ = v___x_8040_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8044_, 0, v_a_8038_);
                    v___x_8043_ = v_reuseFailAlloc_8044_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___boxed(
    mut v_xs_8046_: *mut LeanObject,
    mut v_e_8047_: *mut LeanObject,
    mut v___y_8048_: *mut LeanObject,
    mut v___y_8049_: *mut LeanObject,
    mut v___y_8050_: *mut LeanObject,
    mut v___y_8051_: *mut LeanObject,
    mut v___y_8052_: *mut LeanObject,
    mut v___y_8053_: *mut LeanObject,
    mut v___y_8054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8055_: *mut LeanObject = core::ptr::null_mut();
    v_res_8055_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(
            v_xs_8046_,
            v_e_8047_,
            v___y_8048_,
            v___y_8049_,
            v___y_8050_,
            v___y_8051_,
            v___y_8052_,
            v___y_8053_,
        );
    lean_dec(v___y_8053_);
    lean_dec_ref(v___y_8052_);
    lean_dec(v___y_8051_);
    lean_dec_ref(v___y_8050_);
    lean_dec(v___y_8049_);
    lean_dec_ref(v___y_8048_);
    lean_dec_ref(v_e_8047_);
    return v_res_8055_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_8062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8064_: *mut LeanObject = core::ptr::null_mut();
    v___x_8062_ = lean_box(0);
    v___x_8063_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1;
    v___x_8064_ = l_Lean_mkConst(v___x_8063_, v___x_8062_);
    return v___x_8064_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8067_: *mut LeanObject = core::ptr::null_mut();
    v___x_8066_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3;
    v___x_8067_ = l_Lean_stringToMessageData(v___x_8066_);
    return v___x_8067_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(
    mut v_xs_8068_: *mut LeanObject,
    mut v_e_8069_: *mut LeanObject,
    mut v___y_8070_: *mut LeanObject,
    mut v___y_8071_: *mut LeanObject,
    mut v___y_8072_: *mut LeanObject,
    mut v___y_8073_: *mut LeanObject,
    mut v___y_8074_: *mut LeanObject,
    mut v___y_8075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8080_: u8 = 0;
    let mut v___x_8081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8086_: u8 = 0;
    let mut v___x_8088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8080_ = l_Lean_Expr_isProp(v_e_8069_);
                if v___x_8080_ == 0 {
                    lean_dec_ref(v_xs_8068_);
                    v___x_8081_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4);
                    v___x_8082_ =
                        l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(
                            v___x_8081_,
                            v___y_8070_,
                            v___y_8071_,
                            v___y_8072_,
                            v___y_8073_,
                            v___y_8074_,
                            v___y_8075_,
                        );
                    v_a_8083_ = lean_ctor_get(v___x_8082_, 0);
                    v_isSharedCheck_8090_ = (!lean_is_exclusive(v___x_8082_)) as u8;
                    if v_isSharedCheck_8090_ == 0 {
                        v___x_8085_ = v___x_8082_;
                        v_isShared_8086_ = v_isSharedCheck_8090_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8083_);
                        lean_dec(v___x_8082_);
                        v___x_8085_ = lean_box(0);
                        v_isShared_8086_ = v_isSharedCheck_8090_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8078_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2);
                v___x_8079_ = l_Lean_Meta_mkInstPiOfInstsForall(
                    v_xs_8068_,
                    v___x_8078_,
                    v___y_8072_,
                    v___y_8073_,
                    v___y_8074_,
                    v___y_8075_,
                );
                return v___x_8079_;
            }
            2 => {
                if v_isShared_8086_ == 0 {
                    v___x_8088_ = v___x_8085_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8089_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8089_, 0, v_a_8083_);
                    v___x_8088_ = v_reuseFailAlloc_8089_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___boxed(
    mut v_xs_8091_: *mut LeanObject,
    mut v_e_8092_: *mut LeanObject,
    mut v___y_8093_: *mut LeanObject,
    mut v___y_8094_: *mut LeanObject,
    mut v___y_8095_: *mut LeanObject,
    mut v___y_8096_: *mut LeanObject,
    mut v___y_8097_: *mut LeanObject,
    mut v___y_8098_: *mut LeanObject,
    mut v___y_8099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8100_: *mut LeanObject = core::ptr::null_mut();
    v_res_8100_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(
            v_xs_8091_,
            v_e_8092_,
            v___y_8093_,
            v___y_8094_,
            v___y_8095_,
            v___y_8096_,
            v___y_8097_,
            v___y_8098_,
        );
    lean_dec(v___y_8098_);
    lean_dec_ref(v___y_8097_);
    lean_dec(v___y_8096_);
    lean_dec_ref(v___y_8095_);
    lean_dec(v___y_8094_);
    lean_dec_ref(v___y_8093_);
    lean_dec_ref(v_e_8092_);
    return v_res_8100_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(
    mut v_hints_8103_: *mut LeanObject,
    mut v_as_8104_: *mut LeanObject,
    mut v_i_8105_: *mut LeanObject,
    mut v_j_8106_: *mut LeanObject,
    mut v_bs_8107_: *mut LeanObject,
    mut v___y_8108_: *mut LeanObject,
    mut v___y_8109_: *mut LeanObject,
    mut v___y_8110_: *mut LeanObject,
    mut v___y_8111_: *mut LeanObject,
    mut v___y_8112_: *mut LeanObject,
    mut v___y_8113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_8115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_8116_: u8 = 0;
    let mut v___x_8117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixpointType_8121_: u8 = 0;
    let mut v___x_8122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_8123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_8125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_8126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_8127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_8129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_8130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_8132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_8135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_8136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_8137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_8138_: u8 = 0;
    let mut v_cancelTk_x3f_8139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_8140_: u8 = 0;
    let mut v_inheritedTraceOptions_8141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_8151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_8152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8159_: u8 = 0;
    let mut v___x_8161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_8115_ = lean_unsigned_to_nat(0);
                v_isZero_8116_ = lean_nat_dec_eq(v_i_8105_, v_zero_8115_);
                if v_isZero_8116_ == 1 {
                    lean_dec(v_j_8106_);
                    lean_dec(v_i_8105_);
                    v___x_8117_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8117_, 0, v_bs_8107_);
                    return v___x_8117_;
                } else {
                    v___x_8118_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
                    v___x_8119_ = lean_array_get_borrowed(v___x_8118_, v_hints_8103_, v_j_8106_);
                    v_ref_8120_ = lean_ctor_get(v___x_8119_, 0);
                    v_fixpointType_8121_ = lean_ctor_get_uint8(
                        v___x_8119_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___x_8122_ = lean_array_fget_borrowed(v_as_8104_, v_j_8106_);
                    v_declName_8123_ = lean_ctor_get(v___x_8122_, 3);
                    v_type_8124_ = lean_ctor_get(v___x_8122_, 6);
                    v_value_8125_ = lean_ctor_get(v___x_8122_, 7);
                    v_fileName_8126_ = lean_ctor_get(v___y_8112_, 0);
                    v_fileMap_8127_ = lean_ctor_get(v___y_8112_, 1);
                    v_options_8128_ = lean_ctor_get(v___y_8112_, 2);
                    v_currRecDepth_8129_ = lean_ctor_get(v___y_8112_, 3);
                    v_maxRecDepth_8130_ = lean_ctor_get(v___y_8112_, 4);
                    v_ref_8131_ = lean_ctor_get(v___y_8112_, 5);
                    v_currNamespace_8132_ = lean_ctor_get(v___y_8112_, 6);
                    v_openDecls_8133_ = lean_ctor_get(v___y_8112_, 7);
                    v_initHeartbeats_8134_ = lean_ctor_get(v___y_8112_, 8);
                    v_maxHeartbeats_8135_ = lean_ctor_get(v___y_8112_, 9);
                    v_quotContext_8136_ = lean_ctor_get(v___y_8112_, 10);
                    v_currMacroScope_8137_ = lean_ctor_get(v___y_8112_, 11);
                    v_diag_8138_ = lean_ctor_get_uint8(
                        v___y_8112_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_8139_ = lean_ctor_get(v___y_8112_, 12);
                    v_suppressElabErrors_8140_ = lean_ctor_get_uint8(
                        v___y_8112_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_8141_ = lean_ctor_get(v___y_8112_, 13);
                    v___f_8142_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0;
                    v___f_8143_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1;
                    v___x_8144_ = lean_box((v_isZero_8116_) as usize);
                    v___x_8145_ = lean_box((v_fixpointType_8121_) as usize);
                    lean_inc_ref_n(v_value_8125_, 2);
                    lean_inc_ref(v_type_8124_);
                    lean_inc(v_declName_8123_);
                    v___f_8146_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed as *mut core::ffi::c_void, 16, 7);
                    lean_closure_set(v___f_8146_, 0, v___x_8144_);
                    lean_closure_set(v___f_8146_, 1, v_declName_8123_);
                    lean_closure_set(v___f_8146_, 2, v_type_8124_);
                    lean_closure_set(v___f_8146_, 3, v___x_8145_);
                    lean_closure_set(v___f_8146_, 4, v___f_8142_);
                    lean_closure_set(v___f_8146_, 5, v___f_8143_);
                    lean_closure_set(v___f_8146_, 6, v_value_8125_);
                    v_ref_8147_ = l_Lean_replaceRef(v_ref_8120_, v_ref_8131_);
                    lean_inc_ref(v_inheritedTraceOptions_8141_);
                    lean_inc(v_cancelTk_x3f_8139_);
                    lean_inc(v_currMacroScope_8137_);
                    lean_inc(v_quotContext_8136_);
                    lean_inc(v_maxHeartbeats_8135_);
                    lean_inc(v_initHeartbeats_8134_);
                    lean_inc(v_openDecls_8133_);
                    lean_inc(v_currNamespace_8132_);
                    lean_inc(v_maxRecDepth_8130_);
                    lean_inc(v_currRecDepth_8129_);
                    lean_inc_ref(v_options_8128_);
                    lean_inc_ref(v_fileMap_8127_);
                    lean_inc_ref(v_fileName_8126_);
                    v___x_8148_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v___x_8148_, 0, v_fileName_8126_);
                    lean_ctor_set(v___x_8148_, 1, v_fileMap_8127_);
                    lean_ctor_set(v___x_8148_, 2, v_options_8128_);
                    lean_ctor_set(v___x_8148_, 3, v_currRecDepth_8129_);
                    lean_ctor_set(v___x_8148_, 4, v_maxRecDepth_8130_);
                    lean_ctor_set(v___x_8148_, 5, v_ref_8147_);
                    lean_ctor_set(v___x_8148_, 6, v_currNamespace_8132_);
                    lean_ctor_set(v___x_8148_, 7, v_openDecls_8133_);
                    lean_ctor_set(v___x_8148_, 8, v_initHeartbeats_8134_);
                    lean_ctor_set(v___x_8148_, 9, v_maxHeartbeats_8135_);
                    lean_ctor_set(v___x_8148_, 10, v_quotContext_8136_);
                    lean_ctor_set(v___x_8148_, 11, v_currMacroScope_8137_);
                    lean_ctor_set(v___x_8148_, 12, v_cancelTk_x3f_8139_);
                    lean_ctor_set(v___x_8148_, 13, v_inheritedTraceOptions_8141_);
                    lean_ctor_set_uint8(
                        v___x_8148_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        v_diag_8138_,
                    );
                    lean_ctor_set_uint8(
                        v___x_8148_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_8140_,
                    );
                    v___x_8149_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_value_8125_, v___f_8146_, v_isZero_8116_, v___y_8108_, v___y_8109_, v___y_8110_, v___y_8111_, v___x_8148_, v___y_8113_);
                    lean_dec_ref_known(v___x_8148_, 14);
                    if lean_obj_tag(v___x_8149_) == 0 {
                        v_a_8150_ = lean_ctor_get(v___x_8149_, 0);
                        lean_inc(v_a_8150_);
                        lean_dec_ref_known(v___x_8149_, 1);
                        v_one_8151_ = lean_unsigned_to_nat(1);
                        v_n_8152_ = lean_nat_sub(v_i_8105_, v_one_8151_);
                        lean_dec(v_i_8105_);
                        v___x_8153_ = lean_nat_add(v_j_8106_, v_one_8151_);
                        lean_dec(v_j_8106_);
                        v___x_8154_ = lean_array_push(v_bs_8107_, v_a_8150_);
                        v_i_8105_ = v_n_8152_;
                        v_j_8106_ = v___x_8153_;
                        v_bs_8107_ = v___x_8154_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_8107_);
                        lean_dec(v_j_8106_);
                        lean_dec(v_i_8105_);
                        v_a_8156_ = lean_ctor_get(v___x_8149_, 0);
                        v_isSharedCheck_8163_ = (!lean_is_exclusive(v___x_8149_)) as u8;
                        if v_isSharedCheck_8163_ == 0 {
                            v___x_8158_ = v___x_8149_;
                            v_isShared_8159_ = v_isSharedCheck_8163_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8156_);
                            lean_dec(v___x_8149_);
                            v___x_8158_ = lean_box(0);
                            v_isShared_8159_ = v_isSharedCheck_8163_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8159_ == 0 {
                    v___x_8161_ = v___x_8158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8162_, 0, v_a_8156_);
                    v___x_8161_ = v_reuseFailAlloc_8162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___boxed(
    mut v_hints_8164_: *mut LeanObject,
    mut v_as_8165_: *mut LeanObject,
    mut v_i_8166_: *mut LeanObject,
    mut v_j_8167_: *mut LeanObject,
    mut v_bs_8168_: *mut LeanObject,
    mut v___y_8169_: *mut LeanObject,
    mut v___y_8170_: *mut LeanObject,
    mut v___y_8171_: *mut LeanObject,
    mut v___y_8172_: *mut LeanObject,
    mut v___y_8173_: *mut LeanObject,
    mut v___y_8174_: *mut LeanObject,
    mut v___y_8175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8176_: *mut LeanObject = core::ptr::null_mut();
    v_res_8176_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(
        v_hints_8164_,
        v_as_8165_,
        v_i_8166_,
        v_j_8167_,
        v_bs_8168_,
        v___y_8169_,
        v___y_8170_,
        v___y_8171_,
        v___y_8172_,
        v___y_8173_,
        v___y_8174_,
    );
    lean_dec(v___y_8174_);
    lean_dec_ref(v___y_8173_);
    lean_dec(v___y_8172_);
    lean_dec_ref(v___y_8171_);
    lean_dec(v___y_8170_);
    lean_dec_ref(v___y_8169_);
    lean_dec_ref(v_as_8165_);
    lean_dec_ref(v_hints_8164_);
    return v_res_8176_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(
    mut v_as_8177_: *mut LeanObject,
    mut v_i_8178_: usize,
    mut v_stop_8179_: usize,
) -> u8 {
    let mut v___x_8180_: u8 = 0;
    let mut v___x_8181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixpointType_8182_: u8 = 0;
    let mut v___x_8183_: u8 = 0;
    let mut v___x_8184_: usize = 0;
    let mut v___x_8185_: usize = 0;
    let mut v___x_8187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8180_ = lean_usize_dec_eq(v_i_8178_, v_stop_8179_);
                if v___x_8180_ == 0 {
                    v___x_8181_ = lean_array_uget_borrowed(v_as_8177_, v_i_8178_);
                    v_fixpointType_8182_ = lean_ctor_get_uint8(
                        v___x_8181_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___x_8183_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_8182_);
                    if v___x_8183_ == 0 {
                        v___x_8184_ = 1usize;
                        v___x_8185_ = lean_usize_add(v_i_8178_, v___x_8184_);
                        v_i_8178_ = v___x_8185_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_8183_;
                    }
                } else {
                    v___x_8187_ = 0;
                    return v___x_8187_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31___boxed(
    mut v_as_8188_: *mut LeanObject,
    mut v_i_8189_: *mut LeanObject,
    mut v_stop_8190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_8191_: usize = 0;
    let mut v_stop_boxed_8192_: usize = 0;
    let mut v_res_8193_: u8 = 0;
    let mut v_r_8194_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_8191_ = lean_unbox_usize(v_i_8189_);
    lean_dec(v_i_8189_);
    v_stop_boxed_8192_ = lean_unbox_usize(v_stop_8190_);
    lean_dec(v_stop_8190_);
    v_res_8193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(v_as_8188_, v_i_boxed_8191_, v_stop_boxed_8192_);
    lean_dec_ref(v_as_8188_);
    v_r_8194_ = lean_box((v_res_8193_) as usize);
    return v_r_8194_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(
    mut v_as_8195_: *mut LeanObject,
    mut v_i_8196_: usize,
    mut v_stop_8197_: usize,
) -> u8 {
    let mut v___x_8198_: u8 = 0;
    v___x_8198_ = lean_usize_dec_eq(v_i_8196_, v_stop_8197_);
    if v___x_8198_ == 0 {
        let mut v___x_8199_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fixpointType_8200_: u8 = 0;
        let mut v___x_8201_: u8 = 0;
        v___x_8199_ = lean_array_uget_borrowed(v_as_8195_, v_i_8196_);
        v_fixpointType_8200_ = lean_ctor_get_uint8(
            v___x_8199_,
            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        );
        v___x_8201_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_8200_);
        if v___x_8201_ == 0 {
            let mut v___x_8202_: usize = 0;
            let mut v___x_8203_: usize = 0;
            let mut v___x_8204_: u8 = 0;
            v___x_8202_ = 1usize;
            v___x_8203_ = lean_usize_add(v_i_8196_, v___x_8202_);
            v___x_8204_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(v_as_8195_, v___x_8203_, v_stop_8197_);
            return v___x_8204_;
        } else {
            return v___x_8201_;
        }
    } else {
        let mut v___x_8205_: u8 = 0;
        v___x_8205_ = 0;
        return v___x_8205_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26___boxed(
    mut v_as_8206_: *mut LeanObject,
    mut v_i_8207_: *mut LeanObject,
    mut v_stop_8208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_8209_: usize = 0;
    let mut v_stop_boxed_8210_: usize = 0;
    let mut v_res_8211_: u8 = 0;
    let mut v_r_8212_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_8209_ = lean_unbox_usize(v_i_8207_);
    lean_dec(v_i_8207_);
    v_stop_boxed_8210_ = lean_unbox_usize(v_stop_8208_);
    lean_dec(v_stop_8208_);
    v_res_8211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(v_as_8206_, v_i_boxed_8209_, v_stop_boxed_8210_);
    lean_dec_ref(v_as_8206_);
    v_r_8212_ = lean_box((v_res_8211_) as usize);
    return v_r_8212_;
}
pub unsafe fn _init_l_Lean_Elab_partialFixpoint___closed__1() -> *mut LeanObject {
    let mut v___x_8214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8219_: *mut LeanObject = core::ptr::null_mut();
    v___x_8214_ = l_Lean_Elab_partialFixpoint___closed__0;
    v___x_8215_ = lean_unsigned_to_nat(2);
    v___x_8216_ = lean_unsigned_to_nat(82);
    v___x_8217_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7;
    v___x_8218_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0;
    v___x_8219_ = l_mkPanicMessageWithDecl(
        v___x_8218_,
        v___x_8217_,
        v___x_8216_,
        v___x_8215_,
        v___x_8214_,
    );
    return v___x_8219_;
}
pub unsafe fn _init_l_Lean_Elab_partialFixpoint___closed__3() -> *mut LeanObject {
    let mut v___x_8221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8226_: *mut LeanObject = core::ptr::null_mut();
    v___x_8221_ = l_Lean_Elab_partialFixpoint___closed__2;
    v___x_8222_ = lean_unsigned_to_nat(4);
    v___x_8223_ = lean_unsigned_to_nat(86);
    v___x_8224_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7;
    v___x_8225_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0;
    v___x_8226_ = l_mkPanicMessageWithDecl(
        v___x_8225_,
        v___x_8224_,
        v___x_8223_,
        v___x_8222_,
        v___x_8221_,
    );
    return v___x_8226_;
}
pub unsafe fn l_Lean_Elab_partialFixpoint(
    mut v_docCtx_8229_: *mut LeanObject,
    mut v_preDefs_8230_: *mut LeanObject,
    mut v_a_8231_: *mut LeanObject,
    mut v_a_8232_: *mut LeanObject,
    mut v_a_8233_: *mut LeanObject,
    mut v_a_8234_: *mut LeanObject,
    mut v_a_8235_: *mut LeanObject,
    mut v_a_8236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hints_8240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8242_: u8 = 0;
    let mut v___y_8244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8253_: usize = 0;
    let mut v___x_8254_: usize = 0;
    let mut v___x_8255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perms_8258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8272_: u8 = 0;
    let mut v___x_8274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8276_: u8 = 0;
    let mut v_a_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8280_: u8 = 0;
    let mut v___x_8282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8284_: u8 = 0;
    let mut v___x_8285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8287_: u8 = 0;
    let mut v___x_8288_: usize = 0;
    let mut v___x_8289_: usize = 0;
    let mut v___x_8290_: u8 = 0;
    let mut v___x_8291_: u8 = 0;
    let mut v___x_8292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8293_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8238_ = lean_unsigned_to_nat(0);
                v___x_8239_ = lean_array_get_size(v_preDefs_8230_);
                v_hints_8240_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(
                    v_preDefs_8230_,
                    v___x_8238_,
                    v___x_8239_,
                );
                v___x_8241_ = lean_array_get_size(v_hints_8240_);
                v___x_8242_ = lean_nat_dec_eq(v___x_8239_, v___x_8241_);
                if v___x_8242_ == 0 {
                    lean_dec_ref(v_hints_8240_);
                    lean_dec_ref(v_preDefs_8230_);
                    lean_dec_ref(v_docCtx_8229_);
                    v___x_8285_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_partialFixpoint___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Elab_partialFixpoint___closed__1_once),
                        _init_l_Lean_Elab_partialFixpoint___closed__1,
                    );
                    v___x_8286_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(
                        v___x_8285_,
                        v_a_8231_,
                        v_a_8232_,
                        v_a_8233_,
                        v_a_8234_,
                        v_a_8235_,
                        v_a_8236_,
                    );
                    return v___x_8286_;
                } else {
                    v___x_8287_ = lean_nat_dec_lt(v___x_8238_, v___x_8241_);
                    if v___x_8287_ == 0 {
                        v___y_8244_ = v_a_8231_;
                        v___y_8245_ = v_a_8232_;
                        v___y_8246_ = v_a_8233_;
                        v___y_8247_ = v_a_8234_;
                        v___y_8248_ = v_a_8235_;
                        v___y_8249_ = v_a_8236_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_8287_ == 0 {
                            v___y_8244_ = v_a_8231_;
                            v___y_8245_ = v_a_8232_;
                            v___y_8246_ = v_a_8233_;
                            v___y_8247_ = v_a_8234_;
                            v___y_8248_ = v_a_8235_;
                            v___y_8249_ = v_a_8236_;
                            state = 1;
                            continue;
                        } else {
                            v___x_8288_ = 0usize;
                            v___x_8289_ = lean_usize_of_nat(v___x_8241_);
                            v___x_8290_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(v_hints_8240_, v___x_8288_, v___x_8289_);
                            if v___x_8290_ == 0 {
                                v___y_8244_ = v_a_8231_;
                                v___y_8245_ = v_a_8232_;
                                v___y_8246_ = v_a_8233_;
                                v___y_8247_ = v_a_8234_;
                                v___y_8248_ = v_a_8235_;
                                v___y_8249_ = v_a_8236_;
                                state = 1;
                                continue;
                            } else {
                                if v___x_8287_ == 0 {
                                    v___y_8244_ = v_a_8231_;
                                    v___y_8245_ = v_a_8232_;
                                    v___y_8246_ = v_a_8233_;
                                    v___y_8247_ = v_a_8234_;
                                    v___y_8248_ = v_a_8235_;
                                    v___y_8249_ = v_a_8236_;
                                    state = 1;
                                    continue;
                                } else {
                                    if v___x_8287_ == 0 {
                                        v___y_8244_ = v_a_8231_;
                                        v___y_8245_ = v_a_8232_;
                                        v___y_8246_ = v_a_8233_;
                                        v___y_8247_ = v_a_8234_;
                                        v___y_8248_ = v_a_8235_;
                                        v___y_8249_ = v_a_8236_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_8291_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v___x_8290_, v_hints_8240_, v___x_8288_, v___x_8289_);
                                        if v___x_8291_ == 0 {
                                            v___y_8244_ = v_a_8231_;
                                            v___y_8245_ = v_a_8232_;
                                            v___y_8246_ = v_a_8233_;
                                            v___y_8247_ = v_a_8234_;
                                            v___y_8248_ = v_a_8235_;
                                            v___y_8249_ = v_a_8236_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v_hints_8240_);
                                            lean_dec_ref(v_preDefs_8230_);
                                            lean_dec_ref(v_docCtx_8229_);
                                            v___x_8292_ = lean_obj_once(
                                                core::ptr::addr_of_mut!(
                                                    l_Lean_Elab_partialFixpoint___closed__3
                                                ),
                                                core::ptr::addr_of_mut!(
                                                    l_Lean_Elab_partialFixpoint___closed__3_once
                                                ),
                                                _init_l_Lean_Elab_partialFixpoint___closed__3,
                                            );
                                            v___x_8293_ =
                                                l_panic___at___00Lean_Elab_partialFixpoint_spec__25(
                                                    v___x_8292_,
                                                    v_a_8231_,
                                                    v_a_8232_,
                                                    v_a_8233_,
                                                    v_a_8234_,
                                                    v_a_8235_,
                                                    v_a_8236_,
                                                );
                                            return v___x_8293_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_8250_ = lean_mk_empty_array_with_capacity(v___x_8239_);
                lean_inc_ref(v___x_8250_);
                v___x_8251_ =
                    l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(
                        v_hints_8240_,
                        v_preDefs_8230_,
                        v___x_8239_,
                        v___x_8238_,
                        v___x_8250_,
                        v___y_8244_,
                        v___y_8245_,
                        v___y_8246_,
                        v___y_8247_,
                        v___y_8248_,
                        v___y_8249_,
                    );
                if lean_obj_tag(v___x_8251_) == 0 {
                    v_a_8252_ = lean_ctor_get(v___x_8251_, 0);
                    lean_inc(v_a_8252_);
                    lean_dec_ref_known(v___x_8251_, 1);
                    v_sz_8253_ = lean_array_size(v_preDefs_8230_);
                    v___x_8254_ = 0usize;
                    lean_inc_ref_n(v_preDefs_8230_, 2);
                    v___x_8255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(v_sz_8253_, v___x_8254_, v_preDefs_8230_);
                    v___x_8256_ = l_Lean_Elab_getFixedParamPerms(
                        v_preDefs_8230_,
                        v___y_8246_,
                        v___y_8247_,
                        v___y_8248_,
                        v___y_8249_,
                    );
                    if lean_obj_tag(v___x_8256_) == 0 {
                        v_a_8257_ = lean_ctor_get(v___x_8256_, 0);
                        lean_inc(v_a_8257_);
                        lean_dec_ref_known(v___x_8256_, 1);
                        v_perms_8258_ = lean_ctor_get(v_a_8257_, 1);
                        lean_inc_ref(v_perms_8258_);
                        v___x_8259_ = l_Lean_Elab_instInhabitedPreDefinition_default;
                        v___x_8260_ = lean_array_get(v___x_8259_, v_preDefs_8230_, v___x_8238_);
                        v_type_8261_ = lean_ctor_get(v___x_8260_, 6);
                        lean_inc_ref(v_type_8261_);
                        v___x_8262_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
                        v___x_8263_ = lean_array_get(v___x_8262_, v_perms_8258_, v___x_8238_);
                        v___x_8264_ = l_Lean_Elab_partialFixpoint___boxed__const__1;
                        v___x_8265_ = lean_box((v___x_8242_) as usize);
                        v___x_8266_ = lean_box_usize(v_sz_8253_);
                        v___f_8267_ = lean_alloc_closure(
                            l_Lean_Elab_partialFixpoint___lam__0___boxed as *mut core::ffi::c_void,
                            22,
                            14,
                        );
                        lean_closure_set(v___f_8267_, 0, v_a_8252_);
                        lean_closure_set(v___f_8267_, 1, v_perms_8258_);
                        lean_closure_set(v___f_8267_, 2, v___x_8238_);
                        lean_closure_set(v___f_8267_, 3, v_preDefs_8230_);
                        lean_closure_set(v___f_8267_, 4, v___x_8239_);
                        lean_closure_set(v___f_8267_, 5, v___x_8250_);
                        lean_closure_set(v___f_8267_, 6, v___x_8264_);
                        lean_closure_set(v___f_8267_, 7, v___x_8255_);
                        lean_closure_set(v___f_8267_, 8, v_a_8257_);
                        lean_closure_set(v___f_8267_, 9, v___x_8265_);
                        lean_closure_set(v___f_8267_, 10, v_hints_8240_);
                        lean_closure_set(v___f_8267_, 11, v___x_8260_);
                        lean_closure_set(v___f_8267_, 12, v_docCtx_8229_);
                        lean_closure_set(v___f_8267_, 13, v___x_8266_);
                        v___x_8268_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v___x_8263_, v_type_8261_, v___f_8267_, v___y_8244_, v___y_8245_, v___y_8246_, v___y_8247_, v___y_8248_, v___y_8249_);
                        return v___x_8268_;
                    } else {
                        lean_dec_ref(v___x_8255_);
                        lean_dec(v_a_8252_);
                        lean_dec_ref(v___x_8250_);
                        lean_dec_ref(v_hints_8240_);
                        lean_dec_ref(v_preDefs_8230_);
                        lean_dec_ref(v_docCtx_8229_);
                        v_a_8269_ = lean_ctor_get(v___x_8256_, 0);
                        v_isSharedCheck_8276_ = (!lean_is_exclusive(v___x_8256_)) as u8;
                        if v_isSharedCheck_8276_ == 0 {
                            v___x_8271_ = v___x_8256_;
                            v_isShared_8272_ = v_isSharedCheck_8276_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_8269_);
                            lean_dec(v___x_8256_);
                            v___x_8271_ = lean_box(0);
                            v_isShared_8272_ = v_isSharedCheck_8276_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_8250_);
                    lean_dec_ref(v_hints_8240_);
                    lean_dec_ref(v_preDefs_8230_);
                    lean_dec_ref(v_docCtx_8229_);
                    v_a_8277_ = lean_ctor_get(v___x_8251_, 0);
                    v_isSharedCheck_8284_ = (!lean_is_exclusive(v___x_8251_)) as u8;
                    if v_isSharedCheck_8284_ == 0 {
                        v___x_8279_ = v___x_8251_;
                        v_isShared_8280_ = v_isSharedCheck_8284_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8277_);
                        lean_dec(v___x_8251_);
                        v___x_8279_ = lean_box(0);
                        v_isShared_8280_ = v_isSharedCheck_8284_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8272_ == 0 {
                    v___x_8274_ = v___x_8271_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8275_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8275_, 0, v_a_8269_);
                    v___x_8274_ = v_reuseFailAlloc_8275_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8274_;
            }
            4 => {
                if v_isShared_8280_ == 0 {
                    v___x_8282_ = v___x_8279_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8283_, 0, v_a_8277_);
                    v___x_8282_ = v_reuseFailAlloc_8283_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_partialFixpoint___boxed(
    mut v_docCtx_8294_: *mut LeanObject,
    mut v_preDefs_8295_: *mut LeanObject,
    mut v_a_8296_: *mut LeanObject,
    mut v_a_8297_: *mut LeanObject,
    mut v_a_8298_: *mut LeanObject,
    mut v_a_8299_: *mut LeanObject,
    mut v_a_8300_: *mut LeanObject,
    mut v_a_8301_: *mut LeanObject,
    mut v_a_8302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8303_: *mut LeanObject = core::ptr::null_mut();
    v_res_8303_ = l_Lean_Elab_partialFixpoint(
        v_docCtx_8294_,
        v_preDefs_8295_,
        v_a_8296_,
        v_a_8297_,
        v_a_8298_,
        v_a_8299_,
        v_a_8300_,
        v_a_8301_,
    );
    lean_dec(v_a_8301_);
    lean_dec_ref(v_a_8300_);
    lean_dec(v_a_8299_);
    lean_dec_ref(v_a_8298_);
    lean_dec(v_a_8297_);
    lean_dec_ref(v_a_8296_);
    return v_res_8303_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(
    mut v_00_u03b1_8304_: *mut LeanObject,
    mut v_msg_8305_: *mut LeanObject,
    mut v___y_8306_: *mut LeanObject,
    mut v___y_8307_: *mut LeanObject,
    mut v___y_8308_: *mut LeanObject,
    mut v___y_8309_: *mut LeanObject,
    mut v___y_8310_: *mut LeanObject,
    mut v___y_8311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8313_: *mut LeanObject = core::ptr::null_mut();
    v___x_8313_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(
        v_msg_8305_,
        v___y_8306_,
        v___y_8307_,
        v___y_8308_,
        v___y_8309_,
        v___y_8310_,
        v___y_8311_,
    );
    return v___x_8313_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___boxed(
    mut v_00_u03b1_8314_: *mut LeanObject,
    mut v_msg_8315_: *mut LeanObject,
    mut v___y_8316_: *mut LeanObject,
    mut v___y_8317_: *mut LeanObject,
    mut v___y_8318_: *mut LeanObject,
    mut v___y_8319_: *mut LeanObject,
    mut v___y_8320_: *mut LeanObject,
    mut v___y_8321_: *mut LeanObject,
    mut v___y_8322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8323_: *mut LeanObject = core::ptr::null_mut();
    v_res_8323_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(
        v_00_u03b1_8314_,
        v_msg_8315_,
        v___y_8316_,
        v___y_8317_,
        v___y_8318_,
        v___y_8319_,
        v___y_8320_,
        v___y_8321_,
    );
    lean_dec(v___y_8321_);
    lean_dec_ref(v___y_8320_);
    lean_dec(v___y_8319_);
    lean_dec_ref(v___y_8318_);
    lean_dec(v___y_8317_);
    lean_dec_ref(v___y_8316_);
    return v_res_8323_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2(
    mut v_cls_8324_: *mut LeanObject,
    mut v_msg_8325_: *mut LeanObject,
    mut v___y_8326_: *mut LeanObject,
    mut v___y_8327_: *mut LeanObject,
    mut v___y_8328_: *mut LeanObject,
    mut v___y_8329_: *mut LeanObject,
    mut v___y_8330_: *mut LeanObject,
    mut v___y_8331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8333_: *mut LeanObject = core::ptr::null_mut();
    v___x_8333_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(
        v_cls_8324_,
        v_msg_8325_,
        v___y_8328_,
        v___y_8329_,
        v___y_8330_,
        v___y_8331_,
    );
    return v___x_8333_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___boxed(
    mut v_cls_8334_: *mut LeanObject,
    mut v_msg_8335_: *mut LeanObject,
    mut v___y_8336_: *mut LeanObject,
    mut v___y_8337_: *mut LeanObject,
    mut v___y_8338_: *mut LeanObject,
    mut v___y_8339_: *mut LeanObject,
    mut v___y_8340_: *mut LeanObject,
    mut v___y_8341_: *mut LeanObject,
    mut v___y_8342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8343_: *mut LeanObject = core::ptr::null_mut();
    v_res_8343_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2(
        v_cls_8334_,
        v_msg_8335_,
        v___y_8336_,
        v___y_8337_,
        v___y_8338_,
        v___y_8339_,
        v___y_8340_,
        v___y_8341_,
    );
    lean_dec(v___y_8341_);
    lean_dec_ref(v___y_8340_);
    lean_dec(v___y_8339_);
    lean_dec_ref(v___y_8338_);
    lean_dec(v___y_8337_);
    lean_dec_ref(v___y_8336_);
    return v_res_8343_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6(
    mut v_hints_8344_: *mut LeanObject,
    mut v_as_8345_: *mut LeanObject,
    mut v_i_8346_: *mut LeanObject,
    mut v_j_8347_: *mut LeanObject,
    mut v_inv_8348_: *mut LeanObject,
    mut v_bs_8349_: *mut LeanObject,
    mut v___y_8350_: *mut LeanObject,
    mut v___y_8351_: *mut LeanObject,
    mut v___y_8352_: *mut LeanObject,
    mut v___y_8353_: *mut LeanObject,
    mut v___y_8354_: *mut LeanObject,
    mut v___y_8355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8357_: *mut LeanObject = core::ptr::null_mut();
    v___x_8357_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(
        v_hints_8344_,
        v_as_8345_,
        v_i_8346_,
        v_j_8347_,
        v_bs_8349_,
        v___y_8350_,
        v___y_8351_,
        v___y_8352_,
        v___y_8353_,
        v___y_8354_,
        v___y_8355_,
    );
    return v___x_8357_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___boxed(
    mut v_hints_8358_: *mut LeanObject,
    mut v_as_8359_: *mut LeanObject,
    mut v_i_8360_: *mut LeanObject,
    mut v_j_8361_: *mut LeanObject,
    mut v_inv_8362_: *mut LeanObject,
    mut v_bs_8363_: *mut LeanObject,
    mut v___y_8364_: *mut LeanObject,
    mut v___y_8365_: *mut LeanObject,
    mut v___y_8366_: *mut LeanObject,
    mut v___y_8367_: *mut LeanObject,
    mut v___y_8368_: *mut LeanObject,
    mut v___y_8369_: *mut LeanObject,
    mut v___y_8370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8371_: *mut LeanObject = core::ptr::null_mut();
    v_res_8371_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6(
        v_hints_8358_,
        v_as_8359_,
        v_i_8360_,
        v_j_8361_,
        v_inv_8362_,
        v_bs_8363_,
        v___y_8364_,
        v___y_8365_,
        v___y_8366_,
        v___y_8367_,
        v___y_8368_,
        v___y_8369_,
    );
    lean_dec(v___y_8369_);
    lean_dec_ref(v___y_8368_);
    lean_dec(v___y_8367_);
    lean_dec_ref(v___y_8366_);
    lean_dec(v___y_8365_);
    lean_dec_ref(v___y_8364_);
    lean_dec_ref(v_as_8359_);
    lean_dec_ref(v_hints_8358_);
    return v_res_8371_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10(
    mut v___x_8372_: *mut LeanObject,
    mut v_fixedArgs_8373_: *mut LeanObject,
    mut v_as_8374_: *mut LeanObject,
    mut v_i_8375_: *mut LeanObject,
    mut v_j_8376_: *mut LeanObject,
    mut v_inv_8377_: *mut LeanObject,
    mut v_bs_8378_: *mut LeanObject,
    mut v___y_8379_: *mut LeanObject,
    mut v___y_8380_: *mut LeanObject,
    mut v___y_8381_: *mut LeanObject,
    mut v___y_8382_: *mut LeanObject,
    mut v___y_8383_: *mut LeanObject,
    mut v___y_8384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8386_: *mut LeanObject = core::ptr::null_mut();
    v___x_8386_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(
        v___x_8372_,
        v_fixedArgs_8373_,
        v_as_8374_,
        v_i_8375_,
        v_j_8376_,
        v_bs_8378_,
        v___y_8381_,
        v___y_8382_,
        v___y_8383_,
        v___y_8384_,
    );
    return v___x_8386_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___boxed(
    mut v___x_8387_: *mut LeanObject,
    mut v_fixedArgs_8388_: *mut LeanObject,
    mut v_as_8389_: *mut LeanObject,
    mut v_i_8390_: *mut LeanObject,
    mut v_j_8391_: *mut LeanObject,
    mut v_inv_8392_: *mut LeanObject,
    mut v_bs_8393_: *mut LeanObject,
    mut v___y_8394_: *mut LeanObject,
    mut v___y_8395_: *mut LeanObject,
    mut v___y_8396_: *mut LeanObject,
    mut v___y_8397_: *mut LeanObject,
    mut v___y_8398_: *mut LeanObject,
    mut v___y_8399_: *mut LeanObject,
    mut v___y_8400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8401_: *mut LeanObject = core::ptr::null_mut();
    v_res_8401_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10(
        v___x_8387_,
        v_fixedArgs_8388_,
        v_as_8389_,
        v_i_8390_,
        v_j_8391_,
        v_inv_8392_,
        v_bs_8393_,
        v___y_8394_,
        v___y_8395_,
        v___y_8396_,
        v___y_8397_,
        v___y_8398_,
        v___y_8399_,
    );
    lean_dec(v___y_8399_);
    lean_dec_ref(v___y_8398_);
    lean_dec(v___y_8397_);
    lean_dec_ref(v___y_8396_);
    lean_dec(v___y_8395_);
    lean_dec_ref(v___y_8394_);
    lean_dec_ref(v_as_8389_);
    lean_dec_ref(v___x_8387_);
    return v_res_8401_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(
    mut v___x_8402_: *mut LeanObject,
    mut v_fixedArgs_8403_: *mut LeanObject,
    mut v_as_8404_: *mut LeanObject,
    mut v_i_8405_: *mut LeanObject,
    mut v_j_8406_: *mut LeanObject,
    mut v_inv_8407_: *mut LeanObject,
    mut v_bs_8408_: *mut LeanObject,
    mut v___y_8409_: *mut LeanObject,
    mut v___y_8410_: *mut LeanObject,
    mut v___y_8411_: *mut LeanObject,
    mut v___y_8412_: *mut LeanObject,
    mut v___y_8413_: *mut LeanObject,
    mut v___y_8414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8416_: *mut LeanObject = core::ptr::null_mut();
    v___x_8416_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(
        v___x_8402_,
        v_fixedArgs_8403_,
        v_as_8404_,
        v_i_8405_,
        v_j_8406_,
        v_bs_8408_,
        v___y_8411_,
        v___y_8412_,
        v___y_8413_,
        v___y_8414_,
    );
    return v___x_8416_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___boxed(
    mut v___x_8417_: *mut LeanObject,
    mut v_fixedArgs_8418_: *mut LeanObject,
    mut v_as_8419_: *mut LeanObject,
    mut v_i_8420_: *mut LeanObject,
    mut v_j_8421_: *mut LeanObject,
    mut v_inv_8422_: *mut LeanObject,
    mut v_bs_8423_: *mut LeanObject,
    mut v___y_8424_: *mut LeanObject,
    mut v___y_8425_: *mut LeanObject,
    mut v___y_8426_: *mut LeanObject,
    mut v___y_8427_: *mut LeanObject,
    mut v___y_8428_: *mut LeanObject,
    mut v___y_8429_: *mut LeanObject,
    mut v___y_8430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8431_: *mut LeanObject = core::ptr::null_mut();
    v_res_8431_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(
        v___x_8417_,
        v_fixedArgs_8418_,
        v_as_8419_,
        v_i_8420_,
        v_j_8421_,
        v_inv_8422_,
        v_bs_8423_,
        v___y_8424_,
        v___y_8425_,
        v___y_8426_,
        v___y_8427_,
        v___y_8428_,
        v___y_8429_,
    );
    lean_dec(v___y_8429_);
    lean_dec_ref(v___y_8428_);
    lean_dec(v___y_8427_);
    lean_dec_ref(v___y_8426_);
    lean_dec(v___y_8425_);
    lean_dec_ref(v___y_8424_);
    lean_dec_ref(v_as_8419_);
    lean_dec_ref(v___x_8417_);
    return v_res_8431_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13(
    mut v_as_8432_: *mut LeanObject,
    mut v_i_8433_: usize,
    mut v_stop_8434_: usize,
    mut v_b_8435_: *mut LeanObject,
    mut v___y_8436_: *mut LeanObject,
    mut v___y_8437_: *mut LeanObject,
    mut v___y_8438_: *mut LeanObject,
    mut v___y_8439_: *mut LeanObject,
    mut v___y_8440_: *mut LeanObject,
    mut v___y_8441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8443_: *mut LeanObject = core::ptr::null_mut();
    v___x_8443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_as_8432_, v_i_8433_, v_stop_8434_, v_b_8435_, v___y_8440_, v___y_8441_);
    return v___x_8443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___boxed(
    mut v_as_8444_: *mut LeanObject,
    mut v_i_8445_: *mut LeanObject,
    mut v_stop_8446_: *mut LeanObject,
    mut v_b_8447_: *mut LeanObject,
    mut v___y_8448_: *mut LeanObject,
    mut v___y_8449_: *mut LeanObject,
    mut v___y_8450_: *mut LeanObject,
    mut v___y_8451_: *mut LeanObject,
    mut v___y_8452_: *mut LeanObject,
    mut v___y_8453_: *mut LeanObject,
    mut v___y_8454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_8455_: usize = 0;
    let mut v_stop_boxed_8456_: usize = 0;
    let mut v_res_8457_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_8455_ = lean_unbox_usize(v_i_8445_);
    lean_dec(v_i_8445_);
    v_stop_boxed_8456_ = lean_unbox_usize(v_stop_8446_);
    lean_dec(v_stop_8446_);
    v_res_8457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13(v_as_8444_, v_i_boxed_8455_, v_stop_boxed_8456_, v_b_8447_, v___y_8448_, v___y_8449_, v___y_8450_, v___y_8451_, v___y_8452_, v___y_8453_);
    lean_dec(v___y_8453_);
    lean_dec_ref(v___y_8452_);
    lean_dec(v___y_8451_);
    lean_dec_ref(v___y_8450_);
    lean_dec(v___y_8449_);
    lean_dec_ref(v___y_8448_);
    lean_dec_ref(v_as_8444_);
    return v_res_8457_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16(
    mut v_env_8458_: *mut LeanObject,
    mut v___y_8459_: *mut LeanObject,
    mut v___y_8460_: *mut LeanObject,
    mut v___y_8461_: *mut LeanObject,
    mut v___y_8462_: *mut LeanObject,
    mut v___y_8463_: *mut LeanObject,
    mut v___y_8464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8466_: *mut LeanObject = core::ptr::null_mut();
    v___x_8466_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_8458_, v___y_8462_, v___y_8464_);
    return v___x_8466_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___boxed(
    mut v_env_8467_: *mut LeanObject,
    mut v___y_8468_: *mut LeanObject,
    mut v___y_8469_: *mut LeanObject,
    mut v___y_8470_: *mut LeanObject,
    mut v___y_8471_: *mut LeanObject,
    mut v___y_8472_: *mut LeanObject,
    mut v___y_8473_: *mut LeanObject,
    mut v___y_8474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8475_: *mut LeanObject = core::ptr::null_mut();
    v_res_8475_ =
        l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16(
            v_env_8467_,
            v___y_8468_,
            v___y_8469_,
            v___y_8470_,
            v___y_8471_,
            v___y_8472_,
            v___y_8473_,
        );
    lean_dec(v___y_8473_);
    lean_dec_ref(v___y_8472_);
    lean_dec(v___y_8471_);
    lean_dec_ref(v___y_8470_);
    lean_dec(v___y_8469_);
    lean_dec_ref(v___y_8468_);
    return v_res_8475_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14(
    mut v_00_u03b1_8476_: *mut LeanObject,
    mut v_env_8477_: *mut LeanObject,
    mut v_x_8478_: *mut LeanObject,
    mut v___y_8479_: *mut LeanObject,
    mut v___y_8480_: *mut LeanObject,
    mut v___y_8481_: *mut LeanObject,
    mut v___y_8482_: *mut LeanObject,
    mut v___y_8483_: *mut LeanObject,
    mut v___y_8484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8486_: *mut LeanObject = core::ptr::null_mut();
    v___x_8486_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(
        v_env_8477_,
        v_x_8478_,
        v___y_8479_,
        v___y_8480_,
        v___y_8481_,
        v___y_8482_,
        v___y_8483_,
        v___y_8484_,
    );
    return v___x_8486_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___boxed(
    mut v_00_u03b1_8487_: *mut LeanObject,
    mut v_env_8488_: *mut LeanObject,
    mut v_x_8489_: *mut LeanObject,
    mut v___y_8490_: *mut LeanObject,
    mut v___y_8491_: *mut LeanObject,
    mut v___y_8492_: *mut LeanObject,
    mut v___y_8493_: *mut LeanObject,
    mut v___y_8494_: *mut LeanObject,
    mut v___y_8495_: *mut LeanObject,
    mut v___y_8496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8497_: *mut LeanObject = core::ptr::null_mut();
    v_res_8497_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14(
        v_00_u03b1_8487_,
        v_env_8488_,
        v_x_8489_,
        v___y_8490_,
        v___y_8491_,
        v___y_8492_,
        v___y_8493_,
        v___y_8494_,
        v___y_8495_,
    );
    lean_dec(v___y_8495_);
    lean_dec_ref(v___y_8494_);
    lean_dec(v___y_8493_);
    lean_dec_ref(v___y_8492_);
    lean_dec(v___y_8491_);
    lean_dec_ref(v___y_8490_);
    return v_res_8497_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18(
    mut v_00_u03b1_8498_: *mut LeanObject,
    mut v_name_8499_: *mut LeanObject,
    mut v_bi_8500_: u8,
    mut v_type_8501_: *mut LeanObject,
    mut v_k_8502_: *mut LeanObject,
    mut v_kind_8503_: u8,
    mut v___y_8504_: *mut LeanObject,
    mut v___y_8505_: *mut LeanObject,
    mut v___y_8506_: *mut LeanObject,
    mut v___y_8507_: *mut LeanObject,
    mut v___y_8508_: *mut LeanObject,
    mut v___y_8509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8511_: *mut LeanObject = core::ptr::null_mut();
    v___x_8511_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_8499_, v_bi_8500_, v_type_8501_, v_k_8502_, v_kind_8503_, v___y_8504_, v___y_8505_, v___y_8506_, v___y_8507_, v___y_8508_, v___y_8509_);
    return v___x_8511_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___boxed(
    mut v_00_u03b1_8512_: *mut LeanObject,
    mut v_name_8513_: *mut LeanObject,
    mut v_bi_8514_: *mut LeanObject,
    mut v_type_8515_: *mut LeanObject,
    mut v_k_8516_: *mut LeanObject,
    mut v_kind_8517_: *mut LeanObject,
    mut v___y_8518_: *mut LeanObject,
    mut v___y_8519_: *mut LeanObject,
    mut v___y_8520_: *mut LeanObject,
    mut v___y_8521_: *mut LeanObject,
    mut v___y_8522_: *mut LeanObject,
    mut v___y_8523_: *mut LeanObject,
    mut v___y_8524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_8525_: u8 = 0;
    let mut v_kind_boxed_8526_: u8 = 0;
    let mut v_res_8527_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_8525_ = (lean_unbox(v_bi_8514_) as u8);
    v_kind_boxed_8526_ = (lean_unbox(v_kind_8517_) as u8);
    v_res_8527_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18(v_00_u03b1_8512_, v_name_8513_, v_bi_boxed_8525_, v_type_8515_, v_k_8516_, v_kind_boxed_8526_, v___y_8518_, v___y_8519_, v___y_8520_, v___y_8521_, v___y_8522_, v___y_8523_);
    lean_dec(v___y_8523_);
    lean_dec_ref(v___y_8522_);
    lean_dec(v___y_8521_);
    lean_dec_ref(v___y_8520_);
    lean_dec(v___y_8519_);
    lean_dec_ref(v___y_8518_);
    return v_res_8527_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15(
    mut v_00_u03b1_8528_: *mut LeanObject,
    mut v_name_8529_: *mut LeanObject,
    mut v_type_8530_: *mut LeanObject,
    mut v_k_8531_: *mut LeanObject,
    mut v___y_8532_: *mut LeanObject,
    mut v___y_8533_: *mut LeanObject,
    mut v___y_8534_: *mut LeanObject,
    mut v___y_8535_: *mut LeanObject,
    mut v___y_8536_: *mut LeanObject,
    mut v___y_8537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8539_: *mut LeanObject = core::ptr::null_mut();
    v___x_8539_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(
        v_name_8529_,
        v_type_8530_,
        v_k_8531_,
        v___y_8532_,
        v___y_8533_,
        v___y_8534_,
        v___y_8535_,
        v___y_8536_,
        v___y_8537_,
    );
    return v___x_8539_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___boxed(
    mut v_00_u03b1_8540_: *mut LeanObject,
    mut v_name_8541_: *mut LeanObject,
    mut v_type_8542_: *mut LeanObject,
    mut v_k_8543_: *mut LeanObject,
    mut v___y_8544_: *mut LeanObject,
    mut v___y_8545_: *mut LeanObject,
    mut v___y_8546_: *mut LeanObject,
    mut v___y_8547_: *mut LeanObject,
    mut v___y_8548_: *mut LeanObject,
    mut v___y_8549_: *mut LeanObject,
    mut v___y_8550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8551_: *mut LeanObject = core::ptr::null_mut();
    v_res_8551_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15(
        v_00_u03b1_8540_,
        v_name_8541_,
        v_type_8542_,
        v_k_8543_,
        v___y_8544_,
        v___y_8545_,
        v___y_8546_,
        v___y_8547_,
        v___y_8548_,
        v___y_8549_,
    );
    lean_dec(v___y_8549_);
    lean_dec_ref(v___y_8548_);
    lean_dec(v___y_8547_);
    lean_dec_ref(v___y_8546_);
    lean_dec(v___y_8545_);
    lean_dec_ref(v___y_8544_);
    return v_res_8551_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21(
    mut v_00_u03b1_8552_: *mut LeanObject,
    mut v_x_8553_: *mut LeanObject,
    mut v_isExporting_8554_: u8,
    mut v___y_8555_: *mut LeanObject,
    mut v___y_8556_: *mut LeanObject,
    mut v___y_8557_: *mut LeanObject,
    mut v___y_8558_: *mut LeanObject,
    mut v___y_8559_: *mut LeanObject,
    mut v___y_8560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8562_: *mut LeanObject = core::ptr::null_mut();
    v___x_8562_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_8553_, v_isExporting_8554_, v___y_8555_, v___y_8556_, v___y_8557_, v___y_8558_, v___y_8559_, v___y_8560_);
    return v___x_8562_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___boxed(
    mut v_00_u03b1_8563_: *mut LeanObject,
    mut v_x_8564_: *mut LeanObject,
    mut v_isExporting_8565_: *mut LeanObject,
    mut v___y_8566_: *mut LeanObject,
    mut v___y_8567_: *mut LeanObject,
    mut v___y_8568_: *mut LeanObject,
    mut v___y_8569_: *mut LeanObject,
    mut v___y_8570_: *mut LeanObject,
    mut v___y_8571_: *mut LeanObject,
    mut v___y_8572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_8573_: u8 = 0;
    let mut v_res_8574_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_8573_ = (lean_unbox(v_isExporting_8565_) as u8);
    v_res_8574_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21(v_00_u03b1_8563_, v_x_8564_, v_isExporting_boxed_8573_, v___y_8566_, v___y_8567_, v___y_8568_, v___y_8569_, v___y_8570_, v___y_8571_);
    lean_dec(v___y_8571_);
    lean_dec_ref(v___y_8570_);
    lean_dec(v___y_8569_);
    lean_dec_ref(v___y_8568_);
    lean_dec(v___y_8567_);
    lean_dec_ref(v___y_8566_);
    return v_res_8574_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17(
    mut v_00_u03b1_8575_: *mut LeanObject,
    mut v_x_8576_: *mut LeanObject,
    mut v_when_8577_: u8,
    mut v___y_8578_: *mut LeanObject,
    mut v___y_8579_: *mut LeanObject,
    mut v___y_8580_: *mut LeanObject,
    mut v___y_8581_: *mut LeanObject,
    mut v___y_8582_: *mut LeanObject,
    mut v___y_8583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8585_: *mut LeanObject = core::ptr::null_mut();
    v___x_8585_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(
        v_x_8576_,
        v_when_8577_,
        v___y_8578_,
        v___y_8579_,
        v___y_8580_,
        v___y_8581_,
        v___y_8582_,
        v___y_8583_,
    );
    return v___x_8585_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___boxed(
    mut v_00_u03b1_8586_: *mut LeanObject,
    mut v_x_8587_: *mut LeanObject,
    mut v_when_8588_: *mut LeanObject,
    mut v___y_8589_: *mut LeanObject,
    mut v___y_8590_: *mut LeanObject,
    mut v___y_8591_: *mut LeanObject,
    mut v___y_8592_: *mut LeanObject,
    mut v___y_8593_: *mut LeanObject,
    mut v___y_8594_: *mut LeanObject,
    mut v___y_8595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_8596_: u8 = 0;
    let mut v_res_8597_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_8596_ = (lean_unbox(v_when_8588_) as u8);
    v_res_8597_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17(
        v_00_u03b1_8586_,
        v_x_8587_,
        v_when_boxed_8596_,
        v___y_8589_,
        v___y_8590_,
        v___y_8591_,
        v___y_8592_,
        v___y_8593_,
        v___y_8594_,
    );
    lean_dec(v___y_8594_);
    lean_dec_ref(v___y_8593_);
    lean_dec(v___y_8592_);
    lean_dec_ref(v___y_8591_);
    lean_dec(v___y_8590_);
    lean_dec_ref(v___y_8589_);
    return v_res_8597_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21(
    mut v___x_8598_: *mut LeanObject,
    mut v___x_8599_: *mut LeanObject,
    mut v___y_8600_: *mut LeanObject,
    mut v___x_8601_: *mut LeanObject,
    mut v_a_8602_: *mut LeanObject,
    mut v_as_8603_: *mut LeanObject,
    mut v_i_8604_: *mut LeanObject,
    mut v_j_8605_: *mut LeanObject,
    mut v_inv_8606_: *mut LeanObject,
    mut v_bs_8607_: *mut LeanObject,
    mut v___y_8608_: *mut LeanObject,
    mut v___y_8609_: *mut LeanObject,
    mut v___y_8610_: *mut LeanObject,
    mut v___y_8611_: *mut LeanObject,
    mut v___y_8612_: *mut LeanObject,
    mut v___y_8613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8615_: *mut LeanObject = core::ptr::null_mut();
    v___x_8615_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(
        v___x_8598_,
        v___x_8599_,
        v___y_8600_,
        v___x_8601_,
        v_a_8602_,
        v_as_8603_,
        v_i_8604_,
        v_j_8605_,
        v_bs_8607_,
        v___y_8608_,
        v___y_8609_,
        v___y_8610_,
        v___y_8611_,
        v___y_8612_,
        v___y_8613_,
    );
    return v___x_8615_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8616_: *mut LeanObject = *_args.add(0);
    let mut v___x_8617_: *mut LeanObject = *_args.add(1);
    let mut v___y_8618_: *mut LeanObject = *_args.add(2);
    let mut v___x_8619_: *mut LeanObject = *_args.add(3);
    let mut v_a_8620_: *mut LeanObject = *_args.add(4);
    let mut v_as_8621_: *mut LeanObject = *_args.add(5);
    let mut v_i_8622_: *mut LeanObject = *_args.add(6);
    let mut v_j_8623_: *mut LeanObject = *_args.add(7);
    let mut v_inv_8624_: *mut LeanObject = *_args.add(8);
    let mut v_bs_8625_: *mut LeanObject = *_args.add(9);
    let mut v___y_8626_: *mut LeanObject = *_args.add(10);
    let mut v___y_8627_: *mut LeanObject = *_args.add(11);
    let mut v___y_8628_: *mut LeanObject = *_args.add(12);
    let mut v___y_8629_: *mut LeanObject = *_args.add(13);
    let mut v___y_8630_: *mut LeanObject = *_args.add(14);
    let mut v___y_8631_: *mut LeanObject = *_args.add(15);
    let mut v___y_8632_: *mut LeanObject = *_args.add(16);
    let mut v_res_8633_: *mut LeanObject = core::ptr::null_mut();
    v_res_8633_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21(
        v___x_8616_,
        v___x_8617_,
        v___y_8618_,
        v___x_8619_,
        v_a_8620_,
        v_as_8621_,
        v_i_8622_,
        v_j_8623_,
        v_inv_8624_,
        v_bs_8625_,
        v___y_8626_,
        v___y_8627_,
        v___y_8628_,
        v___y_8629_,
        v___y_8630_,
        v___y_8631_,
    );
    lean_dec(v___y_8631_);
    lean_dec_ref(v___y_8630_);
    lean_dec(v___y_8629_);
    lean_dec_ref(v___y_8628_);
    lean_dec(v___y_8627_);
    lean_dec_ref(v___y_8626_);
    lean_dec_ref(v_as_8621_);
    lean_dec_ref(v___x_8616_);
    return v_res_8633_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22(
    mut v_sz_8634_: usize,
    mut v_i_8635_: usize,
    mut v_bs_8636_: *mut LeanObject,
    mut v___y_8637_: *mut LeanObject,
    mut v___y_8638_: *mut LeanObject,
    mut v___y_8639_: *mut LeanObject,
    mut v___y_8640_: *mut LeanObject,
    mut v___y_8641_: *mut LeanObject,
    mut v___y_8642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8644_: *mut LeanObject = core::ptr::null_mut();
    v___x_8644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_8634_, v_i_8635_, v_bs_8636_, v___y_8639_, v___y_8640_, v___y_8641_, v___y_8642_);
    return v___x_8644_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___boxed(
    mut v_sz_8645_: *mut LeanObject,
    mut v_i_8646_: *mut LeanObject,
    mut v_bs_8647_: *mut LeanObject,
    mut v___y_8648_: *mut LeanObject,
    mut v___y_8649_: *mut LeanObject,
    mut v___y_8650_: *mut LeanObject,
    mut v___y_8651_: *mut LeanObject,
    mut v___y_8652_: *mut LeanObject,
    mut v___y_8653_: *mut LeanObject,
    mut v___y_8654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8655_: usize = 0;
    let mut v_i_boxed_8656_: usize = 0;
    let mut v_res_8657_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8655_ = lean_unbox_usize(v_sz_8645_);
    lean_dec(v_sz_8645_);
    v_i_boxed_8656_ = lean_unbox_usize(v_i_8646_);
    lean_dec(v_i_8646_);
    v_res_8657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22(v_sz_boxed_8655_, v_i_boxed_8656_, v_bs_8647_, v___y_8648_, v___y_8649_, v___y_8650_, v___y_8651_, v___y_8652_, v___y_8653_);
    lean_dec(v___y_8653_);
    lean_dec_ref(v___y_8652_);
    lean_dec(v___y_8651_);
    lean_dec_ref(v___y_8650_);
    lean_dec(v___y_8649_);
    lean_dec_ref(v___y_8648_);
    return v_res_8657_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(
    mut v_msgData_8658_: *mut LeanObject,
    mut v_macroStack_8659_: *mut LeanObject,
    mut v___y_8660_: *mut LeanObject,
    mut v___y_8661_: *mut LeanObject,
    mut v___y_8662_: *mut LeanObject,
    mut v___y_8663_: *mut LeanObject,
    mut v___y_8664_: *mut LeanObject,
    mut v___y_8665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8667_: *mut LeanObject = core::ptr::null_mut();
    v___x_8667_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_8658_, v_macroStack_8659_, v___y_8664_);
    return v___x_8667_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___boxed(
    mut v_msgData_8668_: *mut LeanObject,
    mut v_macroStack_8669_: *mut LeanObject,
    mut v___y_8670_: *mut LeanObject,
    mut v___y_8671_: *mut LeanObject,
    mut v___y_8672_: *mut LeanObject,
    mut v___y_8673_: *mut LeanObject,
    mut v___y_8674_: *mut LeanObject,
    mut v___y_8675_: *mut LeanObject,
    mut v___y_8676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8677_: *mut LeanObject = core::ptr::null_mut();
    v_res_8677_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(v_msgData_8668_, v_macroStack_8669_, v___y_8670_, v___y_8671_, v___y_8672_, v___y_8673_, v___y_8674_, v___y_8675_);
    lean_dec(v___y_8675_);
    lean_dec_ref(v___y_8674_);
    lean_dec(v___y_8673_);
    lean_dec_ref(v___y_8672_);
    lean_dec(v___y_8671_);
    lean_dec_ref(v___y_8670_);
    return v_res_8677_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_8741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8742_: u8 = 0;
    let mut v___x_8743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8744_: *mut LeanObject = core::ptr::null_mut();
    v___x_8741_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7;
    v___x_8742_ = 0;
    v___x_8743_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_;
    v___x_8744_ = l_Lean_registerTraceClass(v___x_8741_, v___x_8742_, v___x_8743_);
    return v___x_8744_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2____boxed(
    mut v_a_8745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8746_: *mut LeanObject = core::ptr::null_mut();
    v_res_8746_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_();
    return v_res_8746_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Mutual(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Monotonicity(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Mutual(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Monotonicity(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
}
