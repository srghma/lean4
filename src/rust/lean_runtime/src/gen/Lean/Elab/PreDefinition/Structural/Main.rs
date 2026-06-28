// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Main
// Imports: Lean.Elab.PreDefinition.Mutual Lean.Elab.PreDefinition.Structural.FindRecArg Lean.Elab.PreDefinition.Structural.Preprocess Lean.Elab.PreDefinition.Structural.BRecOn Lean.Elab.PreDefinition.Structural.IndPred Lean.Elab.PreDefinition.Structural.Eqns Lean.Elab.PreDefinition.Structural.SmartUnfolding Lean.Meta.Tactic.TryThis
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
    l_Array_instInhabited, l_Array_range, l_Array_zip___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Nat::Basic::l_Nat_blt;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_enableRealizationsForConst,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_numTypeFormers;
use crate::r#gen::Lean::Elab::DefView::l_Lean_Elab_DefKind_isTheorem;
use crate::r#gen::Lean::Elab::PreDefinition::Basic::{
    l_Lean_Elab_abstractNestedProofs, l_Lean_Elab_addAndCompilePartialRec,
    l_Lean_Elab_addAsAxiom___boxed, l_Lean_Elab_addAsAxiom___redArg, l_Lean_Elab_addNonRec,
    l_Lean_Elab_applyAttributesOf, l_Lean_Elab_eraseRecAppSyntax,
    l_Lean_Elab_eraseRecAppSyntaxExpr, l_Lean_Elab_instInhabitedPreDefinition_default,
};
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::{
    l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl,
    l_Lean_Elab_FixedParamPerm_buildArgs___redArg, l_Lean_Elab_FixedParamPerm_instantiateForall,
    l_Lean_Elab_FixedParamPerm_instantiateLambda, l_Lean_Elab_FixedParamPerms_erase,
    l_Lean_Elab_getFixedParamPerms___boxed,
};
use crate::r#gen::Lean::Elab::PreDefinition::Mutual::{
    initialize_Lean_Elab_PreDefinition_Mutual, runtime_initialize_Lean_Elab_PreDefinition_Mutual,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::BRecOn::{
    initialize_Lean_Elab_PreDefinition_Structural_BRecOn, l_Lean_Elab_Structural_inferBRecOnFTypes,
    l_Lean_Elab_Structural_mkBRecOnApp, l_Lean_Elab_Structural_mkBRecOnConst,
    l_Lean_Elab_Structural_mkBRecOnF___boxed, l_Lean_Elab_Structural_mkBRecOnMotive,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_BRecOn,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::Basic::l_Lean_Elab_Structural_Positions_numIndices;
use crate::r#gen::Lean::Elab::PreDefinition::Structural::Eqns::{
    initialize_Lean_Elab_PreDefinition_Structural_Eqns, l_Lean_Elab_Structural_registerEqnsInfo,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_Eqns,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::FindRecArg::{
    initialize_Lean_Elab_PreDefinition_Structural_FindRecArg,
    l_Lean_Elab_Structural_findRecArgCandidates___boxed,
    l_Lean_Elab_Structural_tryCandidates___redArg,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::IndPred::{
    initialize_Lean_Elab_PreDefinition_Structural_IndPred,
    l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed, l_Lean_Elab_Structural_mkIndPredBRecOnMotive,
    l_Lean_Elab_Structural_withFunTypes___redArg,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_IndPred,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::Preprocess::{
    initialize_Lean_Elab_PreDefinition_Structural_Preprocess, l_Lean_Elab_Structural_preprocess,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_Preprocess,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::RecArgInfo::{
    l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos,
    l_Lean_Elab_Structural_instInhabitedRecArgInfo_default,
    l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::SmartUnfolding::{
    initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding,
    l_Lean_Elab_Structural_addSmartUnfoldingDef,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding,
};
use crate::r#gen::Lean::Elab::PreDefinition::TerminationMeasure::l_Lean_Elab_TerminationMeasure_delab;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_unlockAsync, l_Lean_getMaxHeight, l_Lean_setDefHeightOverride,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_beta,
    l_Lean_Expr_const___override, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_Expr_isFVarOf, l_Lean_Expr_sort___override,
    l_Lean_instBEqFVarId_beq, l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst,
    l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::lean_local_ctx_erase;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_nil, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_isInductivePredicate, l_Lean_Meta_mapErrorImp___redArg, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::Eqns::l_Lean_Meta_saveEqnAffectingOptions;
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_inferArgumentTypesN, l_Lean_Meta_isProp};
use crate::r#gen::Lean::Meta::LetToHave::l_Lean_Meta_letToHave;
use crate::r#gen::Lean::Meta::PProdN::l_Lean_Meta_PProdN_mkLambdas___boxed;
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addSuggestion,
    runtime_initialize_Lean_Meta_Tactic_TryThis,
};
use crate::r#gen::Lean::MetavarContext::l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit;
use crate::r#gen::Lean::MonadEnv::{l_Lean_isInductiveCore_x3f, l_Lean_withEnv___redArg};
use crate::r#gen::Lean::ReducibilityAttrs::l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_apply_5, lean_apply_6, lean_apply_7, lean_box, lean_box_usize,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(0 as *mut LeanObject)] };
pub static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2_value) as *mut LeanObject;
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4_value) as *mut LeanObject;
static mut l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 80, 111, 115, 105, 116, 105, 111, 110, 115, 46, 109, 97, 112, 77, 119, 105, 116, 104, 0]};
static mut l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2_value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 111, 115, 105, 116, 105, 111, 110, 115, 46, 115, 105, 122, 101, 32, 61, 32, 121, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 111, 115, 105, 116, 105, 111, 110, 115, 46, 110, 117, 109, 73, 110, 100, 105, 99, 101, 115, 32, 61, 32, 120, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 102, 0]};
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__0_value) as *mut LeanObject,12317437071847932413 as *mut LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__0_value) as *mut LeanObject,17542774118954891045 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 99, 107, 101, 100, 70, 65, 114, 103, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [70, 65, 114, 103, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [70, 84, 121, 112, 101, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 117, 110, 84, 121, 112, 101, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [44, 32, 109, 111, 116, 105, 118, 101, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0_value) as *mut LeanObject;
static mut l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 80, 111, 115, 105, 116, 105, 111, 110, 115, 46, 103, 114, 111, 117, 112, 65, 110, 100, 83, 111, 114, 116, 0]};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 65, 114, 114, 97, 121, 46, 114, 97, 110, 103, 101, 32, 120, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 112, 111, 115, 105, 116, 105, 111, 110, 115, 46, 102, 108, 97, 116, 116, 101, 110, 46, 113, 115, 111, 114, 116, 32, 78, 97, 116, 46, 98, 108, 116, 10, 32, 32, 0]};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__0_value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1_value) as *mut LeanObject,6897119537390546559 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2_value) as *mut LeanObject,14406337792964512117 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_PProdN_mkLambdas___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 115, 32, 111, 102, 32, 116, 121, 112, 101, 32, 102, 111, 114, 109, 101, 114, 115, 32, 111, 102, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 116, 111, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0_value) as *mut LeanObject;
pub static l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__1_value) as *mut LeanObject;
pub static l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__1_value) as *mut LeanObject] };
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__2_value) as *mut LeanObject;
pub static l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__2_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3_value) as *mut LeanObject;
pub static l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__4_value) as *mut LeanObject;
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0_value) as *mut LeanObject] };
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7_value) as *mut LeanObject;
pub static l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__4_value) as *mut LeanObject] };
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8_value) as *mut LeanObject;
pub static l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__9_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__9_value) as *mut LeanObject;
pub static l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__9_value) as *mut LeanObject] };
static mut l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0_value: LeanStringObject<61> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [105, 116, 115, 32, 116, 121, 112, 101, 32, 105, 115, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 32, 97, 110, 100, 32, 116, 104, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [10, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 116, 104, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4_value: LeanStringObject<137> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 137, m_capacity: 137, m_length: 136, m_data: [10, 119, 104, 105, 99, 104, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 102, 105, 120, 101, 100, 32, 97, 115, 32, 105, 116, 32, 105, 115, 32, 97, 110, 32, 105, 110, 100, 101, 120, 32, 111, 114, 32, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 97, 110, 32, 105, 110, 100, 101, 120, 44, 32, 97, 110, 100, 32, 105, 110, 100, 105, 99, 101, 115, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 102, 105, 120, 101, 100, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 119, 104, 101, 110, 32, 117, 115, 105, 110, 103, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [78, 101, 119, 32, 114, 101, 99, 65, 114, 103, 73, 110, 102, 111, 115, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [82, 101, 100, 117, 99, 101, 100, 32, 102, 105, 120, 101, 100, 32, 112, 97, 114, 97, 109, 115, 32, 102, 114, 111, 109, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 116, 111, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [44, 32, 101, 114, 97, 115, 105, 110, 103, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [84, 114, 121, 105, 110, 103, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 115, 101, 116, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_reportTermMeasure___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Structural_reportTermMeasure___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Structural_reportTermMeasure___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Structural_reportTermMeasure___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Structural_reportTermMeasure___closed__2_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Structural_reportTermMeasure___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Structural_reportTermMeasure___closed__3_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Structural_reportTermMeasure___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Structural_reportTermMeasure___closed__4_value: LeanStringObject<14> =
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
        m_data: [
            116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 66, 121, 0,
        ],
    };
static mut l_Lean_Elab_Structural_reportTermMeasure___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__1_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__2_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__3_value)
                as *mut LeanObject,
            7625897890118033792 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Structural_reportTermMeasure___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__4_value)
                as *mut LeanObject,
            11893284350339308820 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Structural_reportTermMeasure___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Structural_reportTermMeasure___closed__6_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0],
    };
static mut l_Lean_Elab_Structural_reportTermMeasure___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_reportTermMeasure___closed__6_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0_value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 102, 97, 105, 108, 101, 100, 44, 32, 112, 114, 111, 100, 117, 99, 101, 100, 32, 116, 121, 112, 101, 32, 105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 116, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0(
    mut v_k_4456_: *mut LeanObject,
    mut v_____r_4457_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4456_);
    return v_k_4456_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0___boxed(
    mut v_k_4458_: *mut LeanObject,
    mut v_____r_4459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4460_: *mut LeanObject = core::ptr::null_mut();
    v_res_4460_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0(v_k_4458_, v_____r_4459_);
    lean_dec(v_k_4458_);
    return v_res_4460_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__1(
    mut v_inst_4461_: *mut LeanObject,
    mut v_inst_4462_: *mut LeanObject,
    mut v_inst_4463_: *mut LeanObject,
    mut v___x_4464_: *mut LeanObject,
    mut v_____do__lift_4465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    v___x_4466_ = l_Lean_Environment_unlockAsync(v_____do__lift_4465_);
    v___x_4467_ = l_Lean_withEnv___redArg(
        v_inst_4461_,
        v_inst_4462_,
        v_inst_4463_,
        v___x_4466_,
        v___x_4464_,
    );
    return v___x_4467_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__2(
    mut v_inst_4468_: *mut LeanObject,
    mut v_x_4469_: *mut LeanObject,
    mut v___y_4470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    v___x_4471_ = lean_alloc_closure(
        l_Lean_Elab_addAsAxiom___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_4471_, 0, v___y_4470_);
    v___x_4472_ = lean_apply_2(v_inst_4468_, lean_box(0), v___x_4471_);
    return v___x_4472_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg(
    mut v_inst_4473_: *mut LeanObject,
    mut v_inst_4474_: *mut LeanObject,
    mut v_inst_4475_: *mut LeanObject,
    mut v_inst_4476_: *mut LeanObject,
    mut v_preDefs_4477_: *mut LeanObject,
    mut v_k_4478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: u8 = 0;
    let mut v_toPure_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: u8 = 0;
    let mut v_toPure_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: usize = 0;
    let mut v___x_4499_: usize = 0;
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: usize = 0;
    let mut v___x_4502_: usize = 0;
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_4479_ = lean_ctor_get(v_inst_4473_, 0);
                v_toBind_4480_ = lean_ctor_get(v_inst_4473_, 1);
                lean_inc(v_toBind_4480_);
                v___f_4481_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_4481_, 0, v_k_4478_);
                v___x_4488_ = lean_unsigned_to_nat(0);
                v___x_4489_ = lean_array_get_size(v_preDefs_4477_);
                v___x_4490_ = lean_box(0);
                v___x_4491_ = lean_nat_dec_lt(v___x_4488_, v___x_4489_);
                if v___x_4491_ == 0 {
                    lean_dec_ref(v_preDefs_4477_);
                    lean_dec(v_inst_4474_);
                    v_toPure_4492_ = lean_ctor_get(v_toApplicative_4479_, 1);
                    lean_inc(v_toPure_4492_);
                    v___x_4493_ = lean_apply_2(v_toPure_4492_, lean_box(0), v___x_4490_);
                    v___y_4483_ = v___x_4493_;
                    state = 1;
                    continue;
                } else {
                    v___f_4494_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__2 as *mut core::ffi::c_void, 3, 1);
                    lean_closure_set(v___f_4494_, 0, v_inst_4474_);
                    v___x_4495_ = lean_nat_dec_le(v___x_4489_, v___x_4489_);
                    if v___x_4495_ == 0 {
                        if v___x_4491_ == 0 {
                            lean_dec_ref(v___f_4494_);
                            lean_dec_ref(v_preDefs_4477_);
                            v_toPure_4496_ = lean_ctor_get(v_toApplicative_4479_, 1);
                            lean_inc(v_toPure_4496_);
                            v___x_4497_ = lean_apply_2(v_toPure_4496_, lean_box(0), v___x_4490_);
                            v___y_4483_ = v___x_4497_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4498_ = 0usize;
                            v___x_4499_ = lean_usize_of_nat(v___x_4489_);
                            lean_inc_ref(v_inst_4473_);
                            v___x_4500_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v_inst_4473_,
                                    v___f_4494_,
                                    v_preDefs_4477_,
                                    v___x_4498_,
                                    v___x_4499_,
                                    v___x_4490_,
                                );
                            v___y_4483_ = v___x_4500_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4501_ = 0usize;
                        v___x_4502_ = lean_usize_of_nat(v___x_4489_);
                        lean_inc_ref(v_inst_4473_);
                        v___x_4503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v_inst_4473_,
                            v___f_4494_,
                            v_preDefs_4477_,
                            v___x_4501_,
                            v___x_4502_,
                            v___x_4490_,
                        );
                        v___y_4483_ = v___x_4503_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_getEnv_4484_ = lean_ctor_get(v_inst_4475_, 0);
                lean_inc(v_getEnv_4484_);
                lean_inc(v_toBind_4480_);
                v___x_4485_ = lean_apply_4(
                    v_toBind_4480_,
                    lean_box(0),
                    lean_box(0),
                    v___y_4483_,
                    v___f_4481_,
                );
                v___f_4486_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___f_4486_, 0, v_inst_4473_);
                lean_closure_set(v___f_4486_, 1, v_inst_4476_);
                lean_closure_set(v___f_4486_, 2, v_inst_4475_);
                lean_closure_set(v___f_4486_, 3, v___x_4485_);
                v___x_4487_ = lean_apply_4(
                    v_toBind_4480_,
                    lean_box(0),
                    lean_box(0),
                    v_getEnv_4484_,
                    v___f_4486_,
                );
                return v___x_4487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms(
    mut v_n_4504_: *mut LeanObject,
    mut v_00_u03b1_4505_: *mut LeanObject,
    mut v_inst_4506_: *mut LeanObject,
    mut v_inst_4507_: *mut LeanObject,
    mut v_inst_4508_: *mut LeanObject,
    mut v_inst_4509_: *mut LeanObject,
    mut v_preDefs_4510_: *mut LeanObject,
    mut v_k_4511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    v___x_4512_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___redArg(v_inst_4506_, v_inst_4507_, v_inst_4508_, v_inst_4509_, v_preDefs_4510_, v_k_4511_);
    return v___x_4512_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(
    mut v_k_4513_: *mut LeanObject,
    mut v_b_4514_: *mut LeanObject,
    mut v_c_4515_: *mut LeanObject,
    mut v___y_4516_: *mut LeanObject,
    mut v___y_4517_: *mut LeanObject,
    mut v___y_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4519_);
    lean_inc_ref(v___y_4518_);
    lean_inc(v___y_4517_);
    lean_inc_ref(v___y_4516_);
    v___x_4521_ = lean_apply_7(
        v_k_4513_,
        v_b_4514_,
        v_c_4515_,
        v___y_4516_,
        v___y_4517_,
        v___y_4518_,
        v___y_4519_,
        lean_box(0),
    );
    return v___x_4521_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed(
    mut v_k_4522_: *mut LeanObject,
    mut v_b_4523_: *mut LeanObject,
    mut v_c_4524_: *mut LeanObject,
    mut v___y_4525_: *mut LeanObject,
    mut v___y_4526_: *mut LeanObject,
    mut v___y_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
    mut v___y_4529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4530_: *mut LeanObject = core::ptr::null_mut();
    v_res_4530_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0(v_k_4522_, v_b_4523_, v_c_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
    lean_dec(v___y_4528_);
    lean_dec_ref(v___y_4527_);
    lean_dec(v___y_4526_);
    lean_dec_ref(v___y_4525_);
    return v_res_4530_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(
    mut v_e_4531_: *mut LeanObject,
    mut v_k_4532_: *mut LeanObject,
    mut v_cleanupAnnotations_4533_: u8,
    mut v___y_4534_: *mut LeanObject,
    mut v___y_4535_: *mut LeanObject,
    mut v___y_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: u8 = 0;
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4547_: u8 = 0;
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut v_a_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4539_ = lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_4539_, 0, v_k_4532_);
                v___x_4540_ = 1;
                v___x_4541_ = 0;
                v___x_4542_ = lean_box(0);
                v___x_4543_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
                    v_e_4531_,
                    v___x_4540_,
                    v___x_4541_,
                    v___x_4540_,
                    v___x_4541_,
                    v___x_4542_,
                    v___f_4539_,
                    v_cleanupAnnotations_4533_,
                    v___y_4534_,
                    v___y_4535_,
                    v___y_4536_,
                    v___y_4537_,
                );
                if lean_obj_tag(v___x_4543_) == 0 {
                    v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
                    v_isSharedCheck_4551_ = (!lean_is_exclusive(v___x_4543_)) as u8;
                    if v_isSharedCheck_4551_ == 0 {
                        v___x_4546_ = v___x_4543_;
                        v_isShared_4547_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4544_);
                        lean_dec(v___x_4543_);
                        v___x_4546_ = lean_box(0);
                        v_isShared_4547_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4552_ = lean_ctor_get(v___x_4543_, 0);
                    v_isSharedCheck_4559_ = (!lean_is_exclusive(v___x_4543_)) as u8;
                    if v_isSharedCheck_4559_ == 0 {
                        v___x_4554_ = v___x_4543_;
                        v_isShared_4555_ = v_isSharedCheck_4559_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4552_);
                        lean_dec(v___x_4543_);
                        v___x_4554_ = lean_box(0);
                        v_isShared_4555_ = v_isSharedCheck_4559_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4547_ == 0 {
                    v___x_4549_ = v___x_4546_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
                    v___x_4549_ = v_reuseFailAlloc_4550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4549_;
            }
            3 => {
                if v_isShared_4555_ == 0 {
                    v___x_4557_ = v___x_4554_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
                    v___x_4557_ = v_reuseFailAlloc_4558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg___boxed(
    mut v_e_4560_: *mut LeanObject,
    mut v_k_4561_: *mut LeanObject,
    mut v_cleanupAnnotations_4562_: *mut LeanObject,
    mut v___y_4563_: *mut LeanObject,
    mut v___y_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
    mut v___y_4566_: *mut LeanObject,
    mut v___y_4567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4568_: u8 = 0;
    let mut v_res_4569_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4568_ = (lean_unbox(v_cleanupAnnotations_4562_) as u8);
    v_res_4569_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_4560_, v_k_4561_, v_cleanupAnnotations_boxed_4568_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
    lean_dec(v___y_4566_);
    lean_dec_ref(v___y_4565_);
    lean_dec(v___y_4564_);
    lean_dec_ref(v___y_4563_);
    return v_res_4569_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(
    mut v_00_u03b1_4570_: *mut LeanObject,
    mut v_e_4571_: *mut LeanObject,
    mut v_k_4572_: *mut LeanObject,
    mut v_cleanupAnnotations_4573_: u8,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
    mut v___y_4577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    v___x_4579_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_e_4571_, v_k_4572_, v_cleanupAnnotations_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
    return v___x_4579_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___boxed(
    mut v_00_u03b1_4580_: *mut LeanObject,
    mut v_e_4581_: *mut LeanObject,
    mut v_k_4582_: *mut LeanObject,
    mut v_cleanupAnnotations_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4589_: u8 = 0;
    let mut v_res_4590_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4589_ = (lean_unbox(v_cleanupAnnotations_4583_) as u8);
    v_res_4590_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1(v_00_u03b1_4580_, v_e_4581_, v_k_4582_, v_cleanupAnnotations_boxed_4589_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
    lean_dec(v___y_4587_);
    lean_dec_ref(v___y_4586_);
    lean_dec(v___y_4585_);
    lean_dec_ref(v___y_4584_);
    return v_res_4590_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(
    mut v___x_4594_: *mut LeanObject,
    mut v___y_4595_: *mut LeanObject,
    mut v___y_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4601_: u8 = 0;
    v_options_4600_ = lean_ctor_get(v___y_4597_, 2);
    v_hasTrace_4601_ = lean_ctor_get_uint8(
        v_options_4600_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_4601_ == 0 {
        let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_4594_);
        v___x_4602_ = lean_box((v_hasTrace_4601_) as usize);
        v___x_4603_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4603_, 0, v___x_4602_);
        return v___x_4603_;
    } else {
        let mut v_inheritedTraceOptions_4604_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4607_: u8 = 0;
        let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_4604_ = lean_ctor_get(v___y_4597_, 13);
        v___x_4605_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1;
        v___x_4606_ = l_Lean_Name_append(v___x_4605_, v___x_4594_);
        v___x_4607_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_4604_,
            v_options_4600_,
            v___x_4606_,
        );
        lean_dec(v___x_4606_);
        v___x_4608_ = lean_box((v___x_4607_) as usize);
        v___x_4609_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4609_, 0, v___x_4608_);
        return v___x_4609_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___boxed(
    mut v___x_4610_: *mut LeanObject,
    mut v___y_4611_: *mut LeanObject,
    mut v___y_4612_: *mut LeanObject,
    mut v___y_4613_: *mut LeanObject,
    mut v___y_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4616_: *mut LeanObject = core::ptr::null_mut();
    v_res_4616_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
    lean_dec(v___y_4614_);
    lean_dec_ref(v___y_4613_);
    lean_dec(v___y_4612_);
    lean_dec_ref(v___y_4611_);
    return v_res_4616_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(
    mut v_x_4617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_indIdx_4618_: *mut LeanObject = core::ptr::null_mut();
    v_indIdx_4618_ = lean_ctor_get(v_x_4617_, 5);
    lean_inc(v_indIdx_4618_);
    return v_indIdx_4618_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1___boxed(
    mut v_x_4619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4620_: *mut LeanObject = core::ptr::null_mut();
    v_res_4620_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__1(v_x_4619_);
    lean_dec_ref(v_x_4619_);
    return v_res_4620_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(
    mut v_as_4621_: *mut LeanObject,
    mut v_i_4622_: usize,
    mut v_stop_4623_: usize,
    mut v_b_4624_: *mut LeanObject,
    mut v___y_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4630_: u8 = 0;
    let mut v___x_21776__overap_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: usize = 0;
    let mut v___x_4635_: usize = 0;
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4630_ = lean_usize_dec_eq(v_i_4622_, v_stop_4623_);
                if v___x_4630_ == 0 {
                    v___x_21776__overap_4631_ = lean_array_uget_borrowed(v_as_4621_, v_i_4622_);
                    lean_inc(v___x_21776__overap_4631_);
                    lean_inc(v___y_4628_);
                    lean_inc_ref(v___y_4627_);
                    lean_inc(v___y_4626_);
                    lean_inc_ref(v___y_4625_);
                    v___x_4632_ = lean_apply_5(
                        v___x_21776__overap_4631_,
                        v___y_4625_,
                        v___y_4626_,
                        v___y_4627_,
                        v___y_4628_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4632_) == 0 {
                        v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
                        lean_inc(v_a_4633_);
                        lean_dec_ref_known(v___x_4632_, 1);
                        v___x_4634_ = 1usize;
                        v___x_4635_ = lean_usize_add(v_i_4622_, v___x_4634_);
                        v_i_4622_ = v___x_4635_;
                        v_b_4624_ = v_a_4633_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4632_;
                    }
                } else {
                    v___x_4637_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4637_, 0, v_b_4624_);
                    return v___x_4637_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13___boxed(
    mut v_as_4638_: *mut LeanObject,
    mut v_i_4639_: *mut LeanObject,
    mut v_stop_4640_: *mut LeanObject,
    mut v_b_4641_: *mut LeanObject,
    mut v___y_4642_: *mut LeanObject,
    mut v___y_4643_: *mut LeanObject,
    mut v___y_4644_: *mut LeanObject,
    mut v___y_4645_: *mut LeanObject,
    mut v___y_4646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4647_: usize = 0;
    let mut v_stop_boxed_4648_: usize = 0;
    let mut v_res_4649_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4647_ = lean_unbox_usize(v_i_4639_);
    lean_dec(v_i_4639_);
    v_stop_boxed_4648_ = lean_unbox_usize(v_stop_4640_);
    lean_dec(v_stop_4640_);
    v_res_4649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_as_4638_, v_i_boxed_4647_, v_stop_boxed_4648_, v_b_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
    lean_dec(v___y_4645_);
    lean_dec_ref(v___y_4644_);
    lean_dec(v___y_4643_);
    lean_dec_ref(v___y_4642_);
    lean_dec_ref(v_as_4638_);
    return v_res_4649_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(
    mut v_as_4650_: *mut LeanObject,
    mut v_i_4651_: usize,
    mut v_stop_4652_: usize,
    mut v_b_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4657_: u8 = 0;
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: usize = 0;
    let mut v___x_4662_: usize = 0;
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4657_ = lean_usize_dec_eq(v_i_4651_, v_stop_4652_);
                if v___x_4657_ == 0 {
                    v___x_4658_ = lean_array_uget_borrowed(v_as_4650_, v_i_4651_);
                    v___x_4659_ =
                        l_Lean_Elab_addAsAxiom___redArg(v___x_4658_, v___y_4654_, v___y_4655_);
                    if lean_obj_tag(v___x_4659_) == 0 {
                        v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
                        lean_inc(v_a_4660_);
                        lean_dec_ref_known(v___x_4659_, 1);
                        v___x_4661_ = 1usize;
                        v___x_4662_ = lean_usize_add(v_i_4651_, v___x_4661_);
                        v_i_4651_ = v___x_4662_;
                        v_b_4653_ = v_a_4660_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4659_;
                    }
                } else {
                    v___x_4664_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4664_, 0, v_b_4653_);
                    return v___x_4664_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg___boxed(
    mut v_as_4665_: *mut LeanObject,
    mut v_i_4666_: *mut LeanObject,
    mut v_stop_4667_: *mut LeanObject,
    mut v_b_4668_: *mut LeanObject,
    mut v___y_4669_: *mut LeanObject,
    mut v___y_4670_: *mut LeanObject,
    mut v___y_4671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4672_: usize = 0;
    let mut v_stop_boxed_4673_: usize = 0;
    let mut v_res_4674_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4672_ = lean_unbox_usize(v_i_4666_);
    lean_dec(v_i_4666_);
    v_stop_boxed_4673_ = lean_unbox_usize(v_stop_4667_);
    lean_dec(v_stop_4667_);
    v_res_4674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_4665_, v_i_boxed_4672_, v_stop_boxed_4673_, v_b_4668_, v___y_4669_, v___y_4670_);
    lean_dec(v___y_4670_);
    lean_dec_ref(v___y_4669_);
    lean_dec_ref(v_as_4665_);
    return v_res_4674_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(
    mut v_as_4675_: *mut LeanObject,
    mut v_i_4676_: usize,
    mut v_stop_4677_: usize,
    mut v_b_4678_: *mut LeanObject,
    mut v___y_4679_: *mut LeanObject,
    mut v___y_4680_: *mut LeanObject,
    mut v___y_4681_: *mut LeanObject,
    mut v___y_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    v___x_4684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___redArg(v_as_4675_, v_i_4676_, v_stop_4677_, v_b_4678_, v___y_4681_, v___y_4682_);
    return v___x_4684_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed(
    mut v_as_4685_: *mut LeanObject,
    mut v_i_4686_: *mut LeanObject,
    mut v_stop_4687_: *mut LeanObject,
    mut v_b_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
    mut v___y_4692_: *mut LeanObject,
    mut v___y_4693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4694_: usize = 0;
    let mut v_stop_boxed_4695_: usize = 0;
    let mut v_res_4696_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4694_ = lean_unbox_usize(v_i_4686_);
    lean_dec(v_i_4686_);
    v_stop_boxed_4695_ = lean_unbox_usize(v_stop_4687_);
    lean_dec(v_stop_4687_);
    v_res_4696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24(v_as_4685_, v_i_boxed_4694_, v_stop_boxed_4695_, v_b_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_);
    lean_dec(v___y_4692_);
    lean_dec_ref(v___y_4691_);
    lean_dec(v___y_4690_);
    lean_dec_ref(v___y_4689_);
    lean_dec_ref(v_as_4685_);
    return v_res_4696_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    v___x_4697_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4697_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    v___x_4698_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__0);
    v___x_4699_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4699_, 0, v___x_4698_);
    return v___x_4699_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    v___x_4700_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
    v___x_4701_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4701_, 0, v___x_4700_);
    lean_ctor_set(v___x_4701_, 1, v___x_4700_);
    return v___x_4701_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    v___x_4702_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__1);
    v___x_4703_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4703_, 0, v___x_4702_);
    lean_ctor_set(v___x_4703_, 1, v___x_4702_);
    lean_ctor_set(v___x_4703_, 2, v___x_4702_);
    lean_ctor_set(v___x_4703_, 3, v___x_4702_);
    lean_ctor_set(v___x_4703_, 4, v___x_4702_);
    lean_ctor_set(v___x_4703_, 5, v___x_4702_);
    return v___x_4703_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(
    mut v_env_4704_: *mut LeanObject,
    mut v___y_4705_: *mut LeanObject,
    mut v___y_4706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4718_: u8 = 0;
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4730_: u8 = 0;
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4738_: u8 = 0;
    let mut v_unused_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut v_unused_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4708_ = lean_st_ref_take(v___y_4706_);
                v_nextMacroScope_4709_ = lean_ctor_get(v___x_4708_, 1);
                v_ngen_4710_ = lean_ctor_get(v___x_4708_, 2);
                v_auxDeclNGen_4711_ = lean_ctor_get(v___x_4708_, 3);
                v_traceState_4712_ = lean_ctor_get(v___x_4708_, 4);
                v_messages_4713_ = lean_ctor_get(v___x_4708_, 6);
                v_infoState_4714_ = lean_ctor_get(v___x_4708_, 7);
                v_snapshotTasks_4715_ = lean_ctor_get(v___x_4708_, 8);
                v_isSharedCheck_4741_ = (!lean_is_exclusive(v___x_4708_)) as u8;
                if v_isSharedCheck_4741_ == 0 {
                    v_unused_4742_ = lean_ctor_get(v___x_4708_, 5);
                    lean_dec(v_unused_4742_);
                    v_unused_4743_ = lean_ctor_get(v___x_4708_, 0);
                    lean_dec(v_unused_4743_);
                    v___x_4717_ = v___x_4708_;
                    v_isShared_4718_ = v_isSharedCheck_4741_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4715_);
                    lean_inc(v_infoState_4714_);
                    lean_inc(v_messages_4713_);
                    lean_inc(v_traceState_4712_);
                    lean_inc(v_auxDeclNGen_4711_);
                    lean_inc(v_ngen_4710_);
                    lean_inc(v_nextMacroScope_4709_);
                    lean_dec(v___x_4708_);
                    v___x_4717_ = lean_box(0);
                    v_isShared_4718_ = v_isSharedCheck_4741_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4719_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
                if v_isShared_4718_ == 0 {
                    lean_ctor_set(v___x_4717_, 5, v___x_4719_);
                    lean_ctor_set(v___x_4717_, 0, v_env_4704_);
                    v___x_4721_ = v___x_4717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_env_4704_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 1, v_nextMacroScope_4709_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 2, v_ngen_4710_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 3, v_auxDeclNGen_4711_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 4, v_traceState_4712_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 5, v___x_4719_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 6, v_messages_4713_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 7, v_infoState_4714_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 8, v_snapshotTasks_4715_);
                    v___x_4721_ = v_reuseFailAlloc_4740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4722_ = lean_st_ref_set(v___y_4706_, v___x_4721_);
                v___x_4723_ = lean_st_ref_take(v___y_4705_);
                v_mctx_4724_ = lean_ctor_get(v___x_4723_, 0);
                v_zetaDeltaFVarIds_4725_ = lean_ctor_get(v___x_4723_, 2);
                v_postponed_4726_ = lean_ctor_get(v___x_4723_, 3);
                v_diag_4727_ = lean_ctor_get(v___x_4723_, 4);
                v_isSharedCheck_4738_ = (!lean_is_exclusive(v___x_4723_)) as u8;
                if v_isSharedCheck_4738_ == 0 {
                    v_unused_4739_ = lean_ctor_get(v___x_4723_, 1);
                    lean_dec(v_unused_4739_);
                    v___x_4729_ = v___x_4723_;
                    v_isShared_4730_ = v_isSharedCheck_4738_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_4727_);
                    lean_inc(v_postponed_4726_);
                    lean_inc(v_zetaDeltaFVarIds_4725_);
                    lean_inc(v_mctx_4724_);
                    lean_dec(v___x_4723_);
                    v___x_4729_ = lean_box(0);
                    v_isShared_4730_ = v_isSharedCheck_4738_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4731_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
                if v_isShared_4730_ == 0 {
                    lean_ctor_set(v___x_4729_, 1, v___x_4731_);
                    v___x_4733_ = v___x_4729_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_mctx_4724_);
                    lean_ctor_set(v_reuseFailAlloc_4737_, 1, v___x_4731_);
                    lean_ctor_set(v_reuseFailAlloc_4737_, 2, v_zetaDeltaFVarIds_4725_);
                    lean_ctor_set(v_reuseFailAlloc_4737_, 3, v_postponed_4726_);
                    lean_ctor_set(v_reuseFailAlloc_4737_, 4, v_diag_4727_);
                    v___x_4733_ = v_reuseFailAlloc_4737_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4734_ = lean_st_ref_set(v___y_4705_, v___x_4733_);
                v___x_4735_ = lean_box(0);
                v___x_4736_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4736_, 0, v___x_4735_);
                return v___x_4736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___boxed(
    mut v_env_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
    mut v___y_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4748_: *mut LeanObject = core::ptr::null_mut();
    v_res_4748_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_4744_, v___y_4745_, v___y_4746_);
    lean_dec(v___y_4746_);
    lean_dec(v___y_4745_);
    return v_res_4748_;
}
pub unsafe fn l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(
    mut v_env_4749_: *mut LeanObject,
    mut v_x_4750_: *mut LeanObject,
    mut v___y_4751_: *mut LeanObject,
    mut v___y_4752_: *mut LeanObject,
    mut v___y_4753_: *mut LeanObject,
    mut v___y_4754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4763_: u8 = 0;
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4767_: u8 = 0;
    let mut v_unused_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4775_: u8 = 0;
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4779_: u8 = 0;
    let mut v_unused_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4756_ = lean_st_ref_get(v___y_4754_);
                v_env_4757_ = lean_ctor_get(v___x_4756_, 0);
                lean_inc_ref(v_env_4757_);
                lean_dec(v___x_4756_);
                v___x_4769_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_4749_, v___y_4752_, v___y_4754_);
                lean_dec_ref(v___x_4769_);
                lean_inc(v___y_4754_);
                lean_inc_ref(v___y_4753_);
                lean_inc(v___y_4752_);
                lean_inc_ref(v___y_4751_);
                v___x_4770_ = lean_apply_5(
                    v_x_4750_,
                    v___y_4751_,
                    v___y_4752_,
                    v___y_4753_,
                    v___y_4754_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4770_) == 0 {
                    v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
                    lean_inc(v_a_4771_);
                    lean_dec_ref_known(v___x_4770_, 1);
                    v___x_4772_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_4757_, v___y_4752_, v___y_4754_);
                    v_isSharedCheck_4779_ = (!lean_is_exclusive(v___x_4772_)) as u8;
                    if v_isSharedCheck_4779_ == 0 {
                        v_unused_4780_ = lean_ctor_get(v___x_4772_, 0);
                        lean_dec(v_unused_4780_);
                        v___x_4774_ = v___x_4772_;
                        v_isShared_4775_ = v_isSharedCheck_4779_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_4772_);
                        v___x_4774_ = lean_box(0);
                        v_isShared_4775_ = v_isSharedCheck_4779_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4781_ = lean_ctor_get(v___x_4770_, 0);
                    lean_inc(v_a_4781_);
                    lean_dec_ref_known(v___x_4770_, 1);
                    v_a_4759_ = v_a_4781_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4760_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_4757_, v___y_4752_, v___y_4754_);
                v_isSharedCheck_4767_ = (!lean_is_exclusive(v___x_4760_)) as u8;
                if v_isSharedCheck_4767_ == 0 {
                    v_unused_4768_ = lean_ctor_get(v___x_4760_, 0);
                    lean_dec(v_unused_4768_);
                    v___x_4762_ = v___x_4760_;
                    v_isShared_4763_ = v_isSharedCheck_4767_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_4760_);
                    v___x_4762_ = lean_box(0);
                    v_isShared_4763_ = v_isSharedCheck_4767_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4763_ == 0 {
                    lean_ctor_set_tag(v___x_4762_, 1);
                    lean_ctor_set(v___x_4762_, 0, v_a_4759_);
                    v___x_4765_ = v___x_4762_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4759_);
                    v___x_4765_ = v_reuseFailAlloc_4766_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4765_;
            }
            4 => {
                if v_isShared_4775_ == 0 {
                    lean_ctor_set(v___x_4774_, 0, v_a_4771_);
                    v___x_4777_ = v___x_4774_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_a_4771_);
                    v___x_4777_ = v_reuseFailAlloc_4778_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg___boxed(
    mut v_env_4782_: *mut LeanObject,
    mut v_x_4783_: *mut LeanObject,
    mut v___y_4784_: *mut LeanObject,
    mut v___y_4785_: *mut LeanObject,
    mut v___y_4786_: *mut LeanObject,
    mut v___y_4787_: *mut LeanObject,
    mut v___y_4788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4789_: *mut LeanObject = core::ptr::null_mut();
    v_res_4789_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_4782_, v_x_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
    lean_dec(v___y_4787_);
    lean_dec_ref(v___y_4786_);
    lean_dec(v___y_4785_);
    lean_dec_ref(v___y_4784_);
    return v_res_4789_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(
    mut v___x_4790_: *mut LeanObject,
    mut v___y_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
    mut v___y_4793_: *mut LeanObject,
    mut v___y_4794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    v___x_4796_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4796_, 0, v___x_4790_);
    return v___x_4796_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1___boxed(
    mut v___x_4797_: *mut LeanObject,
    mut v___y_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
    mut v___y_4801_: *mut LeanObject,
    mut v___y_4802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4803_: *mut LeanObject = core::ptr::null_mut();
    v_res_4803_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__1(v___x_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
    lean_dec(v___y_4801_);
    lean_dec_ref(v___y_4800_);
    lean_dec(v___y_4799_);
    lean_dec_ref(v___y_4798_);
    return v_res_4803_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(
    mut v___y_4804_: *mut LeanObject,
    mut v_k_4805_: *mut LeanObject,
    mut v___y_4806_: *mut LeanObject,
    mut v___y_4807_: *mut LeanObject,
    mut v___y_4808_: *mut LeanObject,
    mut v___y_4809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4816_: u8 = 0;
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_4809_);
                lean_inc_ref(v___y_4808_);
                lean_inc(v___y_4807_);
                lean_inc_ref(v___y_4806_);
                v___x_4811_ = lean_apply_5(
                    v___y_4804_,
                    v___y_4806_,
                    v___y_4807_,
                    v___y_4808_,
                    v___y_4809_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4811_) == 0 {
                    lean_dec_ref_known(v___x_4811_, 1);
                    v___x_4812_ = lean_apply_5(
                        v_k_4805_,
                        v___y_4806_,
                        v___y_4807_,
                        v___y_4808_,
                        v___y_4809_,
                        lean_box(0),
                    );
                    return v___x_4812_;
                } else {
                    lean_dec(v___y_4809_);
                    lean_dec_ref(v___y_4808_);
                    lean_dec(v___y_4807_);
                    lean_dec_ref(v___y_4806_);
                    lean_dec_ref(v_k_4805_);
                    v_a_4813_ = lean_ctor_get(v___x_4811_, 0);
                    v_isSharedCheck_4820_ = (!lean_is_exclusive(v___x_4811_)) as u8;
                    if v_isSharedCheck_4820_ == 0 {
                        v___x_4815_ = v___x_4811_;
                        v_isShared_4816_ = v_isSharedCheck_4820_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4813_);
                        lean_dec(v___x_4811_);
                        v___x_4815_ = lean_box(0);
                        v_isShared_4816_ = v_isSharedCheck_4820_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4816_ == 0 {
                    v___x_4818_ = v___x_4815_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
                    v___x_4818_ = v_reuseFailAlloc_4819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed(
    mut v___y_4821_: *mut LeanObject,
    mut v_k_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
    mut v___y_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4828_: *mut LeanObject = core::ptr::null_mut();
    v_res_4828_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0(v___y_4821_, v_k_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
    return v_res_4828_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(
    mut v_preDefs_4833_: *mut LeanObject,
    mut v_k_4834_: *mut LeanObject,
    mut v___y_4835_: *mut LeanObject,
    mut v___y_4836_: *mut LeanObject,
    mut v___y_4837_: *mut LeanObject,
    mut v___y_4838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: u8 = 0;
    let mut v___f_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u8 = 0;
    let mut v___f_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: usize = 0;
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: usize = 0;
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4847_ = lean_unsigned_to_nat(0);
                v___x_4848_ = lean_array_get_size(v_preDefs_4833_);
                v___x_4849_ = lean_box(0);
                v___x_4850_ = lean_nat_dec_lt(v___x_4847_, v___x_4848_);
                if v___x_4850_ == 0 {
                    lean_dec_ref(v_preDefs_4833_);
                    v___f_4851_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0;
                    v___y_4841_ = v___f_4851_;
                    state = 1;
                    continue;
                } else {
                    v___x_4852_ = lean_nat_dec_le(v___x_4848_, v___x_4848_);
                    if v___x_4852_ == 0 {
                        if v___x_4850_ == 0 {
                            lean_dec_ref(v_preDefs_4833_);
                            v___f_4853_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___closed__0;
                            v___y_4841_ = v___f_4853_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4854_ = lean_usize_of_nat(v___x_4848_);
                            v___x_4855_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1;
                            v___x_4856_ = lean_box_usize(v___x_4854_);
                            v___x_4857_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed as *mut core::ffi::c_void, 9, 4);
                            lean_closure_set(v___x_4857_, 0, v_preDefs_4833_);
                            lean_closure_set(v___x_4857_, 1, v___x_4855_);
                            lean_closure_set(v___x_4857_, 2, v___x_4856_);
                            lean_closure_set(v___x_4857_, 3, v___x_4849_);
                            v___y_4841_ = v___x_4857_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4858_ = lean_usize_of_nat(v___x_4848_);
                        v___x_4859_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1;
                        v___x_4860_ = lean_box_usize(v___x_4858_);
                        v___x_4861_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__24___boxed as *mut core::ffi::c_void, 9, 4);
                        lean_closure_set(v___x_4861_, 0, v_preDefs_4833_);
                        lean_closure_set(v___x_4861_, 1, v___x_4859_);
                        lean_closure_set(v___x_4861_, 2, v___x_4860_);
                        lean_closure_set(v___x_4861_, 3, v___x_4849_);
                        v___y_4841_ = v___x_4861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4842_ = lean_st_ref_get(v___y_4838_);
                v_env_4843_ = lean_ctor_get(v___x_4842_, 0);
                lean_inc_ref(v_env_4843_);
                lean_dec(v___x_4842_);
                v___f_4844_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                lean_closure_set(v___f_4844_, 0, v___y_4841_);
                lean_closure_set(v___f_4844_, 1, v_k_4834_);
                v___x_4845_ = l_Lean_Environment_unlockAsync(v_env_4843_);
                v___x_4846_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v___x_4845_, v___f_4844_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
                return v___x_4846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed(
    mut v_preDefs_4862_: *mut LeanObject,
    mut v_k_4863_: *mut LeanObject,
    mut v___y_4864_: *mut LeanObject,
    mut v___y_4865_: *mut LeanObject,
    mut v___y_4866_: *mut LeanObject,
    mut v___y_4867_: *mut LeanObject,
    mut v___y_4868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4869_: *mut LeanObject = core::ptr::null_mut();
    v_res_4869_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_4862_, v_k_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
    lean_dec(v___y_4867_);
    lean_dec_ref(v___y_4866_);
    lean_dec(v___y_4865_);
    lean_dec_ref(v___y_4864_);
    return v_res_4869_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4871_: *mut LeanObject = core::ptr::null_mut();
    v___x_4870_ = lean_box(0);
    v_dummy_4871_ = l_Lean_Expr_sort___override(v___x_4870_);
    return v_dummy_4871_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(
    mut v_a_4872_: u8,
    mut v_a_4873_: *mut LeanObject,
    mut v_a_4874_: *mut LeanObject,
    mut v_recArgInfos_4875_: *mut LeanObject,
    mut v___x_4876_: *mut LeanObject,
    mut v_preDefs_4877_: *mut LeanObject,
    mut v_a_4878_: *mut LeanObject,
    mut v_as_4879_: *mut LeanObject,
    mut v_i_4880_: *mut LeanObject,
    mut v_j_4881_: *mut LeanObject,
    mut v_bs_4882_: *mut LeanObject,
    mut v___y_4883_: *mut LeanObject,
    mut v___y_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_4889_: u8 = 0;
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4908_: u8 = 0;
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4931_: u8 = 0;
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4935_: u8 = 0;
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: u8 = 0;
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: u8 = 0;
    let mut v___x_4940_: usize = 0;
    let mut v___x_4941_: usize = 0;
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: usize = 0;
    let mut v___x_4944_: usize = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4949_: u8 = 0;
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4888_ = lean_unsigned_to_nat(0);
                v_isZero_4889_ = lean_nat_dec_eq(v_i_4880_, v_zero_4888_);
                if v_isZero_4889_ == 1 {
                    lean_dec(v_j_4881_);
                    lean_dec(v_i_4880_);
                    lean_dec_ref(v_a_4878_);
                    lean_dec_ref(v_preDefs_4877_);
                    lean_dec_ref(v___x_4876_);
                    lean_dec_ref(v_recArgInfos_4875_);
                    v___x_4890_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4890_, 0, v_bs_4882_);
                    return v___x_4890_;
                } else {
                    v___x_4891_ = l_Lean_instInhabitedExpr;
                    v_one_4892_ = lean_unsigned_to_nat(1);
                    v_n_4893_ = lean_nat_sub(v_i_4880_, v_one_4892_);
                    lean_dec(v_i_4880_);
                    v___x_4899_ = lean_array_fget_borrowed(v_as_4879_, v_j_4881_);
                    if v_a_4872_ == 0 {
                        v___x_4900_ = lean_array_get_borrowed(v___x_4891_, v_a_4873_, v_j_4881_);
                        v___x_4901_ = lean_array_get_borrowed(v___x_4891_, v_a_4874_, v_j_4881_);
                        lean_inc(v___x_4901_);
                        lean_inc(v___x_4900_);
                        lean_inc(v___x_4899_);
                        lean_inc_ref(v___x_4876_);
                        lean_inc_ref(v_recArgInfos_4875_);
                        v___x_4902_ = lean_alloc_closure(
                            l_Lean_Elab_Structural_mkBRecOnF___boxed as *mut core::ffi::c_void,
                            10,
                            5,
                        );
                        lean_closure_set(v___x_4902_, 0, v_recArgInfos_4875_);
                        lean_closure_set(v___x_4902_, 1, v___x_4876_);
                        lean_closure_set(v___x_4902_, 2, v___x_4899_);
                        lean_closure_set(v___x_4902_, 3, v___x_4900_);
                        lean_closure_set(v___x_4902_, 4, v___x_4901_);
                        lean_inc_ref(v_preDefs_4877_);
                        v___x_4903_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_4877_, v___x_4902_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
                        if lean_obj_tag(v___x_4903_) == 0 {
                            v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
                            lean_inc(v_a_4904_);
                            lean_dec_ref_known(v___x_4903_, 1);
                            v_a_4895_ = v_a_4904_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_n_4893_);
                            lean_dec_ref(v_bs_4882_);
                            lean_dec(v_j_4881_);
                            lean_dec_ref(v_a_4878_);
                            lean_dec_ref(v_preDefs_4877_);
                            lean_dec_ref(v___x_4876_);
                            lean_dec_ref(v_recArgInfos_4875_);
                            v_a_4905_ = lean_ctor_get(v___x_4903_, 0);
                            v_isSharedCheck_4912_ = (!lean_is_exclusive(v___x_4903_)) as u8;
                            if v_isSharedCheck_4912_ == 0 {
                                v___x_4907_ = v___x_4903_;
                                v_isShared_4908_ = v_isSharedCheck_4912_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_4905_);
                                lean_dec(v___x_4903_);
                                v___x_4907_ = lean_box(0);
                                v_isShared_4908_ = v_isSharedCheck_4912_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___x_4913_ = lean_array_get_borrowed(v___x_4891_, v_a_4873_, v_j_4881_);
                        v___x_4914_ = lean_array_get_borrowed(v___x_4891_, v_a_4874_, v_j_4881_);
                        lean_inc_ref(v_a_4878_);
                        v___x_4915_ = lean_apply_1(v_a_4878_, v_zero_4888_);
                        v_dummy_4916_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___closed__0);
                        v_nargs_4917_ = l_Lean_Expr_getAppNumArgs(v___x_4915_);
                        lean_inc(v_nargs_4917_);
                        v___x_4918_ = lean_mk_array(v_nargs_4917_, v_dummy_4916_);
                        v___x_4919_ = lean_nat_sub(v_nargs_4917_, v_one_4892_);
                        lean_dec(v_nargs_4917_);
                        v___x_4920_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v___x_4915_,
                            v___x_4918_,
                            v___x_4919_,
                        );
                        lean_inc(v___x_4914_);
                        lean_inc(v___x_4913_);
                        lean_inc(v___x_4899_);
                        lean_inc_ref(v___x_4876_);
                        lean_inc_ref(v_recArgInfos_4875_);
                        v___x_4921_ = lean_alloc_closure(
                            l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed
                                as *mut core::ffi::c_void,
                            11,
                            6,
                        );
                        lean_closure_set(v___x_4921_, 0, v_recArgInfos_4875_);
                        lean_closure_set(v___x_4921_, 1, v___x_4876_);
                        lean_closure_set(v___x_4921_, 2, v___x_4899_);
                        lean_closure_set(v___x_4921_, 3, v___x_4913_);
                        lean_closure_set(v___x_4921_, 4, v___x_4914_);
                        lean_closure_set(v___x_4921_, 5, v___x_4920_);
                        lean_inc_ref(v_preDefs_4877_);
                        v___x_4922_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_4877_, v___x_4921_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
                        if lean_obj_tag(v___x_4922_) == 0 {
                            v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
                            lean_inc(v_a_4923_);
                            lean_dec_ref_known(v___x_4922_, 1);
                            v_fst_4924_ = lean_ctor_get(v_a_4923_, 0);
                            lean_inc(v_fst_4924_);
                            v_snd_4925_ = lean_ctor_get(v_a_4923_, 1);
                            lean_inc(v_snd_4925_);
                            lean_dec(v_a_4923_);
                            v___x_4936_ = lean_array_get_size(v_snd_4925_);
                            v___x_4937_ = lean_nat_dec_lt(v_zero_4888_, v___x_4936_);
                            if v___x_4937_ == 0 {
                                lean_dec(v_snd_4925_);
                                v_a_4895_ = v_fst_4924_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4938_ = lean_box(0);
                                v___x_4939_ = lean_nat_dec_le(v___x_4936_, v___x_4936_);
                                if v___x_4939_ == 0 {
                                    if v___x_4937_ == 0 {
                                        lean_dec(v_snd_4925_);
                                        v_a_4895_ = v_fst_4924_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_4940_ = 0usize;
                                        v___x_4941_ = lean_usize_of_nat(v___x_4936_);
                                        v___x_4942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_4925_, v___x_4940_, v___x_4941_, v___x_4938_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
                                        lean_dec(v_snd_4925_);
                                        v___y_4927_ = v___x_4942_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v___x_4943_ = 0usize;
                                    v___x_4944_ = lean_usize_of_nat(v___x_4936_);
                                    v___x_4945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__13(v_snd_4925_, v___x_4943_, v___x_4944_, v___x_4938_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
                                    lean_dec(v_snd_4925_);
                                    v___y_4927_ = v___x_4945_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_n_4893_);
                            lean_dec_ref(v_bs_4882_);
                            lean_dec(v_j_4881_);
                            lean_dec_ref(v_a_4878_);
                            lean_dec_ref(v_preDefs_4877_);
                            lean_dec_ref(v___x_4876_);
                            lean_dec_ref(v_recArgInfos_4875_);
                            v_a_4946_ = lean_ctor_get(v___x_4922_, 0);
                            v_isSharedCheck_4953_ = (!lean_is_exclusive(v___x_4922_)) as u8;
                            if v_isSharedCheck_4953_ == 0 {
                                v___x_4948_ = v___x_4922_;
                                v_isShared_4949_ = v_isSharedCheck_4953_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4946_);
                                lean_dec(v___x_4922_);
                                v___x_4948_ = lean_box(0);
                                v_isShared_4949_ = v_isSharedCheck_4953_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4896_ = lean_nat_add(v_j_4881_, v_one_4892_);
                lean_dec(v_j_4881_);
                v___x_4897_ = lean_array_push(v_bs_4882_, v_a_4895_);
                v_i_4880_ = v_n_4893_;
                v_j_4881_ = v___x_4896_;
                v_bs_4882_ = v___x_4897_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4908_ == 0 {
                    v___x_4910_ = v___x_4907_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
                    v___x_4910_ = v_reuseFailAlloc_4911_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4910_;
            }
            4 => {
                if lean_obj_tag(v___y_4927_) == 0 {
                    lean_dec_ref_known(v___y_4927_, 1);
                    v_a_4895_ = v_fst_4924_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_fst_4924_);
                    lean_dec(v_n_4893_);
                    lean_dec_ref(v_bs_4882_);
                    lean_dec(v_j_4881_);
                    lean_dec_ref(v_a_4878_);
                    lean_dec_ref(v_preDefs_4877_);
                    lean_dec_ref(v___x_4876_);
                    lean_dec_ref(v_recArgInfos_4875_);
                    v_a_4928_ = lean_ctor_get(v___y_4927_, 0);
                    v_isSharedCheck_4935_ = (!lean_is_exclusive(v___y_4927_)) as u8;
                    if v_isSharedCheck_4935_ == 0 {
                        v___x_4930_ = v___y_4927_;
                        v_isShared_4931_ = v_isSharedCheck_4935_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4928_);
                        lean_dec(v___y_4927_);
                        v___x_4930_ = lean_box(0);
                        v_isShared_4931_ = v_isSharedCheck_4935_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4931_ == 0 {
                    v___x_4933_ = v___x_4930_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
                    v___x_4933_ = v_reuseFailAlloc_4934_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4933_;
            }
            7 => {
                if v_isShared_4949_ == 0 {
                    v___x_4951_ = v___x_4948_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
                    v___x_4951_ = v_reuseFailAlloc_4952_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg___boxed(
    mut v_a_4954_: *mut LeanObject,
    mut v_a_4955_: *mut LeanObject,
    mut v_a_4956_: *mut LeanObject,
    mut v_recArgInfos_4957_: *mut LeanObject,
    mut v___x_4958_: *mut LeanObject,
    mut v_preDefs_4959_: *mut LeanObject,
    mut v_a_4960_: *mut LeanObject,
    mut v_as_4961_: *mut LeanObject,
    mut v_i_4962_: *mut LeanObject,
    mut v_j_4963_: *mut LeanObject,
    mut v_bs_4964_: *mut LeanObject,
    mut v___y_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
    mut v___y_4967_: *mut LeanObject,
    mut v___y_4968_: *mut LeanObject,
    mut v___y_4969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_27611__boxed_4970_: u8 = 0;
    let mut v_res_4971_: *mut LeanObject = core::ptr::null_mut();
    v_a_27611__boxed_4970_ = (lean_unbox(v_a_4954_) as u8);
    v_res_4971_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_27611__boxed_4970_, v_a_4955_, v_a_4956_, v_recArgInfos_4957_, v___x_4958_, v_preDefs_4959_, v_a_4960_, v_as_4961_, v_i_4962_, v_j_4963_, v_bs_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
    lean_dec(v___y_4968_);
    lean_dec_ref(v___y_4967_);
    lean_dec(v___y_4966_);
    lean_dec_ref(v___y_4965_);
    lean_dec_ref(v_as_4961_);
    lean_dec_ref(v_a_4956_);
    lean_dec_ref(v_a_4955_);
    return v_res_4971_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(
    mut v_msgData_4972_: *mut LeanObject,
    mut v___y_4973_: *mut LeanObject,
    mut v___y_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    v___x_4978_ = lean_st_ref_get(v___y_4976_);
    v_env_4979_ = lean_ctor_get(v___x_4978_, 0);
    lean_inc_ref(v_env_4979_);
    lean_dec(v___x_4978_);
    v___x_4980_ = lean_st_ref_get(v___y_4974_);
    v_mctx_4981_ = lean_ctor_get(v___x_4980_, 0);
    lean_inc_ref(v_mctx_4981_);
    lean_dec(v___x_4980_);
    v_lctx_4982_ = lean_ctor_get(v___y_4973_, 2);
    v_options_4983_ = lean_ctor_get(v___y_4975_, 2);
    lean_inc_ref(v_options_4983_);
    lean_inc_ref(v_lctx_4982_);
    v___x_4984_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4984_, 0, v_env_4979_);
    lean_ctor_set(v___x_4984_, 1, v_mctx_4981_);
    lean_ctor_set(v___x_4984_, 2, v_lctx_4982_);
    lean_ctor_set(v___x_4984_, 3, v_options_4983_);
    v___x_4985_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4985_, 0, v___x_4984_);
    lean_ctor_set(v___x_4985_, 1, v_msgData_4972_);
    v___x_4986_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4986_, 0, v___x_4985_);
    return v___x_4986_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21___boxed(
    mut v_msgData_4987_: *mut LeanObject,
    mut v___y_4988_: *mut LeanObject,
    mut v___y_4989_: *mut LeanObject,
    mut v___y_4990_: *mut LeanObject,
    mut v___y_4991_: *mut LeanObject,
    mut v___y_4992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4993_: *mut LeanObject = core::ptr::null_mut();
    v_res_4993_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msgData_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_);
    lean_dec(v___y_4991_);
    lean_dec_ref(v___y_4990_);
    lean_dec(v___y_4989_);
    lean_dec_ref(v___y_4988_);
    return v_res_4993_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0()
-> f64 {
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: f64 = 0.0;
    v___x_4994_ = lean_unsigned_to_nat(0);
    v___x_4995_ = lean_float_of_nat(v___x_4994_);
    return v___x_4995_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(
    mut v_cls_4999_: *mut LeanObject,
    mut v_msg_5000_: *mut LeanObject,
    mut v___y_5001_: *mut LeanObject,
    mut v___y_5002_: *mut LeanObject,
    mut v___y_5003_: *mut LeanObject,
    mut v___y_5004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5024_: u8 = 0;
    let mut v_tid_5025_: u64 = 0;
    let mut v_traces_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5029_: u8 = 0;
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: f64 = 0.0;
    let mut v___x_5032_: u8 = 0;
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5050_: u8 = 0;
    let mut v_isSharedCheck_5051_: u8 = 0;
    let mut v_isSharedCheck_5052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5006_ = lean_ctor_get(v___y_5003_, 5);
                v___x_5007_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_);
                v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
                v_isSharedCheck_5052_ = (!lean_is_exclusive(v___x_5007_)) as u8;
                if v_isSharedCheck_5052_ == 0 {
                    v___x_5010_ = v___x_5007_;
                    v_isShared_5011_ = v_isSharedCheck_5052_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5008_);
                    lean_dec(v___x_5007_);
                    v___x_5010_ = lean_box(0);
                    v_isShared_5011_ = v_isSharedCheck_5052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5012_ = lean_st_ref_take(v___y_5004_);
                v_traceState_5013_ = lean_ctor_get(v___x_5012_, 4);
                v_env_5014_ = lean_ctor_get(v___x_5012_, 0);
                v_nextMacroScope_5015_ = lean_ctor_get(v___x_5012_, 1);
                v_ngen_5016_ = lean_ctor_get(v___x_5012_, 2);
                v_auxDeclNGen_5017_ = lean_ctor_get(v___x_5012_, 3);
                v_cache_5018_ = lean_ctor_get(v___x_5012_, 5);
                v_messages_5019_ = lean_ctor_get(v___x_5012_, 6);
                v_infoState_5020_ = lean_ctor_get(v___x_5012_, 7);
                v_snapshotTasks_5021_ = lean_ctor_get(v___x_5012_, 8);
                v_isSharedCheck_5051_ = (!lean_is_exclusive(v___x_5012_)) as u8;
                if v_isSharedCheck_5051_ == 0 {
                    v___x_5023_ = v___x_5012_;
                    v_isShared_5024_ = v_isSharedCheck_5051_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5021_);
                    lean_inc(v_infoState_5020_);
                    lean_inc(v_messages_5019_);
                    lean_inc(v_cache_5018_);
                    lean_inc(v_traceState_5013_);
                    lean_inc(v_auxDeclNGen_5017_);
                    lean_inc(v_ngen_5016_);
                    lean_inc(v_nextMacroScope_5015_);
                    lean_inc(v_env_5014_);
                    lean_dec(v___x_5012_);
                    v___x_5023_ = lean_box(0);
                    v_isShared_5024_ = v_isSharedCheck_5051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5025_ = lean_ctor_get_uint64(
                    v_traceState_5013_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5026_ = lean_ctor_get(v_traceState_5013_, 0);
                v_isSharedCheck_5050_ = (!lean_is_exclusive(v_traceState_5013_)) as u8;
                if v_isSharedCheck_5050_ == 0 {
                    v___x_5028_ = v_traceState_5013_;
                    v_isShared_5029_ = v_isSharedCheck_5050_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_5026_);
                    lean_dec(v_traceState_5013_);
                    v___x_5028_ = lean_box(0);
                    v_isShared_5029_ = v_isSharedCheck_5050_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5030_ = lean_box(0);
                v___x_5031_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__0);
                v___x_5032_ = 0;
                v___x_5033_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__1;
                v___x_5034_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_5034_, 0, v_cls_4999_);
                lean_ctor_set(v___x_5034_, 1, v___x_5030_);
                lean_ctor_set(v___x_5034_, 2, v___x_5033_);
                lean_ctor_set_float(
                    v___x_5034_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5031_,
                );
                lean_ctor_set_float(
                    v___x_5034_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5031_,
                );
                lean_ctor_set_uint8(
                    v___x_5034_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_5032_,
                );
                v___x_5035_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___closed__2;
                v___x_5036_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_5036_, 0, v___x_5034_);
                lean_ctor_set(v___x_5036_, 1, v_a_5008_);
                lean_ctor_set(v___x_5036_, 2, v___x_5035_);
                lean_inc(v_ref_5006_);
                v___x_5037_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5037_, 0, v_ref_5006_);
                lean_ctor_set(v___x_5037_, 1, v___x_5036_);
                v___x_5038_ = l_Lean_PersistentArray_push___redArg(v_traces_5026_, v___x_5037_);
                if v_isShared_5029_ == 0 {
                    lean_ctor_set(v___x_5028_, 0, v___x_5038_);
                    v___x_5040_ = v___x_5028_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5038_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5049_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5025_,
                    );
                    v___x_5040_ = v_reuseFailAlloc_5049_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5024_ == 0 {
                    lean_ctor_set(v___x_5023_, 4, v___x_5040_);
                    v___x_5042_ = v___x_5023_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_env_5014_);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 1, v_nextMacroScope_5015_);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 2, v_ngen_5016_);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 3, v_auxDeclNGen_5017_);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 4, v___x_5040_);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 5, v_cache_5018_);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 6, v_messages_5019_);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 7, v_infoState_5020_);
                    lean_ctor_set(v_reuseFailAlloc_5048_, 8, v_snapshotTasks_5021_);
                    v___x_5042_ = v_reuseFailAlloc_5048_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5043_ = lean_st_ref_set(v___y_5004_, v___x_5042_);
                v___x_5044_ = lean_box(0);
                if v_isShared_5011_ == 0 {
                    lean_ctor_set(v___x_5010_, 0, v___x_5044_);
                    v___x_5046_ = v___x_5010_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5044_);
                    v___x_5046_ = v_reuseFailAlloc_5047_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5046_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11___boxed(
    mut v_cls_5053_: *mut LeanObject,
    mut v_msg_5054_: *mut LeanObject,
    mut v___y_5055_: *mut LeanObject,
    mut v___y_5056_: *mut LeanObject,
    mut v___y_5057_: *mut LeanObject,
    mut v___y_5058_: *mut LeanObject,
    mut v___y_5059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5060_: *mut LeanObject = core::ptr::null_mut();
    v_res_5060_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v_cls_5053_, v_msg_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
    lean_dec(v___y_5058_);
    lean_dec_ref(v___y_5057_);
    lean_dec(v___y_5056_);
    lean_dec_ref(v___y_5055_);
    return v_res_5060_;
}
pub unsafe fn l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(
    mut v_as_5061_: *mut LeanObject,
    mut v_bs_5062_: *mut LeanObject,
    mut v_i_5063_: *mut LeanObject,
    mut v_cs_5064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: u8 = 0;
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: u8 = 0;
    let mut v_a_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5071_: u8 = 0;
    let mut v_levelParams_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termination_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5081_: u8 = 0;
    let mut v_b_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v_unused_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5065_ = lean_array_get_size(v_as_5061_);
                v___x_5066_ = lean_nat_dec_lt(v_i_5063_, v___x_5065_);
                if v___x_5066_ == 0 {
                    lean_dec(v_i_5063_);
                    return v_cs_5064_;
                } else {
                    v___x_5067_ = lean_array_get_size(v_bs_5062_);
                    v___x_5068_ = lean_nat_dec_lt(v_i_5063_, v___x_5067_);
                    if v___x_5068_ == 0 {
                        lean_dec(v_i_5063_);
                        return v_cs_5064_;
                    } else {
                        v_a_5069_ = lean_array_fget(v_as_5061_, v_i_5063_);
                        v_ref_5070_ = lean_ctor_get(v_a_5069_, 0);
                        v_kind_5071_ = lean_ctor_get_uint8(
                            v_a_5069_,
                            (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                        );
                        v_levelParams_5072_ = lean_ctor_get(v_a_5069_, 1);
                        v_modifiers_5073_ = lean_ctor_get(v_a_5069_, 2);
                        v_declName_5074_ = lean_ctor_get(v_a_5069_, 3);
                        v_binders_5075_ = lean_ctor_get(v_a_5069_, 4);
                        v_numSectionVars_5076_ = lean_ctor_get(v_a_5069_, 5);
                        v_type_5077_ = lean_ctor_get(v_a_5069_, 6);
                        v_termination_5078_ = lean_ctor_get(v_a_5069_, 8);
                        v_isSharedCheck_5090_ = (!lean_is_exclusive(v_a_5069_)) as u8;
                        if v_isSharedCheck_5090_ == 0 {
                            v_unused_5091_ = lean_ctor_get(v_a_5069_, 7);
                            lean_dec(v_unused_5091_);
                            v___x_5080_ = v_a_5069_;
                            v_isShared_5081_ = v_isSharedCheck_5090_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_termination_5078_);
                            lean_inc(v_type_5077_);
                            lean_inc(v_numSectionVars_5076_);
                            lean_inc(v_binders_5075_);
                            lean_inc(v_declName_5074_);
                            lean_inc(v_modifiers_5073_);
                            lean_inc(v_levelParams_5072_);
                            lean_inc(v_ref_5070_);
                            lean_dec(v_a_5069_);
                            v___x_5080_ = lean_box(0);
                            v_isShared_5081_ = v_isSharedCheck_5090_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_b_5082_ = lean_array_fget_borrowed(v_bs_5062_, v_i_5063_);
                lean_inc(v_b_5082_);
                if v_isShared_5081_ == 0 {
                    lean_ctor_set(v___x_5080_, 7, v_b_5082_);
                    v___x_5084_ = v___x_5080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 9, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_ref_5070_);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 1, v_levelParams_5072_);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 2, v_modifiers_5073_);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 3, v_declName_5074_);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 4, v_binders_5075_);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 5, v_numSectionVars_5076_);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 6, v_type_5077_);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 7, v_b_5082_);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 8, v_termination_5078_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5089_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                        v_kind_5071_,
                    );
                    v___x_5084_ = v_reuseFailAlloc_5089_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5085_ = lean_unsigned_to_nat(1);
                v___x_5086_ = lean_nat_add(v_i_5063_, v___x_5085_);
                lean_dec(v_i_5063_);
                v___x_5087_ = lean_array_push(v_cs_5064_, v___x_5084_);
                v_i_5063_ = v___x_5086_;
                v_cs_5064_ = v___x_5087_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9___boxed(
    mut v_as_5092_: *mut LeanObject,
    mut v_bs_5093_: *mut LeanObject,
    mut v_i_5094_: *mut LeanObject,
    mut v_cs_5095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5096_: *mut LeanObject = core::ptr::null_mut();
    v_res_5096_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_as_5092_, v_bs_5093_, v_i_5094_, v_cs_5095_);
    lean_dec_ref(v_bs_5093_);
    lean_dec_ref(v_as_5092_);
    return v_res_5096_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(
    mut v_a_5097_: *mut LeanObject,
    mut v_a_5098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5104_: u8 = 0;
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5097_) == 0 {
                    v___x_5099_ = l_List_reverse___redArg(v_a_5098_);
                    return v___x_5099_;
                } else {
                    v_head_5100_ = lean_ctor_get(v_a_5097_, 0);
                    v_tail_5101_ = lean_ctor_get(v_a_5097_, 1);
                    v_isSharedCheck_5110_ = (!lean_is_exclusive(v_a_5097_)) as u8;
                    if v_isSharedCheck_5110_ == 0 {
                        v___x_5103_ = v_a_5097_;
                        v_isShared_5104_ = v_isSharedCheck_5110_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5101_);
                        lean_inc(v_head_5100_);
                        lean_dec(v_a_5097_);
                        v___x_5103_ = lean_box(0);
                        v_isShared_5104_ = v_isSharedCheck_5110_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5105_ = l_Lean_MessageData_ofExpr(v_head_5100_);
                if v_isShared_5104_ == 0 {
                    lean_ctor_set(v___x_5103_, 1, v_a_5098_);
                    lean_ctor_set(v___x_5103_, 0, v___x_5105_);
                    v___x_5107_ = v___x_5103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5105_);
                    lean_ctor_set(v_reuseFailAlloc_5109_, 1, v_a_5098_);
                    v___x_5107_ = v_reuseFailAlloc_5109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5097_ = v_tail_5101_;
                v_a_5098_ = v___x_5107_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(
    mut v_fixedParamPerms_5111_: *mut LeanObject,
    mut v___x_5112_: *mut LeanObject,
    mut v_j_5113_: *mut LeanObject,
    mut v_xs_5114_: *mut LeanObject,
    mut v_snd_5115_: *mut LeanObject,
    mut v_isZero_5116_: u8,
    mut v_ys_5117_: *mut LeanObject,
    mut v_x_5118_: *mut LeanObject,
    mut v___y_5119_: *mut LeanObject,
    mut v___y_5120_: *mut LeanObject,
    mut v___y_5121_: *mut LeanObject,
    mut v___y_5122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_perms_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: u8 = 0;
    let mut v___x_5129_: u8 = 0;
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    v_perms_5124_ = lean_ctor_get(v_fixedParamPerms_5111_, 1);
    v___x_5125_ = lean_array_get_borrowed(v___x_5112_, v_perms_5124_, v_j_5113_);
    lean_inc_ref(v_ys_5117_);
    lean_inc(v___x_5125_);
    v___x_5126_ =
        l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_5125_, v_xs_5114_, v_ys_5117_);
    v___x_5127_ = l_Lean_Expr_beta(v_snd_5115_, v_ys_5117_);
    v___x_5128_ = 1;
    v___x_5129_ = 1;
    v___x_5130_ = l_Lean_Meta_mkLambdaFVars(
        v___x_5126_,
        v___x_5127_,
        v_isZero_5116_,
        v___x_5128_,
        v_isZero_5116_,
        v___x_5128_,
        v___x_5129_,
        v___y_5119_,
        v___y_5120_,
        v___y_5121_,
        v___y_5122_,
    );
    lean_dec_ref(v___x_5126_);
    return v___x_5130_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed(
    mut v_fixedParamPerms_5131_: *mut LeanObject,
    mut v___x_5132_: *mut LeanObject,
    mut v_j_5133_: *mut LeanObject,
    mut v_xs_5134_: *mut LeanObject,
    mut v_snd_5135_: *mut LeanObject,
    mut v_isZero_5136_: *mut LeanObject,
    mut v_ys_5137_: *mut LeanObject,
    mut v_x_5138_: *mut LeanObject,
    mut v___y_5139_: *mut LeanObject,
    mut v___y_5140_: *mut LeanObject,
    mut v___y_5141_: *mut LeanObject,
    mut v___y_5142_: *mut LeanObject,
    mut v___y_5143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_5144_: u8 = 0;
    let mut v_res_5145_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_5144_ = (lean_unbox(v_isZero_5136_) as u8);
    v_res_5145_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0(v_fixedParamPerms_5131_, v___x_5132_, v_j_5133_, v_xs_5134_, v_snd_5135_, v_isZero_boxed_5144_, v_ys_5137_, v_x_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
    lean_dec(v___y_5142_);
    lean_dec_ref(v___y_5141_);
    lean_dec(v___y_5140_);
    lean_dec_ref(v___y_5139_);
    lean_dec_ref(v_x_5138_);
    lean_dec_ref(v_xs_5134_);
    lean_dec(v_j_5133_);
    lean_dec_ref(v___x_5132_);
    lean_dec_ref(v_fixedParamPerms_5131_);
    return v_res_5145_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    v___x_5146_ = l_Array_instInhabited(lean_box(0));
    return v___x_5146_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(
    mut v_fixedParamPerms_5147_: *mut LeanObject,
    mut v_xs_5148_: *mut LeanObject,
    mut v_as_5149_: *mut LeanObject,
    mut v_i_5150_: *mut LeanObject,
    mut v_j_5151_: *mut LeanObject,
    mut v_bs_5152_: *mut LeanObject,
    mut v___y_5153_: *mut LeanObject,
    mut v___y_5154_: *mut LeanObject,
    mut v___y_5155_: *mut LeanObject,
    mut v___y_5156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5159_: u8 = 0;
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5177_: u8 = 0;
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5158_ = lean_unsigned_to_nat(0);
                v_isZero_5159_ = lean_nat_dec_eq(v_i_5150_, v_zero_5158_);
                if v_isZero_5159_ == 1 {
                    lean_dec(v_j_5151_);
                    lean_dec(v_i_5150_);
                    lean_dec_ref(v_xs_5148_);
                    lean_dec_ref(v_fixedParamPerms_5147_);
                    v___x_5160_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5160_, 0, v_bs_5152_);
                    return v___x_5160_;
                } else {
                    v___x_5161_ = lean_array_fget_borrowed(v_as_5149_, v_j_5151_);
                    v_fst_5162_ = lean_ctor_get(v___x_5161_, 0);
                    v_snd_5163_ = lean_ctor_get(v___x_5161_, 1);
                    v___x_5164_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
                    v___x_5165_ = lean_box((v_isZero_5159_) as usize);
                    lean_inc(v_snd_5163_);
                    lean_inc_ref(v_xs_5148_);
                    lean_inc(v_j_5151_);
                    lean_inc_ref(v_fixedParamPerms_5147_);
                    v___f_5166_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 6);
                    lean_closure_set(v___f_5166_, 0, v_fixedParamPerms_5147_);
                    lean_closure_set(v___f_5166_, 1, v___x_5164_);
                    lean_closure_set(v___f_5166_, 2, v_j_5151_);
                    lean_closure_set(v___f_5166_, 3, v_xs_5148_);
                    lean_closure_set(v___f_5166_, 4, v_snd_5163_);
                    lean_closure_set(v___f_5166_, 5, v___x_5165_);
                    lean_inc(v_fst_5162_);
                    v___x_5167_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_fst_5162_, v___f_5166_, v_isZero_5159_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_);
                    if lean_obj_tag(v___x_5167_) == 0 {
                        v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
                        lean_inc(v_a_5168_);
                        lean_dec_ref_known(v___x_5167_, 1);
                        v_one_5169_ = lean_unsigned_to_nat(1);
                        v_n_5170_ = lean_nat_sub(v_i_5150_, v_one_5169_);
                        lean_dec(v_i_5150_);
                        v___x_5171_ = lean_nat_add(v_j_5151_, v_one_5169_);
                        lean_dec(v_j_5151_);
                        v___x_5172_ = lean_array_push(v_bs_5152_, v_a_5168_);
                        v_i_5150_ = v_n_5170_;
                        v_j_5151_ = v___x_5171_;
                        v_bs_5152_ = v___x_5172_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5152_);
                        lean_dec(v_j_5151_);
                        lean_dec(v_i_5150_);
                        lean_dec_ref(v_xs_5148_);
                        lean_dec_ref(v_fixedParamPerms_5147_);
                        v_a_5174_ = lean_ctor_get(v___x_5167_, 0);
                        v_isSharedCheck_5181_ = (!lean_is_exclusive(v___x_5167_)) as u8;
                        if v_isSharedCheck_5181_ == 0 {
                            v___x_5176_ = v___x_5167_;
                            v_isShared_5177_ = v_isSharedCheck_5181_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5174_);
                            lean_dec(v___x_5167_);
                            v___x_5176_ = lean_box(0);
                            v_isShared_5177_ = v_isSharedCheck_5181_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5177_ == 0 {
                    v___x_5179_ = v___x_5176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5180_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5174_);
                    v___x_5179_ = v_reuseFailAlloc_5180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___boxed(
    mut v_fixedParamPerms_5182_: *mut LeanObject,
    mut v_xs_5183_: *mut LeanObject,
    mut v_as_5184_: *mut LeanObject,
    mut v_i_5185_: *mut LeanObject,
    mut v_j_5186_: *mut LeanObject,
    mut v_bs_5187_: *mut LeanObject,
    mut v___y_5188_: *mut LeanObject,
    mut v___y_5189_: *mut LeanObject,
    mut v___y_5190_: *mut LeanObject,
    mut v___y_5191_: *mut LeanObject,
    mut v___y_5192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5193_: *mut LeanObject = core::ptr::null_mut();
    v_res_5193_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_5182_, v_xs_5183_, v_as_5184_, v_i_5185_, v_j_5186_, v_bs_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_);
    lean_dec(v___y_5191_);
    lean_dec_ref(v___y_5190_);
    lean_dec(v___y_5189_);
    lean_dec_ref(v___y_5188_);
    lean_dec_ref(v_as_5184_);
    return v_res_5193_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(
    mut v_a_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5194_) == 0 {
                    v___x_5196_ = l_List_reverse___redArg(v_a_5195_);
                    return v___x_5196_;
                } else {
                    v_head_5197_ = lean_ctor_get(v_a_5194_, 0);
                    v_tail_5198_ = lean_ctor_get(v_a_5194_, 1);
                    v_isSharedCheck_5207_ = (!lean_is_exclusive(v_a_5194_)) as u8;
                    if v_isSharedCheck_5207_ == 0 {
                        v___x_5200_ = v_a_5194_;
                        v_isShared_5201_ = v_isSharedCheck_5207_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5198_);
                        lean_inc(v_head_5197_);
                        lean_dec(v_a_5194_);
                        v___x_5200_ = lean_box(0);
                        v_isShared_5201_ = v_isSharedCheck_5207_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5202_ = l_Lean_mkLevelParam(v_head_5197_);
                if v_isShared_5201_ == 0 {
                    lean_ctor_set(v___x_5200_, 1, v_a_5195_);
                    lean_ctor_set(v___x_5200_, 0, v___x_5202_);
                    v___x_5204_ = v___x_5200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5206_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5206_, 0, v___x_5202_);
                    lean_ctor_set(v_reuseFailAlloc_5206_, 1, v_a_5195_);
                    v___x_5204_ = v_reuseFailAlloc_5206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5194_ = v_tail_5198_;
                v_a_5195_ = v___x_5204_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    v___x_5208_ = l_instMonadEIO(lean_box(0));
    return v___x_5208_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    v___x_5213_ = l_Array_instInhabited(lean_box(0));
    return v___x_5213_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(
    mut v_msg_5214_: *mut LeanObject,
    mut v___y_5215_: *mut LeanObject,
    mut v___y_5216_: *mut LeanObject,
    mut v___y_5217_: *mut LeanObject,
    mut v___y_5218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5225_: u8 = 0;
    let mut v_toFunctor_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5232_: u8 = 0;
    let mut v___f_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v_toFunctor_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5256_: u8 = 0;
    let mut v___f_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_23903__overap_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut v_unused_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5277_: u8 = 0;
    let mut v_unused_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5281_: u8 = 0;
    let mut v_unused_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v_unused_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5220_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0_once), _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__0);
                v___x_5221_ = l_StateRefT_x27_instMonad___redArg(v___x_5220_);
                v_toApplicative_5222_ = lean_ctor_get(v___x_5221_, 0);
                v_isSharedCheck_5283_ = (!lean_is_exclusive(v___x_5221_)) as u8;
                if v_isSharedCheck_5283_ == 0 {
                    v_unused_5284_ = lean_ctor_get(v___x_5221_, 1);
                    lean_dec(v_unused_5284_);
                    v___x_5224_ = v___x_5221_;
                    v_isShared_5225_ = v_isSharedCheck_5283_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5222_);
                    lean_dec(v___x_5221_);
                    v___x_5224_ = lean_box(0);
                    v_isShared_5225_ = v_isSharedCheck_5283_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5226_ = lean_ctor_get(v_toApplicative_5222_, 0);
                v_toSeq_5227_ = lean_ctor_get(v_toApplicative_5222_, 2);
                v_toSeqLeft_5228_ = lean_ctor_get(v_toApplicative_5222_, 3);
                v_toSeqRight_5229_ = lean_ctor_get(v_toApplicative_5222_, 4);
                v_isSharedCheck_5281_ = (!lean_is_exclusive(v_toApplicative_5222_)) as u8;
                if v_isSharedCheck_5281_ == 0 {
                    v_unused_5282_ = lean_ctor_get(v_toApplicative_5222_, 1);
                    lean_dec(v_unused_5282_);
                    v___x_5231_ = v_toApplicative_5222_;
                    v_isShared_5232_ = v_isSharedCheck_5281_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5229_);
                    lean_inc(v_toSeqLeft_5228_);
                    lean_inc(v_toSeq_5227_);
                    lean_inc(v_toFunctor_5226_);
                    lean_dec(v_toApplicative_5222_);
                    v___x_5231_ = lean_box(0);
                    v_isShared_5232_ = v_isSharedCheck_5281_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5233_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__1;
                v___f_5234_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__2;
                lean_inc_ref(v_toFunctor_5226_);
                v___f_5235_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5235_, 0, v_toFunctor_5226_);
                v___f_5236_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5236_, 0, v_toFunctor_5226_);
                v___x_5237_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5237_, 0, v___f_5235_);
                lean_ctor_set(v___x_5237_, 1, v___f_5236_);
                v___f_5238_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5238_, 0, v_toSeqRight_5229_);
                v___f_5239_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5239_, 0, v_toSeqLeft_5228_);
                v___f_5240_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5240_, 0, v_toSeq_5227_);
                if v_isShared_5232_ == 0 {
                    lean_ctor_set(v___x_5231_, 4, v___f_5238_);
                    lean_ctor_set(v___x_5231_, 3, v___f_5239_);
                    lean_ctor_set(v___x_5231_, 2, v___f_5240_);
                    lean_ctor_set(v___x_5231_, 1, v___f_5233_);
                    lean_ctor_set(v___x_5231_, 0, v___x_5237_);
                    v___x_5242_ = v___x_5231_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5280_, 0, v___x_5237_);
                    lean_ctor_set(v_reuseFailAlloc_5280_, 1, v___f_5233_);
                    lean_ctor_set(v_reuseFailAlloc_5280_, 2, v___f_5240_);
                    lean_ctor_set(v_reuseFailAlloc_5280_, 3, v___f_5239_);
                    lean_ctor_set(v_reuseFailAlloc_5280_, 4, v___f_5238_);
                    v___x_5242_ = v_reuseFailAlloc_5280_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5225_ == 0 {
                    lean_ctor_set(v___x_5224_, 1, v___f_5234_);
                    lean_ctor_set(v___x_5224_, 0, v___x_5242_);
                    v___x_5244_ = v___x_5224_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5242_);
                    lean_ctor_set(v_reuseFailAlloc_5279_, 1, v___f_5234_);
                    v___x_5244_ = v_reuseFailAlloc_5279_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5245_ = l_StateRefT_x27_instMonad___redArg(v___x_5244_);
                v_toApplicative_5246_ = lean_ctor_get(v___x_5245_, 0);
                v_isSharedCheck_5277_ = (!lean_is_exclusive(v___x_5245_)) as u8;
                if v_isSharedCheck_5277_ == 0 {
                    v_unused_5278_ = lean_ctor_get(v___x_5245_, 1);
                    lean_dec(v_unused_5278_);
                    v___x_5248_ = v___x_5245_;
                    v_isShared_5249_ = v_isSharedCheck_5277_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5246_);
                    lean_dec(v___x_5245_);
                    v___x_5248_ = lean_box(0);
                    v_isShared_5249_ = v_isSharedCheck_5277_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_5250_ = lean_ctor_get(v_toApplicative_5246_, 0);
                v_toSeq_5251_ = lean_ctor_get(v_toApplicative_5246_, 2);
                v_toSeqLeft_5252_ = lean_ctor_get(v_toApplicative_5246_, 3);
                v_toSeqRight_5253_ = lean_ctor_get(v_toApplicative_5246_, 4);
                v_isSharedCheck_5275_ = (!lean_is_exclusive(v_toApplicative_5246_)) as u8;
                if v_isSharedCheck_5275_ == 0 {
                    v_unused_5276_ = lean_ctor_get(v_toApplicative_5246_, 1);
                    lean_dec(v_unused_5276_);
                    v___x_5255_ = v_toApplicative_5246_;
                    v_isShared_5256_ = v_isSharedCheck_5275_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5253_);
                    lean_inc(v_toSeqLeft_5252_);
                    lean_inc(v_toSeq_5251_);
                    lean_inc(v_toFunctor_5250_);
                    lean_dec(v_toApplicative_5246_);
                    v___x_5255_ = lean_box(0);
                    v_isShared_5256_ = v_isSharedCheck_5275_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_5257_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__3;
                v___f_5258_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__4;
                lean_inc_ref(v_toFunctor_5250_);
                v___f_5259_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5259_, 0, v_toFunctor_5250_);
                v___f_5260_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5260_, 0, v_toFunctor_5250_);
                v___x_5261_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5261_, 0, v___f_5259_);
                lean_ctor_set(v___x_5261_, 1, v___f_5260_);
                v___f_5262_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5262_, 0, v_toSeqRight_5253_);
                v___f_5263_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5263_, 0, v_toSeqLeft_5252_);
                v___f_5264_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5264_, 0, v_toSeq_5251_);
                if v_isShared_5256_ == 0 {
                    lean_ctor_set(v___x_5255_, 4, v___f_5262_);
                    lean_ctor_set(v___x_5255_, 3, v___f_5263_);
                    lean_ctor_set(v___x_5255_, 2, v___f_5264_);
                    lean_ctor_set(v___x_5255_, 1, v___f_5257_);
                    lean_ctor_set(v___x_5255_, 0, v___x_5261_);
                    v___x_5266_ = v___x_5255_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5274_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5274_, 0, v___x_5261_);
                    lean_ctor_set(v_reuseFailAlloc_5274_, 1, v___f_5257_);
                    lean_ctor_set(v_reuseFailAlloc_5274_, 2, v___f_5264_);
                    lean_ctor_set(v_reuseFailAlloc_5274_, 3, v___f_5263_);
                    lean_ctor_set(v_reuseFailAlloc_5274_, 4, v___f_5262_);
                    v___x_5266_ = v_reuseFailAlloc_5274_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5249_ == 0 {
                    lean_ctor_set(v___x_5248_, 1, v___f_5258_);
                    lean_ctor_set(v___x_5248_, 0, v___x_5266_);
                    v___x_5268_ = v___x_5248_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5273_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5266_);
                    lean_ctor_set(v_reuseFailAlloc_5273_, 1, v___f_5258_);
                    v___x_5268_ = v_reuseFailAlloc_5273_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5269_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5), core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5_once), _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___closed__5);
                v___x_5270_ = l_instInhabitedOfMonad___redArg(v___x_5268_, v___x_5269_);
                v___x_23903__overap_5271_ = lean_panic_fn_borrowed(v___x_5270_, v_msg_5214_);
                lean_dec(v___x_5270_);
                lean_inc(v___y_5218_);
                lean_inc_ref(v___y_5217_);
                lean_inc(v___y_5216_);
                lean_inc_ref(v___y_5215_);
                v___x_5272_ = lean_apply_5(
                    v___x_23903__overap_5271_,
                    v___y_5215_,
                    v___y_5216_,
                    v___y_5217_,
                    v___y_5218_,
                    lean_box(0),
                );
                return v___x_5272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg___boxed(
    mut v_msg_5285_: *mut LeanObject,
    mut v___y_5286_: *mut LeanObject,
    mut v___y_5287_: *mut LeanObject,
    mut v___y_5288_: *mut LeanObject,
    mut v___y_5289_: *mut LeanObject,
    mut v___y_5290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5291_: *mut LeanObject = core::ptr::null_mut();
    v_res_5291_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
    lean_dec(v___y_5289_);
    lean_dec_ref(v___y_5288_);
    lean_dec(v___y_5287_);
    lean_dec_ref(v___y_5286_);
    return v_res_5291_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(
    mut v_xs_5292_: *mut LeanObject,
    mut v_sz_5293_: usize,
    mut v_i_5294_: usize,
    mut v_bs_5295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5296_: u8 = 0;
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: usize = 0;
    let mut v___x_5303_: usize = 0;
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5296_ = lean_usize_dec_lt(v_i_5294_, v_sz_5293_);
                if v___x_5296_ == 0 {
                    return v_bs_5295_;
                } else {
                    v___x_5297_ = l_Lean_instInhabitedExpr;
                    v_v_5298_ = lean_array_uget(v_bs_5295_, v_i_5294_);
                    v___x_5299_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5300_ = lean_array_uset(v_bs_5295_, v_i_5294_, v___x_5299_);
                    v___x_5301_ = lean_array_get_borrowed(v___x_5297_, v_xs_5292_, v_v_5298_);
                    lean_dec(v_v_5298_);
                    v___x_5302_ = 1usize;
                    v___x_5303_ = lean_usize_add(v_i_5294_, v___x_5302_);
                    lean_inc(v___x_5301_);
                    v___x_5304_ = lean_array_uset(v_bs_x27_5300_, v_i_5294_, v___x_5301_);
                    v_i_5294_ = v___x_5303_;
                    v_bs_5295_ = v___x_5304_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13___boxed(
    mut v_xs_5306_: *mut LeanObject,
    mut v_sz_5307_: *mut LeanObject,
    mut v_i_5308_: *mut LeanObject,
    mut v_bs_5309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5310_: usize = 0;
    let mut v_i_boxed_5311_: usize = 0;
    let mut v_res_5312_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5310_ = lean_unbox_usize(v_sz_5307_);
    lean_dec(v_sz_5307_);
    v_i_boxed_5311_ = lean_unbox_usize(v_i_5308_);
    lean_dec(v_i_5308_);
    v_res_5312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_5306_, v_sz_boxed_5310_, v_i_boxed_5311_, v_bs_5309_);
    lean_dec_ref(v_xs_5306_);
    return v_res_5312_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(
    mut v_xs_5313_: *mut LeanObject,
    mut v_f_5314_: *mut LeanObject,
    mut v_as_5315_: *mut LeanObject,
    mut v_bs_5316_: *mut LeanObject,
    mut v_i_5317_: *mut LeanObject,
    mut v_cs_5318_: *mut LeanObject,
    mut v___y_5319_: *mut LeanObject,
    mut v___y_5320_: *mut LeanObject,
    mut v___y_5321_: *mut LeanObject,
    mut v___y_5322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: u8 = 0;
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: u8 = 0;
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5332_: usize = 0;
    let mut v___x_5333_: usize = 0;
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5344_: u8 = 0;
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5324_ = lean_array_get_size(v_as_5315_);
                v___x_5325_ = lean_nat_dec_lt(v_i_5317_, v___x_5324_);
                if v___x_5325_ == 0 {
                    lean_dec(v_i_5317_);
                    lean_dec_ref(v_f_5314_);
                    v___x_5326_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5326_, 0, v_cs_5318_);
                    return v___x_5326_;
                } else {
                    v___x_5327_ = lean_array_get_size(v_bs_5316_);
                    v___x_5328_ = lean_nat_dec_lt(v_i_5317_, v___x_5327_);
                    if v___x_5328_ == 0 {
                        lean_dec(v_i_5317_);
                        lean_dec_ref(v_f_5314_);
                        v___x_5329_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5329_, 0, v_cs_5318_);
                        return v___x_5329_;
                    } else {
                        v_a_5330_ = lean_array_fget_borrowed(v_as_5315_, v_i_5317_);
                        v_b_5331_ = lean_array_fget_borrowed(v_bs_5316_, v_i_5317_);
                        v_sz_5332_ = lean_array_size(v_b_5331_);
                        v___x_5333_ = 0usize;
                        lean_inc(v_b_5331_);
                        v___x_5334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__13(v_xs_5313_, v_sz_5332_, v___x_5333_, v_b_5331_);
                        lean_inc_ref(v_f_5314_);
                        lean_inc(v___y_5322_);
                        lean_inc_ref(v___y_5321_);
                        lean_inc(v___y_5320_);
                        lean_inc_ref(v___y_5319_);
                        lean_inc(v_a_5330_);
                        v___x_5335_ = lean_apply_7(
                            v_f_5314_,
                            v_a_5330_,
                            v___x_5334_,
                            v___y_5319_,
                            v___y_5320_,
                            v___y_5321_,
                            v___y_5322_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_5335_) == 0 {
                            v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
                            lean_inc(v_a_5336_);
                            lean_dec_ref_known(v___x_5335_, 1);
                            v___x_5337_ = lean_unsigned_to_nat(1);
                            v___x_5338_ = lean_nat_add(v_i_5317_, v___x_5337_);
                            lean_dec(v_i_5317_);
                            v___x_5339_ = lean_array_push(v_cs_5318_, v_a_5336_);
                            v_i_5317_ = v___x_5338_;
                            v_cs_5318_ = v___x_5339_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_cs_5318_);
                            lean_dec(v_i_5317_);
                            lean_dec_ref(v_f_5314_);
                            v_a_5341_ = lean_ctor_get(v___x_5335_, 0);
                            v_isSharedCheck_5348_ = (!lean_is_exclusive(v___x_5335_)) as u8;
                            if v_isSharedCheck_5348_ == 0 {
                                v___x_5343_ = v___x_5335_;
                                v_isShared_5344_ = v_isSharedCheck_5348_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5341_);
                                lean_dec(v___x_5335_);
                                v___x_5343_ = lean_box(0);
                                v_isShared_5344_ = v_isSharedCheck_5348_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5344_ == 0 {
                    v___x_5346_ = v___x_5343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_a_5341_);
                    v___x_5346_ = v_reuseFailAlloc_5347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg___boxed(
    mut v_xs_5349_: *mut LeanObject,
    mut v_f_5350_: *mut LeanObject,
    mut v_as_5351_: *mut LeanObject,
    mut v_bs_5352_: *mut LeanObject,
    mut v_i_5353_: *mut LeanObject,
    mut v_cs_5354_: *mut LeanObject,
    mut v___y_5355_: *mut LeanObject,
    mut v___y_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5360_: *mut LeanObject = core::ptr::null_mut();
    v_res_5360_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_5349_, v_f_5350_, v_as_5351_, v_bs_5352_, v_i_5353_, v_cs_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_);
    lean_dec(v___y_5358_);
    lean_dec_ref(v___y_5357_);
    lean_dec(v___y_5356_);
    lean_dec_ref(v___y_5355_);
    lean_dec_ref(v_bs_5352_);
    lean_dec_ref(v_as_5351_);
    lean_dec_ref(v_xs_5349_);
    return v_res_5360_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    v___x_5364_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__2;
    v___x_5365_ = lean_unsigned_to_nat(2);
    v___x_5366_ = lean_unsigned_to_nat(73);
    v___x_5367_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1;
    v___x_5368_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0;
    v___x_5369_ = l_mkPanicMessageWithDecl(
        v___x_5368_,
        v___x_5367_,
        v___x_5366_,
        v___x_5365_,
        v___x_5364_,
    );
    return v___x_5369_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    v___x_5371_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__4;
    v___x_5372_ = lean_unsigned_to_nat(2);
    v___x_5373_ = lean_unsigned_to_nat(74);
    v___x_5374_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__1;
    v___x_5375_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0;
    v___x_5376_ = l_mkPanicMessageWithDecl(
        v___x_5375_,
        v___x_5374_,
        v___x_5373_,
        v___x_5372_,
        v___x_5371_,
    );
    return v___x_5376_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(
    mut v_f_5379_: *mut LeanObject,
    mut v_positions_5380_: *mut LeanObject,
    mut v_ys_5381_: *mut LeanObject,
    mut v_xs_5382_: *mut LeanObject,
    mut v___y_5383_: *mut LeanObject,
    mut v___y_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
    mut v___y_5386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: u8 = 0;
    v___x_5388_ = lean_array_get_size(v_positions_5380_);
    v___x_5389_ = lean_array_get_size(v_ys_5381_);
    v___x_5390_ = lean_nat_dec_eq(v___x_5388_, v___x_5389_);
    if v___x_5390_ == 0 {
        let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_f_5379_);
        v___x_5391_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3_once), _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__3);
        v___x_5392_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_5391_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_);
        return v___x_5392_;
    } else {
        let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5395_: u8 = 0;
        v___x_5393_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_5380_);
        v___x_5394_ = lean_array_get_size(v_xs_5382_);
        v___x_5395_ = lean_nat_dec_eq(v___x_5393_, v___x_5394_);
        lean_dec(v___x_5393_);
        if v___x_5395_ == 0 {
            let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_f_5379_);
            v___x_5396_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5_once), _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__5);
            v___x_5397_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v___x_5396_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_);
            return v___x_5397_;
        } else {
            let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
            v___x_5398_ = lean_unsigned_to_nat(0);
            v___x_5399_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__6;
            v___x_5400_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_5382_, v_f_5379_, v_ys_5381_, v_positions_5380_, v___x_5398_, v___x_5399_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_);
            return v___x_5400_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___boxed(
    mut v_f_5401_: *mut LeanObject,
    mut v_positions_5402_: *mut LeanObject,
    mut v_ys_5403_: *mut LeanObject,
    mut v_xs_5404_: *mut LeanObject,
    mut v___y_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
    mut v___y_5409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5410_: *mut LeanObject = core::ptr::null_mut();
    v_res_5410_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_5401_, v_positions_5402_, v_ys_5403_, v_xs_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_);
    lean_dec(v___y_5408_);
    lean_dec_ref(v___y_5407_);
    lean_dec(v___y_5406_);
    lean_dec_ref(v___y_5405_);
    lean_dec_ref(v_xs_5404_);
    lean_dec_ref(v_ys_5403_);
    lean_dec_ref(v_positions_5402_);
    return v_res_5410_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(
    mut v___x_5411_: *mut LeanObject,
    mut v_a_5412_: *mut LeanObject,
    mut v_a_5413_: *mut LeanObject,
    mut v_funTypes_5414_: *mut LeanObject,
    mut v_as_5415_: *mut LeanObject,
    mut v_i_5416_: *mut LeanObject,
    mut v_j_5417_: *mut LeanObject,
    mut v_bs_5418_: *mut LeanObject,
    mut v___y_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
    mut v___y_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5425_: u8 = 0;
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5440_: u8 = 0;
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5444_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5424_ = lean_unsigned_to_nat(0);
                v_isZero_5425_ = lean_nat_dec_eq(v_i_5416_, v_zero_5424_);
                if v_isZero_5425_ == 1 {
                    lean_dec(v_j_5417_);
                    lean_dec(v_i_5416_);
                    lean_dec_ref(v_funTypes_5414_);
                    lean_dec_ref(v_a_5413_);
                    lean_dec_ref(v_a_5412_);
                    lean_dec_ref(v___x_5411_);
                    v___x_5426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5426_, 0, v_bs_5418_);
                    return v___x_5426_;
                } else {
                    v___x_5427_ = lean_array_fget_borrowed(v_as_5415_, v_j_5417_);
                    v_fst_5428_ = lean_ctor_get(v___x_5427_, 0);
                    v_snd_5429_ = lean_ctor_get(v___x_5427_, 1);
                    lean_inc(v_snd_5429_);
                    lean_inc(v_fst_5428_);
                    lean_inc_ref(v_funTypes_5414_);
                    lean_inc_ref(v_a_5413_);
                    lean_inc_ref(v_a_5412_);
                    lean_inc(v_j_5417_);
                    lean_inc_ref(v___x_5411_);
                    v___x_5430_ = l_Lean_Elab_Structural_mkBRecOnApp(
                        v___x_5411_,
                        v_j_5417_,
                        v_a_5412_,
                        v_a_5413_,
                        v_funTypes_5414_,
                        v_fst_5428_,
                        v_snd_5429_,
                        v___y_5419_,
                        v___y_5420_,
                        v___y_5421_,
                        v___y_5422_,
                    );
                    if lean_obj_tag(v___x_5430_) == 0 {
                        v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
                        lean_inc(v_a_5431_);
                        lean_dec_ref_known(v___x_5430_, 1);
                        v_one_5432_ = lean_unsigned_to_nat(1);
                        v_n_5433_ = lean_nat_sub(v_i_5416_, v_one_5432_);
                        lean_dec(v_i_5416_);
                        v___x_5434_ = lean_nat_add(v_j_5417_, v_one_5432_);
                        lean_dec(v_j_5417_);
                        v___x_5435_ = lean_array_push(v_bs_5418_, v_a_5431_);
                        v_i_5416_ = v_n_5433_;
                        v_j_5417_ = v___x_5434_;
                        v_bs_5418_ = v___x_5435_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5418_);
                        lean_dec(v_j_5417_);
                        lean_dec(v_i_5416_);
                        lean_dec_ref(v_funTypes_5414_);
                        lean_dec_ref(v_a_5413_);
                        lean_dec_ref(v_a_5412_);
                        lean_dec_ref(v___x_5411_);
                        v_a_5437_ = lean_ctor_get(v___x_5430_, 0);
                        v_isSharedCheck_5444_ = (!lean_is_exclusive(v___x_5430_)) as u8;
                        if v_isSharedCheck_5444_ == 0 {
                            v___x_5439_ = v___x_5430_;
                            v_isShared_5440_ = v_isSharedCheck_5444_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5437_);
                            lean_dec(v___x_5430_);
                            v___x_5439_ = lean_box(0);
                            v_isShared_5440_ = v_isSharedCheck_5444_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5440_ == 0 {
                    v___x_5442_ = v___x_5439_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
                    v___x_5442_ = v_reuseFailAlloc_5443_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5442_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg___boxed(
    mut v___x_5445_: *mut LeanObject,
    mut v_a_5446_: *mut LeanObject,
    mut v_a_5447_: *mut LeanObject,
    mut v_funTypes_5448_: *mut LeanObject,
    mut v_as_5449_: *mut LeanObject,
    mut v_i_5450_: *mut LeanObject,
    mut v_j_5451_: *mut LeanObject,
    mut v_bs_5452_: *mut LeanObject,
    mut v___y_5453_: *mut LeanObject,
    mut v___y_5454_: *mut LeanObject,
    mut v___y_5455_: *mut LeanObject,
    mut v___y_5456_: *mut LeanObject,
    mut v___y_5457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5458_: *mut LeanObject = core::ptr::null_mut();
    v_res_5458_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_5445_, v_a_5446_, v_a_5447_, v_funTypes_5448_, v_as_5449_, v_i_5450_, v_j_5451_, v_bs_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_);
    lean_dec(v___y_5456_);
    lean_dec_ref(v___y_5455_);
    lean_dec(v___y_5454_);
    lean_dec_ref(v___y_5453_);
    lean_dec_ref(v_as_5449_);
    return v_res_5458_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(
    mut v_declName_5459_: *mut LeanObject,
    mut v_s_5460_: u8,
    mut v___y_5461_: *mut LeanObject,
    mut v___y_5462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5475_: u8 = 0;
    let mut v___x_5476_: u8 = 0;
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5490_: u8 = 0;
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5498_: u8 = 0;
    let mut v_unused_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5501_: u8 = 0;
    let mut v_unused_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5464_ = lean_st_ref_take(v___y_5462_);
                v_env_5465_ = lean_ctor_get(v___x_5464_, 0);
                v_nextMacroScope_5466_ = lean_ctor_get(v___x_5464_, 1);
                v_ngen_5467_ = lean_ctor_get(v___x_5464_, 2);
                v_auxDeclNGen_5468_ = lean_ctor_get(v___x_5464_, 3);
                v_traceState_5469_ = lean_ctor_get(v___x_5464_, 4);
                v_messages_5470_ = lean_ctor_get(v___x_5464_, 6);
                v_infoState_5471_ = lean_ctor_get(v___x_5464_, 7);
                v_snapshotTasks_5472_ = lean_ctor_get(v___x_5464_, 8);
                v_isSharedCheck_5501_ = (!lean_is_exclusive(v___x_5464_)) as u8;
                if v_isSharedCheck_5501_ == 0 {
                    v_unused_5502_ = lean_ctor_get(v___x_5464_, 5);
                    lean_dec(v_unused_5502_);
                    v___x_5474_ = v___x_5464_;
                    v_isShared_5475_ = v_isSharedCheck_5501_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5472_);
                    lean_inc(v_infoState_5471_);
                    lean_inc(v_messages_5470_);
                    lean_inc(v_traceState_5469_);
                    lean_inc(v_auxDeclNGen_5468_);
                    lean_inc(v_ngen_5467_);
                    lean_inc(v_nextMacroScope_5466_);
                    lean_inc(v_env_5465_);
                    lean_dec(v___x_5464_);
                    v___x_5474_ = lean_box(0);
                    v_isShared_5475_ = v_isSharedCheck_5501_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5476_ = 0;
                v___x_5477_ = lean_box(0);
                v___x_5478_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_5465_,
                    v_declName_5459_,
                    v_s_5460_,
                    v___x_5476_,
                    v___x_5477_,
                );
                v___x_5479_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
                if v_isShared_5475_ == 0 {
                    lean_ctor_set(v___x_5474_, 5, v___x_5479_);
                    lean_ctor_set(v___x_5474_, 0, v___x_5478_);
                    v___x_5481_ = v___x_5474_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5500_, 0, v___x_5478_);
                    lean_ctor_set(v_reuseFailAlloc_5500_, 1, v_nextMacroScope_5466_);
                    lean_ctor_set(v_reuseFailAlloc_5500_, 2, v_ngen_5467_);
                    lean_ctor_set(v_reuseFailAlloc_5500_, 3, v_auxDeclNGen_5468_);
                    lean_ctor_set(v_reuseFailAlloc_5500_, 4, v_traceState_5469_);
                    lean_ctor_set(v_reuseFailAlloc_5500_, 5, v___x_5479_);
                    lean_ctor_set(v_reuseFailAlloc_5500_, 6, v_messages_5470_);
                    lean_ctor_set(v_reuseFailAlloc_5500_, 7, v_infoState_5471_);
                    lean_ctor_set(v_reuseFailAlloc_5500_, 8, v_snapshotTasks_5472_);
                    v___x_5481_ = v_reuseFailAlloc_5500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5482_ = lean_st_ref_set(v___y_5462_, v___x_5481_);
                v___x_5483_ = lean_st_ref_take(v___y_5461_);
                v_mctx_5484_ = lean_ctor_get(v___x_5483_, 0);
                v_zetaDeltaFVarIds_5485_ = lean_ctor_get(v___x_5483_, 2);
                v_postponed_5486_ = lean_ctor_get(v___x_5483_, 3);
                v_diag_5487_ = lean_ctor_get(v___x_5483_, 4);
                v_isSharedCheck_5498_ = (!lean_is_exclusive(v___x_5483_)) as u8;
                if v_isSharedCheck_5498_ == 0 {
                    v_unused_5499_ = lean_ctor_get(v___x_5483_, 1);
                    lean_dec(v_unused_5499_);
                    v___x_5489_ = v___x_5483_;
                    v_isShared_5490_ = v_isSharedCheck_5498_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_5487_);
                    lean_inc(v_postponed_5486_);
                    lean_inc(v_zetaDeltaFVarIds_5485_);
                    lean_inc(v_mctx_5484_);
                    lean_dec(v___x_5483_);
                    v___x_5489_ = lean_box(0);
                    v_isShared_5490_ = v_isSharedCheck_5498_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5491_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
                if v_isShared_5490_ == 0 {
                    lean_ctor_set(v___x_5489_, 1, v___x_5491_);
                    v___x_5493_ = v___x_5489_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5497_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_mctx_5484_);
                    lean_ctor_set(v_reuseFailAlloc_5497_, 1, v___x_5491_);
                    lean_ctor_set(v_reuseFailAlloc_5497_, 2, v_zetaDeltaFVarIds_5485_);
                    lean_ctor_set(v_reuseFailAlloc_5497_, 3, v_postponed_5486_);
                    lean_ctor_set(v_reuseFailAlloc_5497_, 4, v_diag_5487_);
                    v___x_5493_ = v_reuseFailAlloc_5497_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5494_ = lean_st_ref_set(v___y_5461_, v___x_5493_);
                v___x_5495_ = lean_box(0);
                v___x_5496_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5496_, 0, v___x_5495_);
                return v___x_5496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg___boxed(
    mut v_declName_5503_: *mut LeanObject,
    mut v_s_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_5508_: u8 = 0;
    let mut v_res_5509_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_5508_ = (lean_unbox(v_s_5504_) as u8);
    v_res_5509_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_5503_, v_s_boxed_5508_, v___y_5505_, v___y_5506_);
    lean_dec(v___y_5506_);
    lean_dec(v___y_5505_);
    return v_res_5509_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(
    mut v_declName_5510_: *mut LeanObject,
    mut v___y_5511_: *mut LeanObject,
    mut v___y_5512_: *mut LeanObject,
    mut v___y_5513_: *mut LeanObject,
    mut v___y_5514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5516_: u8 = 0;
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    v___x_5516_ = 0;
    v___x_5517_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_5510_, v___x_5516_, v___y_5512_, v___y_5514_);
    return v___x_5517_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16___boxed(
    mut v_declName_5518_: *mut LeanObject,
    mut v___y_5519_: *mut LeanObject,
    mut v___y_5520_: *mut LeanObject,
    mut v___y_5521_: *mut LeanObject,
    mut v___y_5522_: *mut LeanObject,
    mut v___y_5523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5524_: *mut LeanObject = core::ptr::null_mut();
    v_res_5524_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v_declName_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
    lean_dec(v___y_5522_);
    lean_dec_ref(v___y_5521_);
    lean_dec(v___y_5520_);
    lean_dec_ref(v___y_5519_);
    return v_res_5524_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(
    mut v_xs_5528_: *mut LeanObject,
    mut v_a_5529_: u8,
    mut v_preDefs_5530_: *mut LeanObject,
    mut v___x_5531_: *mut LeanObject,
    mut v_as_5532_: *mut LeanObject,
    mut v_i_5533_: *mut LeanObject,
    mut v_j_5534_: *mut LeanObject,
    mut v_bs_5535_: *mut LeanObject,
    mut v___y_5536_: *mut LeanObject,
    mut v___y_5537_: *mut LeanObject,
    mut v___y_5538_: *mut LeanObject,
    mut v___y_5539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5542_: u8 = 0;
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: u8 = 0;
    let mut v_one_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5558_: u8 = 0;
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5562_: u8 = 0;
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: u8 = 0;
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5575_: u8 = 0;
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_5583_: u8 = 0;
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: u32 = 0;
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5590_: u8 = 0;
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5608_: u8 = 0;
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5621_: u8 = 0;
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5630_: u8 = 0;
    let mut v_unused_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5633_: u8 = 0;
    let mut v_unused_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5638_: u8 = 0;
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5642_: u8 = 0;
    let mut v_reuseFailAlloc_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: u8 = 0;
    let mut v___x_5645_: u8 = 0;
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5541_ = lean_unsigned_to_nat(0);
                v_isZero_5542_ = lean_nat_dec_eq(v_i_5533_, v_zero_5541_);
                if v_isZero_5542_ == 1 {
                    lean_dec(v_j_5534_);
                    lean_dec(v_i_5533_);
                    lean_dec(v___x_5531_);
                    v___x_5543_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5543_, 0, v_bs_5535_);
                    return v___x_5543_;
                } else {
                    v___x_5544_ = 1;
                    v_one_5545_ = lean_unsigned_to_nat(1);
                    v_n_5546_ = lean_nat_sub(v_i_5533_, v_one_5545_);
                    lean_dec(v_i_5533_);
                    v___x_5563_ = lean_array_fget_borrowed(v_as_5532_, v_j_5534_);
                    v___x_5564_ = 1;
                    lean_inc(v___x_5563_);
                    v___x_5565_ = l_Lean_Meta_mkLambdaFVars(
                        v_xs_5528_,
                        v___x_5563_,
                        v_a_5529_,
                        v___x_5544_,
                        v_a_5529_,
                        v___x_5544_,
                        v___x_5564_,
                        v___y_5536_,
                        v___y_5537_,
                        v___y_5538_,
                        v___y_5539_,
                    );
                    if lean_obj_tag(v___x_5565_) == 0 {
                        v_a_5566_ = lean_ctor_get(v___x_5565_, 0);
                        lean_inc(v_a_5566_);
                        lean_dec_ref_known(v___x_5565_, 1);
                        v___x_5567_ =
                            l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_5566_, v___y_5538_, v___y_5539_);
                        if lean_obj_tag(v___x_5567_) == 0 {
                            v_a_5568_ = lean_ctor_get(v___x_5567_, 0);
                            lean_inc_n(v_a_5568_, 2);
                            lean_dec_ref_known(v___x_5567_, 1);
                            lean_inc(v___y_5539_);
                            lean_inc_ref(v___y_5538_);
                            lean_inc(v___y_5537_);
                            lean_inc_ref(v___y_5536_);
                            v___x_5569_ = lean_infer_type(
                                v_a_5568_,
                                v___y_5536_,
                                v___y_5537_,
                                v___y_5538_,
                                v___y_5539_,
                            );
                            if lean_obj_tag(v___x_5569_) == 0 {
                                v_a_5570_ = lean_ctor_get(v___x_5569_, 0);
                                lean_inc(v_a_5570_);
                                lean_dec_ref_known(v___x_5569_, 1);
                                v___x_5571_ = l_Lean_Meta_letToHave(
                                    v_a_5570_,
                                    v___y_5536_,
                                    v___y_5537_,
                                    v___y_5538_,
                                    v___y_5539_,
                                );
                                if lean_obj_tag(v___x_5571_) == 0 {
                                    v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
                                    v_isSharedCheck_5646_ = (!lean_is_exclusive(v___x_5571_)) as u8;
                                    if v_isSharedCheck_5646_ == 0 {
                                        v___x_5574_ = v___x_5571_;
                                        v_isShared_5575_ = v_isSharedCheck_5646_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5572_);
                                        lean_dec(v___x_5571_);
                                        v___x_5574_ = lean_box(0);
                                        v_isShared_5575_ = v_isSharedCheck_5646_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_5568_);
                                    v___y_5553_ = v___x_5571_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5568_);
                                v___y_5553_ = v___x_5569_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_5553_ = v___x_5567_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_5553_ = v___x_5565_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5549_ = lean_nat_add(v_j_5534_, v_one_5545_);
                lean_dec(v_j_5534_);
                v___x_5550_ = lean_array_push(v_bs_5535_, v_a_5548_);
                v_i_5533_ = v_n_5546_;
                v_j_5534_ = v___x_5549_;
                v_bs_5535_ = v___x_5550_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_5553_) == 0 {
                    v_a_5554_ = lean_ctor_get(v___y_5553_, 0);
                    lean_inc(v_a_5554_);
                    lean_dec_ref_known(v___y_5553_, 1);
                    v_a_5548_ = v_a_5554_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_n_5546_);
                    lean_dec_ref(v_bs_5535_);
                    lean_dec(v_j_5534_);
                    lean_dec(v___x_5531_);
                    v_a_5555_ = lean_ctor_get(v___y_5553_, 0);
                    v_isSharedCheck_5562_ = (!lean_is_exclusive(v___y_5553_)) as u8;
                    if v_isSharedCheck_5562_ == 0 {
                        v___x_5557_ = v___y_5553_;
                        v_isShared_5558_ = v_isSharedCheck_5562_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5555_);
                        lean_dec(v___y_5553_);
                        v___x_5557_ = lean_box(0);
                        v_isShared_5558_ = v_isSharedCheck_5562_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5558_ == 0 {
                    v___x_5560_ = v___x_5557_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
                    v___x_5560_ = v_reuseFailAlloc_5561_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5560_;
            }
            5 => {
                v___x_5576_ = lean_st_ref_get(v___y_5539_);
                v___x_5577_ = l_Lean_Elab_instInhabitedPreDefinition_default;
                v___x_5578_ = lean_array_get_borrowed(v___x_5577_, v_preDefs_5530_, v_j_5534_);
                v_modifiers_5579_ = lean_ctor_get(v___x_5578_, 2);
                v_levelParams_5580_ = lean_ctor_get(v___x_5578_, 1);
                v_declName_5581_ = lean_ctor_get(v___x_5578_, 3);
                v_env_5582_ = lean_ctor_get(v___x_5576_, 0);
                lean_inc_ref(v_env_5582_);
                lean_dec(v___x_5576_);
                v_isUnsafe_5583_ = lean_ctor_get_uint8(
                    v_modifiers_5579_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v___x_5584_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___closed__1;
                lean_inc(v_declName_5581_);
                v___x_5585_ = l_Lean_Name_append(v_declName_5581_, v___x_5584_);
                lean_inc(v_a_5568_);
                v___x_5586_ = l_Lean_getMaxHeight(v_env_5582_, v_a_5568_);
                lean_inc(v_levelParams_5580_);
                lean_inc(v___x_5585_);
                v___x_5587_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_5587_, 0, v___x_5585_);
                lean_ctor_set(v___x_5587_, 1, v_levelParams_5580_);
                lean_ctor_set(v___x_5587_, 2, v_a_5572_);
                v___x_5588_ = lean_box(1);
                if v_isUnsafe_5583_ == 0 {
                    v___x_5644_ = 1;
                    v___y_5590_ = v___x_5644_;
                    state = 6;
                    continue;
                } else {
                    v___x_5645_ = 0;
                    v___y_5590_ = v___x_5645_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5591_ = lean_box(0);
                lean_inc(v___x_5585_);
                v___x_5592_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5592_, 0, v___x_5585_);
                lean_ctor_set(v___x_5592_, 1, v___x_5591_);
                v___x_5593_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_5593_, 0, v___x_5587_);
                lean_ctor_set(v___x_5593_, 1, v_a_5568_);
                lean_ctor_set(v___x_5593_, 2, v___x_5588_);
                lean_ctor_set(v___x_5593_, 3, v___x_5592_);
                lean_ctor_set_uint8(
                    v___x_5593_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___y_5590_,
                );
                if v_isShared_5575_ == 0 {
                    lean_ctor_set_tag(v___x_5574_, 1);
                    lean_ctor_set(v___x_5574_, 0, v___x_5593_);
                    v___x_5595_ = v___x_5574_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5643_, 0, v___x_5593_);
                    v___x_5595_ = v_reuseFailAlloc_5643_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5596_ = l_Lean_addDecl(v___x_5595_, v_a_5529_, v___y_5538_, v___y_5539_);
                if lean_obj_tag(v___x_5596_) == 0 {
                    lean_dec_ref_known(v___x_5596_, 1);
                    v___x_5597_ = lean_st_ref_take(v___y_5539_);
                    v_env_5598_ = lean_ctor_get(v___x_5597_, 0);
                    v_nextMacroScope_5599_ = lean_ctor_get(v___x_5597_, 1);
                    v_ngen_5600_ = lean_ctor_get(v___x_5597_, 2);
                    v_auxDeclNGen_5601_ = lean_ctor_get(v___x_5597_, 3);
                    v_traceState_5602_ = lean_ctor_get(v___x_5597_, 4);
                    v_messages_5603_ = lean_ctor_get(v___x_5597_, 6);
                    v_infoState_5604_ = lean_ctor_get(v___x_5597_, 7);
                    v_snapshotTasks_5605_ = lean_ctor_get(v___x_5597_, 8);
                    v_isSharedCheck_5633_ = (!lean_is_exclusive(v___x_5597_)) as u8;
                    if v_isSharedCheck_5633_ == 0 {
                        v_unused_5634_ = lean_ctor_get(v___x_5597_, 5);
                        lean_dec(v_unused_5634_);
                        v___x_5607_ = v___x_5597_;
                        v_isShared_5608_ = v_isSharedCheck_5633_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_5605_);
                        lean_inc(v_infoState_5604_);
                        lean_inc(v_messages_5603_);
                        lean_inc(v_traceState_5602_);
                        lean_inc(v_auxDeclNGen_5601_);
                        lean_inc(v_ngen_5600_);
                        lean_inc(v_nextMacroScope_5599_);
                        lean_inc(v_env_5598_);
                        lean_dec(v___x_5597_);
                        v___x_5607_ = lean_box(0);
                        v_isShared_5608_ = v_isSharedCheck_5633_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5585_);
                    lean_dec(v_n_5546_);
                    lean_dec_ref(v_bs_5535_);
                    lean_dec(v_j_5534_);
                    lean_dec(v___x_5531_);
                    v_a_5635_ = lean_ctor_get(v___x_5596_, 0);
                    v_isSharedCheck_5642_ = (!lean_is_exclusive(v___x_5596_)) as u8;
                    if v_isSharedCheck_5642_ == 0 {
                        v___x_5637_ = v___x_5596_;
                        v_isShared_5638_ = v_isSharedCheck_5642_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_5635_);
                        lean_dec(v___x_5596_);
                        v___x_5637_ = lean_box(0);
                        v_isShared_5638_ = v_isSharedCheck_5642_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                lean_inc(v___x_5585_);
                v___x_5609_ = l_Lean_setDefHeightOverride(v_env_5598_, v___x_5585_, v___x_5586_);
                v___x_5610_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__2);
                if v_isShared_5608_ == 0 {
                    lean_ctor_set(v___x_5607_, 5, v___x_5610_);
                    lean_ctor_set(v___x_5607_, 0, v___x_5609_);
                    v___x_5612_ = v___x_5607_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5632_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5632_, 0, v___x_5609_);
                    lean_ctor_set(v_reuseFailAlloc_5632_, 1, v_nextMacroScope_5599_);
                    lean_ctor_set(v_reuseFailAlloc_5632_, 2, v_ngen_5600_);
                    lean_ctor_set(v_reuseFailAlloc_5632_, 3, v_auxDeclNGen_5601_);
                    lean_ctor_set(v_reuseFailAlloc_5632_, 4, v_traceState_5602_);
                    lean_ctor_set(v_reuseFailAlloc_5632_, 5, v___x_5610_);
                    lean_ctor_set(v_reuseFailAlloc_5632_, 6, v_messages_5603_);
                    lean_ctor_set(v_reuseFailAlloc_5632_, 7, v_infoState_5604_);
                    lean_ctor_set(v_reuseFailAlloc_5632_, 8, v_snapshotTasks_5605_);
                    v___x_5612_ = v_reuseFailAlloc_5632_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5613_ = lean_st_ref_set(v___y_5539_, v___x_5612_);
                v___x_5614_ = lean_st_ref_take(v___y_5537_);
                v_mctx_5615_ = lean_ctor_get(v___x_5614_, 0);
                v_zetaDeltaFVarIds_5616_ = lean_ctor_get(v___x_5614_, 2);
                v_postponed_5617_ = lean_ctor_get(v___x_5614_, 3);
                v_diag_5618_ = lean_ctor_get(v___x_5614_, 4);
                v_isSharedCheck_5630_ = (!lean_is_exclusive(v___x_5614_)) as u8;
                if v_isSharedCheck_5630_ == 0 {
                    v_unused_5631_ = lean_ctor_get(v___x_5614_, 1);
                    lean_dec(v_unused_5631_);
                    v___x_5620_ = v___x_5614_;
                    v_isShared_5621_ = v_isSharedCheck_5630_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_diag_5618_);
                    lean_inc(v_postponed_5617_);
                    lean_inc(v_zetaDeltaFVarIds_5616_);
                    lean_inc(v_mctx_5615_);
                    lean_dec(v___x_5614_);
                    v___x_5620_ = lean_box(0);
                    v_isShared_5621_ = v_isSharedCheck_5630_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5622_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg___closed__3);
                if v_isShared_5621_ == 0 {
                    lean_ctor_set(v___x_5620_, 1, v___x_5622_);
                    v___x_5624_ = v___x_5620_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_mctx_5615_);
                    lean_ctor_set(v_reuseFailAlloc_5629_, 1, v___x_5622_);
                    lean_ctor_set(v_reuseFailAlloc_5629_, 2, v_zetaDeltaFVarIds_5616_);
                    lean_ctor_set(v_reuseFailAlloc_5629_, 3, v_postponed_5617_);
                    lean_ctor_set(v_reuseFailAlloc_5629_, 4, v_diag_5618_);
                    v___x_5624_ = v_reuseFailAlloc_5629_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_5625_ = lean_st_ref_set(v___y_5537_, v___x_5624_);
                lean_inc(v___x_5585_);
                v___x_5626_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16(v___x_5585_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_);
                lean_dec_ref(v___x_5626_);
                lean_inc(v___x_5531_);
                v___x_5627_ = l_Lean_mkConst(v___x_5585_, v___x_5531_);
                v___x_5628_ = l_Lean_mkAppN(v___x_5627_, v_xs_5528_);
                v_a_5548_ = v___x_5628_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_5638_ == 0 {
                    v___x_5640_ = v___x_5637_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5641_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_a_5635_);
                    v___x_5640_ = v_reuseFailAlloc_5641_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg___boxed(
    mut v_xs_5647_: *mut LeanObject,
    mut v_a_5648_: *mut LeanObject,
    mut v_preDefs_5649_: *mut LeanObject,
    mut v___x_5650_: *mut LeanObject,
    mut v_as_5651_: *mut LeanObject,
    mut v_i_5652_: *mut LeanObject,
    mut v_j_5653_: *mut LeanObject,
    mut v_bs_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
    mut v___y_5657_: *mut LeanObject,
    mut v___y_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_28564__boxed_5660_: u8 = 0;
    let mut v_res_5661_: *mut LeanObject = core::ptr::null_mut();
    v_a_28564__boxed_5660_ = (lean_unbox(v_a_5648_) as u8);
    v_res_5661_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_5647_, v_a_28564__boxed_5660_, v_preDefs_5649_, v___x_5650_, v_as_5651_, v_i_5652_, v_j_5653_, v_bs_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
    lean_dec(v___y_5658_);
    lean_dec_ref(v___y_5657_);
    lean_dec(v___y_5656_);
    lean_dec_ref(v___y_5655_);
    lean_dec_ref(v_as_5651_);
    lean_dec_ref(v_preDefs_5649_);
    lean_dec_ref(v_xs_5647_);
    return v_res_5661_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2()
-> *mut LeanObject {
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    v___x_5665_ = lean_box(0);
    v___x_5666_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__1;
    v___x_5667_ = l_Lean_Expr_const___override(v___x_5666_, v___x_5665_);
    return v___x_5667_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4()
-> *mut LeanObject {
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    v___x_5669_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__3;
    v___x_5670_ = l_Lean_stringToMessageData(v___x_5669_);
    return v___x_5670_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6()
-> *mut LeanObject {
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    v___x_5672_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__5;
    v___x_5673_ = l_Lean_stringToMessageData(v___x_5672_);
    return v___x_5673_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8()
-> *mut LeanObject {
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    v___x_5675_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__7;
    v___x_5676_ = l_Lean_stringToMessageData(v___x_5675_);
    return v___x_5676_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10()
-> *mut LeanObject {
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    v___x_5678_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__9;
    v___x_5679_ = l_Lean_stringToMessageData(v___x_5678_);
    return v___x_5679_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12()
-> *mut LeanObject {
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    v___x_5681_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__11;
    v___x_5682_ = l_Lean_stringToMessageData(v___x_5681_);
    return v___x_5682_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(
    mut v___f_5683_: *mut LeanObject,
    mut v_recArgInfos_5684_: *mut LeanObject,
    mut v_a_5685_: *mut LeanObject,
    mut v___x_5686_: *mut LeanObject,
    mut v___x_5687_: *mut LeanObject,
    mut v_fixedParamPerms_5688_: *mut LeanObject,
    mut v_xs_5689_: *mut LeanObject,
    mut v_preDefs_5690_: *mut LeanObject,
    mut v_numIndices_5691_: *mut LeanObject,
    mut v___f_5692_: *mut LeanObject,
    mut v___x_5693_: *mut LeanObject,
    mut v_a_5694_: u8,
    mut v_funTypes_5695_: *mut LeanObject,
    mut v_motives_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5727_: u8 = 0;
    let mut v_a_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5731_: u8 = 0;
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5735_: u8 = 0;
    let mut v_a_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5739_: u8 = 0;
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5743_: u8 = 0;
    let mut v___y_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_FArgs_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5763_: u8 = 0;
    let mut v_a_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: u8 = 0;
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5779_: u8 = 0;
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5783_: u8 = 0;
    let mut v_a_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5791_: u8 = 0;
    let mut v_a_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5795_: u8 = 0;
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5799_: u8 = 0;
    let mut v___y_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5823_: u8 = 0;
    let mut v___y_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: u8 = 0;
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5848_: u8 = 0;
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5852_: u8 = 0;
    let mut v_a_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5860_: u8 = 0;
    let mut v_a_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5864_: u8 = 0;
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5868_: u8 = 0;
    let mut v___y_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: u8 = 0;
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5891_: u8 = 0;
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5895_: u8 = 0;
    let mut v_a_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5899_: u8 = 0;
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5903_: u8 = 0;
    let mut v_a_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5907_: u8 = 0;
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5911_: u8 = 0;
    let mut v_a_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5915_: u8 = 0;
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5919_: u8 = 0;
    let mut v___x_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: u8 = 0;
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5939_: u8 = 0;
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5943_: u8 = 0;
    let mut v_a_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5947_: u8 = 0;
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___f_5683_);
                lean_inc(v___y_5700_);
                lean_inc_ref(v___y_5699_);
                lean_inc(v___y_5698_);
                lean_inc_ref(v___y_5697_);
                v___x_5920_ = lean_apply_5(
                    v___f_5683_,
                    v___y_5697_,
                    v___y_5698_,
                    v___y_5699_,
                    v___y_5700_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5920_) == 0 {
                    v_a_5921_ = lean_ctor_get(v___x_5920_, 0);
                    lean_inc(v_a_5921_);
                    lean_dec_ref_known(v___x_5920_, 1);
                    v___x_5922_ = (lean_unbox(v_a_5921_) as u8);
                    lean_dec(v_a_5921_);
                    if v___x_5922_ == 0 {
                        v___y_5870_ = v___y_5697_;
                        v___y_5871_ = v___y_5698_;
                        v___y_5872_ = v___y_5699_;
                        v___y_5873_ = v___y_5700_;
                        state = 25;
                        continue;
                    } else {
                        v___x_5923_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__10);
                        lean_inc_ref(v_funTypes_5695_);
                        v___x_5924_ = lean_array_to_list(v_funTypes_5695_);
                        v___x_5925_ = lean_box(0);
                        v___x_5926_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_5924_, v___x_5925_);
                        v___x_5927_ = l_Lean_MessageData_ofList(v___x_5926_);
                        v___x_5928_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5928_, 0, v___x_5923_);
                        lean_ctor_set(v___x_5928_, 1, v___x_5927_);
                        v___x_5929_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__12);
                        v___x_5930_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5930_, 0, v___x_5928_);
                        lean_ctor_set(v___x_5930_, 1, v___x_5929_);
                        lean_inc_ref(v_motives_5696_);
                        v___x_5931_ = lean_array_to_list(v_motives_5696_);
                        v___x_5932_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_5931_, v___x_5925_);
                        v___x_5933_ = l_Lean_MessageData_ofList(v___x_5932_);
                        v___x_5934_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5934_, 0, v___x_5930_);
                        lean_ctor_set(v___x_5934_, 1, v___x_5933_);
                        lean_inc(v___x_5693_);
                        v___x_5935_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_5693_, v___x_5934_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_);
                        if lean_obj_tag(v___x_5935_) == 0 {
                            lean_dec_ref_known(v___x_5935_, 1);
                            v___y_5870_ = v___y_5697_;
                            v___y_5871_ = v___y_5698_;
                            v___y_5872_ = v___y_5699_;
                            v___y_5873_ = v___y_5700_;
                            state = 25;
                            continue;
                        } else {
                            lean_dec_ref(v_motives_5696_);
                            lean_dec_ref(v_funTypes_5695_);
                            lean_dec(v___x_5693_);
                            lean_dec_ref(v___f_5692_);
                            lean_dec_ref(v_preDefs_5690_);
                            lean_dec_ref(v_xs_5689_);
                            lean_dec_ref(v_fixedParamPerms_5688_);
                            lean_dec(v___x_5687_);
                            lean_dec_ref(v___x_5686_);
                            lean_dec_ref(v_recArgInfos_5684_);
                            lean_dec_ref(v___f_5683_);
                            v_a_5936_ = lean_ctor_get(v___x_5935_, 0);
                            v_isSharedCheck_5943_ = (!lean_is_exclusive(v___x_5935_)) as u8;
                            if v_isSharedCheck_5943_ == 0 {
                                v___x_5938_ = v___x_5935_;
                                v_isShared_5939_ = v_isSharedCheck_5943_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_a_5936_);
                                lean_dec(v___x_5935_);
                                v___x_5938_ = lean_box(0);
                                v_isShared_5939_ = v_isSharedCheck_5943_;
                                state = 34;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_motives_5696_);
                    lean_dec_ref(v_funTypes_5695_);
                    lean_dec(v___x_5693_);
                    lean_dec_ref(v___f_5692_);
                    lean_dec_ref(v_preDefs_5690_);
                    lean_dec_ref(v_xs_5689_);
                    lean_dec_ref(v_fixedParamPerms_5688_);
                    lean_dec(v___x_5687_);
                    lean_dec_ref(v___x_5686_);
                    lean_dec_ref(v_recArgInfos_5684_);
                    lean_dec_ref(v___f_5683_);
                    v_a_5944_ = lean_ctor_get(v___x_5920_, 0);
                    v_isSharedCheck_5951_ = (!lean_is_exclusive(v___x_5920_)) as u8;
                    if v_isSharedCheck_5951_ == 0 {
                        v___x_5946_ = v___x_5920_;
                        v_isShared_5947_ = v_isSharedCheck_5951_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_5944_);
                        lean_dec(v___x_5920_);
                        v___x_5946_ = lean_box(0);
                        v_isShared_5947_ = v_isSharedCheck_5951_;
                        state = 36;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5709_ = l_Array_zip___redArg(v_recArgInfos_5684_, v_a_5685_);
                lean_dec_ref(v_recArgInfos_5684_);
                v___x_5710_ = lean_array_get_size(v___x_5709_);
                v___x_5711_ = lean_mk_empty_array_with_capacity(v___x_5710_);
                lean_inc(v___x_5687_);
                v___x_5712_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_5686_, v___y_5703_, v___y_5704_, v_funTypes_5695_, v___x_5709_, v___x_5710_, v___x_5687_, v___x_5711_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_);
                lean_dec_ref(v___x_5709_);
                if lean_obj_tag(v___x_5712_) == 0 {
                    v_a_5713_ = lean_ctor_get(v___x_5712_, 0);
                    lean_inc(v_a_5713_);
                    lean_dec_ref_known(v___x_5712_, 1);
                    v___x_5714_ = l_Array_zip___redArg(v_a_5685_, v_a_5713_);
                    lean_dec(v_a_5713_);
                    v___x_5715_ = lean_array_get_size(v___x_5714_);
                    v___x_5716_ = lean_mk_empty_array_with_capacity(v___x_5715_);
                    lean_inc(v___x_5687_);
                    v___x_5717_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_5688_, v_xs_5689_, v___x_5714_, v___x_5715_, v___x_5687_, v___x_5716_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_);
                    lean_dec_ref(v___x_5714_);
                    if lean_obj_tag(v___x_5717_) == 0 {
                        v_a_5718_ = lean_ctor_get(v___x_5717_, 0);
                        v_isSharedCheck_5727_ = (!lean_is_exclusive(v___x_5717_)) as u8;
                        if v_isSharedCheck_5727_ == 0 {
                            v___x_5720_ = v___x_5717_;
                            v_isShared_5721_ = v_isSharedCheck_5727_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5718_);
                            lean_dec(v___x_5717_);
                            v___x_5720_ = lean_box(0);
                            v_isShared_5721_ = v_isSharedCheck_5727_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_preDefs_5690_);
                        lean_dec(v___x_5687_);
                        v_a_5728_ = lean_ctor_get(v___x_5717_, 0);
                        v_isSharedCheck_5735_ = (!lean_is_exclusive(v___x_5717_)) as u8;
                        if v_isSharedCheck_5735_ == 0 {
                            v___x_5730_ = v___x_5717_;
                            v_isShared_5731_ = v_isSharedCheck_5735_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5728_);
                            lean_dec(v___x_5717_);
                            v___x_5730_ = lean_box(0);
                            v_isShared_5731_ = v_isSharedCheck_5735_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_preDefs_5690_);
                    lean_dec_ref(v_xs_5689_);
                    lean_dec_ref(v_fixedParamPerms_5688_);
                    lean_dec(v___x_5687_);
                    v_a_5736_ = lean_ctor_get(v___x_5712_, 0);
                    v_isSharedCheck_5743_ = (!lean_is_exclusive(v___x_5712_)) as u8;
                    if v_isSharedCheck_5743_ == 0 {
                        v___x_5738_ = v___x_5712_;
                        v_isShared_5739_ = v_isSharedCheck_5743_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5736_);
                        lean_dec(v___x_5712_);
                        v___x_5738_ = lean_box(0);
                        v_isShared_5739_ = v_isSharedCheck_5743_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5722_ = lean_mk_empty_array_with_capacity(v___x_5687_);
                v___x_5723_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__9(v_preDefs_5690_, v_a_5718_, v___x_5687_, v___x_5722_);
                lean_dec(v_a_5718_);
                lean_dec_ref(v_preDefs_5690_);
                if v_isShared_5721_ == 0 {
                    lean_ctor_set(v___x_5720_, 0, v___x_5723_);
                    v___x_5725_ = v___x_5720_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5726_, 0, v___x_5723_);
                    v___x_5725_ = v_reuseFailAlloc_5726_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5725_;
            }
            4 => {
                if v_isShared_5731_ == 0 {
                    v___x_5733_ = v___x_5730_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5734_, 0, v_a_5728_);
                    v___x_5733_ = v_reuseFailAlloc_5734_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5733_;
            }
            6 => {
                if v_isShared_5739_ == 0 {
                    v___x_5741_ = v___x_5738_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_a_5736_);
                    v___x_5741_ = v_reuseFailAlloc_5742_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5741_;
            }
            8 => {
                lean_inc_ref(v___y_5745_);
                lean_inc(v___x_5687_);
                v___x_5751_ = lean_apply_1(v___y_5745_, v___x_5687_);
                v___x_5752_ = lean_unsigned_to_nat(1);
                v___x_5753_ = lean_nat_add(v_numIndices_5691_, v___x_5752_);
                v___x_5754_ = lean_box(0);
                v___x_5755_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__2);
                v___x_5756_ = lean_mk_array(v___x_5753_, v___x_5755_);
                v___x_5757_ = l_Lean_mkAppN(v___x_5751_, v___x_5756_);
                lean_dec_ref(v___x_5756_);
                v___x_5758_ = lean_array_get_size(v___x_5686_);
                v___x_5759_ = l_Lean_Meta_inferArgumentTypesN(
                    v___x_5758_,
                    v___x_5757_,
                    v___y_5747_,
                    v___y_5748_,
                    v___y_5749_,
                    v___y_5750_,
                );
                if lean_obj_tag(v___x_5759_) == 0 {
                    v_a_5760_ = lean_ctor_get(v___x_5759_, 0);
                    lean_inc(v_a_5760_);
                    lean_dec_ref_known(v___x_5759_, 1);
                    v___x_5761_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v___f_5692_, v___x_5686_, v_a_5760_, v_FArgs_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_);
                    lean_dec_ref(v_FArgs_5746_);
                    lean_dec(v_a_5760_);
                    if lean_obj_tag(v___x_5761_) == 0 {
                        v_options_5762_ = lean_ctor_get(v___y_5749_, 2);
                        v_hasTrace_5763_ = lean_ctor_get_uint8(
                            v_options_5762_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_5763_ == 0 {
                            lean_dec(v___x_5693_);
                            v_a_5764_ = lean_ctor_get(v___x_5761_, 0);
                            lean_inc(v_a_5764_);
                            lean_dec_ref_known(v___x_5761_, 1);
                            v___y_5703_ = v___y_5745_;
                            v___y_5704_ = v_a_5764_;
                            v___y_5705_ = v___y_5747_;
                            v___y_5706_ = v___y_5748_;
                            v___y_5707_ = v___y_5749_;
                            v___y_5708_ = v___y_5750_;
                            state = 1;
                            continue;
                        } else {
                            v_a_5765_ = lean_ctor_get(v___x_5761_, 0);
                            lean_inc(v_a_5765_);
                            lean_dec_ref_known(v___x_5761_, 1);
                            v_inheritedTraceOptions_5766_ = lean_ctor_get(v___y_5749_, 13);
                            v___x_5767_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1;
                            lean_inc(v___x_5693_);
                            v___x_5768_ = l_Lean_Name_append(v___x_5767_, v___x_5693_);
                            v___x_5769_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_5766_,
                                v_options_5762_,
                                v___x_5768_,
                            );
                            lean_dec(v___x_5768_);
                            if v___x_5769_ == 0 {
                                lean_dec(v___x_5693_);
                                v___y_5703_ = v___y_5745_;
                                v___y_5704_ = v_a_5765_;
                                v___y_5705_ = v___y_5747_;
                                v___y_5706_ = v___y_5748_;
                                v___y_5707_ = v___y_5749_;
                                v___y_5708_ = v___y_5750_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5770_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__4);
                                lean_inc(v_a_5765_);
                                v___x_5771_ = lean_array_to_list(v_a_5765_);
                                v___x_5772_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_5771_, v___x_5754_);
                                v___x_5773_ = l_Lean_MessageData_ofList(v___x_5772_);
                                v___x_5774_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5774_, 0, v___x_5770_);
                                lean_ctor_set(v___x_5774_, 1, v___x_5773_);
                                v___x_5775_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_5693_, v___x_5774_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_);
                                if lean_obj_tag(v___x_5775_) == 0 {
                                    lean_dec_ref_known(v___x_5775_, 1);
                                    v___y_5703_ = v___y_5745_;
                                    v___y_5704_ = v_a_5765_;
                                    v___y_5705_ = v___y_5747_;
                                    v___y_5706_ = v___y_5748_;
                                    v___y_5707_ = v___y_5749_;
                                    v___y_5708_ = v___y_5750_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_a_5765_);
                                    lean_dec_ref(v___y_5745_);
                                    lean_dec_ref(v_funTypes_5695_);
                                    lean_dec_ref(v_preDefs_5690_);
                                    lean_dec_ref(v_xs_5689_);
                                    lean_dec_ref(v_fixedParamPerms_5688_);
                                    lean_dec(v___x_5687_);
                                    lean_dec_ref(v___x_5686_);
                                    lean_dec_ref(v_recArgInfos_5684_);
                                    v_a_5776_ = lean_ctor_get(v___x_5775_, 0);
                                    v_isSharedCheck_5783_ = (!lean_is_exclusive(v___x_5775_)) as u8;
                                    if v_isSharedCheck_5783_ == 0 {
                                        v___x_5778_ = v___x_5775_;
                                        v_isShared_5779_ = v_isSharedCheck_5783_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5776_);
                                        lean_dec(v___x_5775_);
                                        v___x_5778_ = lean_box(0);
                                        v_isShared_5779_ = v_isSharedCheck_5783_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_5745_);
                        lean_dec_ref(v_funTypes_5695_);
                        lean_dec(v___x_5693_);
                        lean_dec_ref(v_preDefs_5690_);
                        lean_dec_ref(v_xs_5689_);
                        lean_dec_ref(v_fixedParamPerms_5688_);
                        lean_dec(v___x_5687_);
                        lean_dec_ref(v___x_5686_);
                        lean_dec_ref(v_recArgInfos_5684_);
                        v_a_5784_ = lean_ctor_get(v___x_5761_, 0);
                        v_isSharedCheck_5791_ = (!lean_is_exclusive(v___x_5761_)) as u8;
                        if v_isSharedCheck_5791_ == 0 {
                            v___x_5786_ = v___x_5761_;
                            v_isShared_5787_ = v_isSharedCheck_5791_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_5784_);
                            lean_dec(v___x_5761_);
                            v___x_5786_ = lean_box(0);
                            v_isShared_5787_ = v_isSharedCheck_5791_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_FArgs_5746_);
                    lean_dec_ref(v___y_5745_);
                    lean_dec_ref(v_funTypes_5695_);
                    lean_dec(v___x_5693_);
                    lean_dec_ref(v___f_5692_);
                    lean_dec_ref(v_preDefs_5690_);
                    lean_dec_ref(v_xs_5689_);
                    lean_dec_ref(v_fixedParamPerms_5688_);
                    lean_dec(v___x_5687_);
                    lean_dec_ref(v___x_5686_);
                    lean_dec_ref(v_recArgInfos_5684_);
                    v_a_5792_ = lean_ctor_get(v___x_5759_, 0);
                    v_isSharedCheck_5799_ = (!lean_is_exclusive(v___x_5759_)) as u8;
                    if v_isSharedCheck_5799_ == 0 {
                        v___x_5794_ = v___x_5759_;
                        v_isShared_5795_ = v_isSharedCheck_5799_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_5792_);
                        lean_dec(v___x_5759_);
                        v___x_5794_ = lean_box(0);
                        v_isShared_5795_ = v_isSharedCheck_5799_;
                        state = 13;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_5779_ == 0 {
                    v___x_5781_ = v___x_5778_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5782_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5782_, 0, v_a_5776_);
                    v___x_5781_ = v_reuseFailAlloc_5782_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5781_;
            }
            11 => {
                if v_isShared_5787_ == 0 {
                    v___x_5789_ = v___x_5786_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
                    v___x_5789_ = v_reuseFailAlloc_5790_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5789_;
            }
            13 => {
                if v_isShared_5795_ == 0 {
                    v___x_5797_ = v___x_5794_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5798_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_a_5792_);
                    v___x_5797_ = v_reuseFailAlloc_5798_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5797_;
            }
            15 => {
                if v_a_5694_ == 0 {
                    v___x_5807_ = l_Lean_Elab_instInhabitedPreDefinition_default;
                    v___x_5808_ =
                        lean_array_get_borrowed(v___x_5807_, v_preDefs_5690_, v___x_5687_);
                    v_levelParams_5809_ = lean_ctor_get(v___x_5808_, 1);
                    v___x_5810_ = lean_box(0);
                    lean_inc(v_levelParams_5809_);
                    v___x_5811_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__15(v_levelParams_5809_, v___x_5810_);
                    v___x_5812_ = lean_array_get_size(v___y_5802_);
                    v___x_5813_ = lean_mk_empty_array_with_capacity(v___x_5812_);
                    lean_inc(v___x_5687_);
                    v___x_5814_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_5689_, v_a_5694_, v_preDefs_5690_, v___x_5811_, v___y_5802_, v___x_5812_, v___x_5687_, v___x_5813_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_);
                    lean_dec_ref(v___y_5802_);
                    if lean_obj_tag(v___x_5814_) == 0 {
                        v_a_5815_ = lean_ctor_get(v___x_5814_, 0);
                        lean_inc(v_a_5815_);
                        lean_dec_ref_known(v___x_5814_, 1);
                        v___y_5745_ = v___y_5801_;
                        v_FArgs_5746_ = v_a_5815_;
                        v___y_5747_ = v___y_5803_;
                        v___y_5748_ = v___y_5804_;
                        v___y_5749_ = v___y_5805_;
                        v___y_5750_ = v___y_5806_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec_ref(v___y_5801_);
                        lean_dec_ref(v_funTypes_5695_);
                        lean_dec(v___x_5693_);
                        lean_dec_ref(v___f_5692_);
                        lean_dec_ref(v_preDefs_5690_);
                        lean_dec_ref(v_xs_5689_);
                        lean_dec_ref(v_fixedParamPerms_5688_);
                        lean_dec(v___x_5687_);
                        lean_dec_ref(v___x_5686_);
                        lean_dec_ref(v_recArgInfos_5684_);
                        v_a_5816_ = lean_ctor_get(v___x_5814_, 0);
                        v_isSharedCheck_5823_ = (!lean_is_exclusive(v___x_5814_)) as u8;
                        if v_isSharedCheck_5823_ == 0 {
                            v___x_5818_ = v___x_5814_;
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_5816_);
                            lean_dec(v___x_5814_);
                            v___x_5818_ = lean_box(0);
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    v___y_5745_ = v___y_5801_;
                    v_FArgs_5746_ = v___y_5802_;
                    v___y_5747_ = v___y_5803_;
                    v___y_5748_ = v___y_5804_;
                    v___y_5749_ = v___y_5805_;
                    v___y_5750_ = v___y_5806_;
                    state = 8;
                    continue;
                }
            }
            16 => {
                if v_isShared_5819_ == 0 {
                    v___x_5821_ = v___x_5818_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_a_5816_);
                    v___x_5821_ = v_reuseFailAlloc_5822_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5821_;
            }
            18 => {
                v___x_5831_ = lean_array_get_size(v_recArgInfos_5684_);
                v___x_5832_ = lean_mk_empty_array_with_capacity(v___x_5831_);
                lean_inc(v___x_5687_);
                lean_inc_ref(v___y_5825_);
                lean_inc_ref(v_preDefs_5690_);
                lean_inc_ref(v___x_5686_);
                lean_inc_ref(v_recArgInfos_5684_);
                v___x_5833_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_5694_, v_a_5685_, v___y_5826_, v_recArgInfos_5684_, v___x_5686_, v_preDefs_5690_, v___y_5825_, v_recArgInfos_5684_, v___x_5831_, v___x_5687_, v___x_5832_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
                lean_dec_ref(v___y_5826_);
                if lean_obj_tag(v___x_5833_) == 0 {
                    v_a_5834_ = lean_ctor_get(v___x_5833_, 0);
                    lean_inc(v_a_5834_);
                    lean_dec_ref_known(v___x_5833_, 1);
                    lean_inc(v___y_5830_);
                    lean_inc_ref(v___y_5829_);
                    lean_inc(v___y_5828_);
                    lean_inc_ref(v___y_5827_);
                    v___x_5835_ = lean_apply_5(
                        v___f_5683_,
                        v___y_5827_,
                        v___y_5828_,
                        v___y_5829_,
                        v___y_5830_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_5835_) == 0 {
                        v_a_5836_ = lean_ctor_get(v___x_5835_, 0);
                        lean_inc(v_a_5836_);
                        lean_dec_ref_known(v___x_5835_, 1);
                        v___x_5837_ = (lean_unbox(v_a_5836_) as u8);
                        lean_dec(v_a_5836_);
                        if v___x_5837_ == 0 {
                            v___y_5801_ = v___y_5825_;
                            v___y_5802_ = v_a_5834_;
                            v___y_5803_ = v___y_5827_;
                            v___y_5804_ = v___y_5828_;
                            v___y_5805_ = v___y_5829_;
                            v___y_5806_ = v___y_5830_;
                            state = 15;
                            continue;
                        } else {
                            v___x_5838_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__6);
                            lean_inc(v_a_5834_);
                            v___x_5839_ = lean_array_to_list(v_a_5834_);
                            v___x_5840_ = lean_box(0);
                            v___x_5841_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_5839_, v___x_5840_);
                            v___x_5842_ = l_Lean_MessageData_ofList(v___x_5841_);
                            v___x_5843_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5843_, 0, v___x_5838_);
                            lean_ctor_set(v___x_5843_, 1, v___x_5842_);
                            lean_inc(v___x_5693_);
                            v___x_5844_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_5693_, v___x_5843_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
                            if lean_obj_tag(v___x_5844_) == 0 {
                                lean_dec_ref_known(v___x_5844_, 1);
                                v___y_5801_ = v___y_5825_;
                                v___y_5802_ = v_a_5834_;
                                v___y_5803_ = v___y_5827_;
                                v___y_5804_ = v___y_5828_;
                                v___y_5805_ = v___y_5829_;
                                v___y_5806_ = v___y_5830_;
                                state = 15;
                                continue;
                            } else {
                                lean_dec(v_a_5834_);
                                lean_dec_ref(v___y_5825_);
                                lean_dec_ref(v_funTypes_5695_);
                                lean_dec(v___x_5693_);
                                lean_dec_ref(v___f_5692_);
                                lean_dec_ref(v_preDefs_5690_);
                                lean_dec_ref(v_xs_5689_);
                                lean_dec_ref(v_fixedParamPerms_5688_);
                                lean_dec(v___x_5687_);
                                lean_dec_ref(v___x_5686_);
                                lean_dec_ref(v_recArgInfos_5684_);
                                v_a_5845_ = lean_ctor_get(v___x_5844_, 0);
                                v_isSharedCheck_5852_ = (!lean_is_exclusive(v___x_5844_)) as u8;
                                if v_isSharedCheck_5852_ == 0 {
                                    v___x_5847_ = v___x_5844_;
                                    v_isShared_5848_ = v_isSharedCheck_5852_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_5845_);
                                    lean_dec(v___x_5844_);
                                    v___x_5847_ = lean_box(0);
                                    v_isShared_5848_ = v_isSharedCheck_5852_;
                                    state = 19;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_5834_);
                        lean_dec_ref(v___y_5825_);
                        lean_dec_ref(v_funTypes_5695_);
                        lean_dec(v___x_5693_);
                        lean_dec_ref(v___f_5692_);
                        lean_dec_ref(v_preDefs_5690_);
                        lean_dec_ref(v_xs_5689_);
                        lean_dec_ref(v_fixedParamPerms_5688_);
                        lean_dec(v___x_5687_);
                        lean_dec_ref(v___x_5686_);
                        lean_dec_ref(v_recArgInfos_5684_);
                        v_a_5853_ = lean_ctor_get(v___x_5835_, 0);
                        v_isSharedCheck_5860_ = (!lean_is_exclusive(v___x_5835_)) as u8;
                        if v_isSharedCheck_5860_ == 0 {
                            v___x_5855_ = v___x_5835_;
                            v_isShared_5856_ = v_isSharedCheck_5860_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_5853_);
                            lean_dec(v___x_5835_);
                            v___x_5855_ = lean_box(0);
                            v_isShared_5856_ = v_isSharedCheck_5860_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_5825_);
                    lean_dec_ref(v_funTypes_5695_);
                    lean_dec(v___x_5693_);
                    lean_dec_ref(v___f_5692_);
                    lean_dec_ref(v_preDefs_5690_);
                    lean_dec_ref(v_xs_5689_);
                    lean_dec_ref(v_fixedParamPerms_5688_);
                    lean_dec(v___x_5687_);
                    lean_dec_ref(v___x_5686_);
                    lean_dec_ref(v_recArgInfos_5684_);
                    lean_dec_ref(v___f_5683_);
                    v_a_5861_ = lean_ctor_get(v___x_5833_, 0);
                    v_isSharedCheck_5868_ = (!lean_is_exclusive(v___x_5833_)) as u8;
                    if v_isSharedCheck_5868_ == 0 {
                        v___x_5863_ = v___x_5833_;
                        v_isShared_5864_ = v_isSharedCheck_5868_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_5861_);
                        lean_dec(v___x_5833_);
                        v___x_5863_ = lean_box(0);
                        v_isShared_5864_ = v_isSharedCheck_5868_;
                        state = 23;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_5848_ == 0 {
                    v___x_5850_ = v___x_5847_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_a_5845_);
                    v___x_5850_ = v_reuseFailAlloc_5851_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5850_;
            }
            21 => {
                if v_isShared_5856_ == 0 {
                    v___x_5858_ = v___x_5855_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
                    v___x_5858_ = v_reuseFailAlloc_5859_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5858_;
            }
            23 => {
                if v_isShared_5864_ == 0 {
                    v___x_5866_ = v___x_5863_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5861_);
                    v___x_5866_ = v_reuseFailAlloc_5867_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5866_;
            }
            25 => {
                v___x_5874_ = l_Lean_Elab_Structural_mkBRecOnConst(
                    v_recArgInfos_5684_,
                    v___x_5686_,
                    v_motives_5696_,
                    v_a_5694_,
                    v___y_5870_,
                    v___y_5871_,
                    v___y_5872_,
                    v___y_5873_,
                );
                lean_dec_ref(v_motives_5696_);
                if lean_obj_tag(v___x_5874_) == 0 {
                    v_a_5875_ = lean_ctor_get(v___x_5874_, 0);
                    lean_inc_n(v_a_5875_, 2);
                    lean_dec_ref_known(v___x_5874_, 1);
                    lean_inc_ref(v___x_5686_);
                    v___x_5876_ = l_Lean_Elab_Structural_inferBRecOnFTypes(
                        v_recArgInfos_5684_,
                        v___x_5686_,
                        v_a_5875_,
                        v___y_5870_,
                        v___y_5871_,
                        v___y_5872_,
                        v___y_5873_,
                    );
                    if lean_obj_tag(v___x_5876_) == 0 {
                        v_a_5877_ = lean_ctor_get(v___x_5876_, 0);
                        lean_inc(v_a_5877_);
                        lean_dec_ref_known(v___x_5876_, 1);
                        lean_inc_ref(v___f_5683_);
                        lean_inc(v___y_5873_);
                        lean_inc_ref(v___y_5872_);
                        lean_inc(v___y_5871_);
                        lean_inc_ref(v___y_5870_);
                        v___x_5878_ = lean_apply_5(
                            v___f_5683_,
                            v___y_5870_,
                            v___y_5871_,
                            v___y_5872_,
                            v___y_5873_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_5878_) == 0 {
                            v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
                            lean_inc(v_a_5879_);
                            lean_dec_ref_known(v___x_5878_, 1);
                            v___x_5880_ = (lean_unbox(v_a_5879_) as u8);
                            lean_dec(v_a_5879_);
                            if v___x_5880_ == 0 {
                                v___y_5825_ = v_a_5875_;
                                v___y_5826_ = v_a_5877_;
                                v___y_5827_ = v___y_5870_;
                                v___y_5828_ = v___y_5871_;
                                v___y_5829_ = v___y_5872_;
                                v___y_5830_ = v___y_5873_;
                                state = 18;
                                continue;
                            } else {
                                v___x_5881_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___closed__8);
                                lean_inc(v_a_5877_);
                                v___x_5882_ = lean_array_to_list(v_a_5877_);
                                v___x_5883_ = lean_box(0);
                                v___x_5884_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_5882_, v___x_5883_);
                                v___x_5885_ = l_Lean_MessageData_ofList(v___x_5884_);
                                v___x_5886_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5886_, 0, v___x_5881_);
                                lean_ctor_set(v___x_5886_, 1, v___x_5885_);
                                lean_inc(v___x_5693_);
                                v___x_5887_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_5693_, v___x_5886_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_);
                                if lean_obj_tag(v___x_5887_) == 0 {
                                    lean_dec_ref_known(v___x_5887_, 1);
                                    v___y_5825_ = v_a_5875_;
                                    v___y_5826_ = v_a_5877_;
                                    v___y_5827_ = v___y_5870_;
                                    v___y_5828_ = v___y_5871_;
                                    v___y_5829_ = v___y_5872_;
                                    v___y_5830_ = v___y_5873_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_dec(v_a_5877_);
                                    lean_dec(v_a_5875_);
                                    lean_dec_ref(v_funTypes_5695_);
                                    lean_dec(v___x_5693_);
                                    lean_dec_ref(v___f_5692_);
                                    lean_dec_ref(v_preDefs_5690_);
                                    lean_dec_ref(v_xs_5689_);
                                    lean_dec_ref(v_fixedParamPerms_5688_);
                                    lean_dec(v___x_5687_);
                                    lean_dec_ref(v___x_5686_);
                                    lean_dec_ref(v_recArgInfos_5684_);
                                    lean_dec_ref(v___f_5683_);
                                    v_a_5888_ = lean_ctor_get(v___x_5887_, 0);
                                    v_isSharedCheck_5895_ = (!lean_is_exclusive(v___x_5887_)) as u8;
                                    if v_isSharedCheck_5895_ == 0 {
                                        v___x_5890_ = v___x_5887_;
                                        v_isShared_5891_ = v_isSharedCheck_5895_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5888_);
                                        lean_dec(v___x_5887_);
                                        v___x_5890_ = lean_box(0);
                                        v_isShared_5891_ = v_isSharedCheck_5895_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_5877_);
                            lean_dec(v_a_5875_);
                            lean_dec_ref(v_funTypes_5695_);
                            lean_dec(v___x_5693_);
                            lean_dec_ref(v___f_5692_);
                            lean_dec_ref(v_preDefs_5690_);
                            lean_dec_ref(v_xs_5689_);
                            lean_dec_ref(v_fixedParamPerms_5688_);
                            lean_dec(v___x_5687_);
                            lean_dec_ref(v___x_5686_);
                            lean_dec_ref(v_recArgInfos_5684_);
                            lean_dec_ref(v___f_5683_);
                            v_a_5896_ = lean_ctor_get(v___x_5878_, 0);
                            v_isSharedCheck_5903_ = (!lean_is_exclusive(v___x_5878_)) as u8;
                            if v_isSharedCheck_5903_ == 0 {
                                v___x_5898_ = v___x_5878_;
                                v_isShared_5899_ = v_isSharedCheck_5903_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_5896_);
                                lean_dec(v___x_5878_);
                                v___x_5898_ = lean_box(0);
                                v_isShared_5899_ = v_isSharedCheck_5903_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5875_);
                        lean_dec_ref(v_funTypes_5695_);
                        lean_dec(v___x_5693_);
                        lean_dec_ref(v___f_5692_);
                        lean_dec_ref(v_preDefs_5690_);
                        lean_dec_ref(v_xs_5689_);
                        lean_dec_ref(v_fixedParamPerms_5688_);
                        lean_dec(v___x_5687_);
                        lean_dec_ref(v___x_5686_);
                        lean_dec_ref(v_recArgInfos_5684_);
                        lean_dec_ref(v___f_5683_);
                        v_a_5904_ = lean_ctor_get(v___x_5876_, 0);
                        v_isSharedCheck_5911_ = (!lean_is_exclusive(v___x_5876_)) as u8;
                        if v_isSharedCheck_5911_ == 0 {
                            v___x_5906_ = v___x_5876_;
                            v_isShared_5907_ = v_isSharedCheck_5911_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_5904_);
                            lean_dec(v___x_5876_);
                            v___x_5906_ = lean_box(0);
                            v_isShared_5907_ = v_isSharedCheck_5911_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_funTypes_5695_);
                    lean_dec(v___x_5693_);
                    lean_dec_ref(v___f_5692_);
                    lean_dec_ref(v_preDefs_5690_);
                    lean_dec_ref(v_xs_5689_);
                    lean_dec_ref(v_fixedParamPerms_5688_);
                    lean_dec(v___x_5687_);
                    lean_dec_ref(v___x_5686_);
                    lean_dec_ref(v_recArgInfos_5684_);
                    lean_dec_ref(v___f_5683_);
                    v_a_5912_ = lean_ctor_get(v___x_5874_, 0);
                    v_isSharedCheck_5919_ = (!lean_is_exclusive(v___x_5874_)) as u8;
                    if v_isSharedCheck_5919_ == 0 {
                        v___x_5914_ = v___x_5874_;
                        v_isShared_5915_ = v_isSharedCheck_5919_;
                        state = 32;
                        continue;
                    } else {
                        lean_inc(v_a_5912_);
                        lean_dec(v___x_5874_);
                        v___x_5914_ = lean_box(0);
                        v_isShared_5915_ = v_isSharedCheck_5919_;
                        state = 32;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_5891_ == 0 {
                    v___x_5893_ = v___x_5890_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5888_);
                    v___x_5893_ = v_reuseFailAlloc_5894_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_5893_;
            }
            28 => {
                if v_isShared_5899_ == 0 {
                    v___x_5901_ = v___x_5898_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_a_5896_);
                    v___x_5901_ = v_reuseFailAlloc_5902_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5901_;
            }
            30 => {
                if v_isShared_5907_ == 0 {
                    v___x_5909_ = v___x_5906_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5910_, 0, v_a_5904_);
                    v___x_5909_ = v_reuseFailAlloc_5910_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_5909_;
            }
            32 => {
                if v_isShared_5915_ == 0 {
                    v___x_5917_ = v___x_5914_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5918_, 0, v_a_5912_);
                    v___x_5917_ = v_reuseFailAlloc_5918_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5917_;
            }
            34 => {
                if v_isShared_5939_ == 0 {
                    v___x_5941_ = v___x_5938_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_a_5936_);
                    v___x_5941_ = v_reuseFailAlloc_5942_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_5941_;
            }
            36 => {
                if v_isShared_5947_ == 0 {
                    v___x_5949_ = v___x_5946_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5950_, 0, v_a_5944_);
                    v___x_5949_ = v_reuseFailAlloc_5950_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_5949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5952_: *mut LeanObject = *_args.add(0);
    let mut v_recArgInfos_5953_: *mut LeanObject = *_args.add(1);
    let mut v_a_5954_: *mut LeanObject = *_args.add(2);
    let mut v___x_5955_: *mut LeanObject = *_args.add(3);
    let mut v___x_5956_: *mut LeanObject = *_args.add(4);
    let mut v_fixedParamPerms_5957_: *mut LeanObject = *_args.add(5);
    let mut v_xs_5958_: *mut LeanObject = *_args.add(6);
    let mut v_preDefs_5959_: *mut LeanObject = *_args.add(7);
    let mut v_numIndices_5960_: *mut LeanObject = *_args.add(8);
    let mut v___f_5961_: *mut LeanObject = *_args.add(9);
    let mut v___x_5962_: *mut LeanObject = *_args.add(10);
    let mut v_a_5963_: *mut LeanObject = *_args.add(11);
    let mut v_funTypes_5964_: *mut LeanObject = *_args.add(12);
    let mut v_motives_5965_: *mut LeanObject = *_args.add(13);
    let mut v___y_5966_: *mut LeanObject = *_args.add(14);
    let mut v___y_5967_: *mut LeanObject = *_args.add(15);
    let mut v___y_5968_: *mut LeanObject = *_args.add(16);
    let mut v___y_5969_: *mut LeanObject = *_args.add(17);
    let mut v___y_5970_: *mut LeanObject = *_args.add(18);
    let mut v_a_28818__boxed_5971_: u8 = 0;
    let mut v_res_5972_: *mut LeanObject = core::ptr::null_mut();
    v_a_28818__boxed_5971_ = (lean_unbox(v_a_5963_) as u8);
    v_res_5972_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_5952_, v_recArgInfos_5953_, v_a_5954_, v___x_5955_, v___x_5956_, v_fixedParamPerms_5957_, v_xs_5958_, v_preDefs_5959_, v_numIndices_5960_, v___f_5961_, v___x_5962_, v_a_28818__boxed_5971_, v_funTypes_5964_, v_motives_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
    lean_dec(v___y_5969_);
    lean_dec_ref(v___y_5968_);
    lean_dec(v___y_5967_);
    lean_dec_ref(v___y_5966_);
    lean_dec(v_numIndices_5960_);
    lean_dec_ref(v_a_5954_);
    return v_res_5972_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(
    mut v_a_5973_: *mut LeanObject,
    mut v_funTypes_5974_: *mut LeanObject,
    mut v_as_5975_: *mut LeanObject,
    mut v_i_5976_: *mut LeanObject,
    mut v_j_5977_: *mut LeanObject,
    mut v_bs_5978_: *mut LeanObject,
    mut v___y_5979_: *mut LeanObject,
    mut v___y_5980_: *mut LeanObject,
    mut v___y_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5985_: u8 = 0;
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6001_: u8 = 0;
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5984_ = lean_unsigned_to_nat(0);
                v_isZero_5985_ = lean_nat_dec_eq(v_i_5976_, v_zero_5984_);
                if v_isZero_5985_ == 1 {
                    lean_dec(v_j_5977_);
                    lean_dec(v_i_5976_);
                    v___x_5986_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5986_, 0, v_bs_5978_);
                    return v___x_5986_;
                } else {
                    v___x_5987_ = l_Lean_instInhabitedExpr;
                    v___x_5988_ = lean_array_fget_borrowed(v_as_5975_, v_j_5977_);
                    v___x_5989_ = lean_array_get_borrowed(v___x_5987_, v_a_5973_, v_j_5977_);
                    v___x_5990_ = lean_array_get_borrowed(v___x_5987_, v_funTypes_5974_, v_j_5977_);
                    lean_inc(v___x_5990_);
                    lean_inc(v___x_5989_);
                    lean_inc(v___x_5988_);
                    v___x_5991_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(
                        v___x_5988_,
                        v___x_5989_,
                        v___x_5990_,
                        v___y_5979_,
                        v___y_5980_,
                        v___y_5981_,
                        v___y_5982_,
                    );
                    if lean_obj_tag(v___x_5991_) == 0 {
                        v_a_5992_ = lean_ctor_get(v___x_5991_, 0);
                        lean_inc(v_a_5992_);
                        lean_dec_ref_known(v___x_5991_, 1);
                        v_one_5993_ = lean_unsigned_to_nat(1);
                        v_n_5994_ = lean_nat_sub(v_i_5976_, v_one_5993_);
                        lean_dec(v_i_5976_);
                        v___x_5995_ = lean_nat_add(v_j_5977_, v_one_5993_);
                        lean_dec(v_j_5977_);
                        v___x_5996_ = lean_array_push(v_bs_5978_, v_a_5992_);
                        v_i_5976_ = v_n_5994_;
                        v_j_5977_ = v___x_5995_;
                        v_bs_5978_ = v___x_5996_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5978_);
                        lean_dec(v_j_5977_);
                        lean_dec(v_i_5976_);
                        v_a_5998_ = lean_ctor_get(v___x_5991_, 0);
                        v_isSharedCheck_6005_ = (!lean_is_exclusive(v___x_5991_)) as u8;
                        if v_isSharedCheck_6005_ == 0 {
                            v___x_6000_ = v___x_5991_;
                            v_isShared_6001_ = v_isSharedCheck_6005_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5998_);
                            lean_dec(v___x_5991_);
                            v___x_6000_ = lean_box(0);
                            v_isShared_6001_ = v_isSharedCheck_6005_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6001_ == 0 {
                    v___x_6003_ = v___x_6000_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6004_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_a_5998_);
                    v___x_6003_ = v_reuseFailAlloc_6004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg___boxed(
    mut v_a_6006_: *mut LeanObject,
    mut v_funTypes_6007_: *mut LeanObject,
    mut v_as_6008_: *mut LeanObject,
    mut v_i_6009_: *mut LeanObject,
    mut v_j_6010_: *mut LeanObject,
    mut v_bs_6011_: *mut LeanObject,
    mut v___y_6012_: *mut LeanObject,
    mut v___y_6013_: *mut LeanObject,
    mut v___y_6014_: *mut LeanObject,
    mut v___y_6015_: *mut LeanObject,
    mut v___y_6016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6017_: *mut LeanObject = core::ptr::null_mut();
    v_res_6017_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_6006_, v_funTypes_6007_, v_as_6008_, v_i_6009_, v_j_6010_, v_bs_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_);
    lean_dec(v___y_6015_);
    lean_dec_ref(v___y_6014_);
    lean_dec(v___y_6013_);
    lean_dec_ref(v___y_6012_);
    lean_dec_ref(v_as_6008_);
    lean_dec_ref(v_funTypes_6007_);
    lean_dec_ref(v_a_6006_);
    return v_res_6017_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(
    mut v_recArgInfos_6018_: *mut LeanObject,
    mut v_a_6019_: *mut LeanObject,
    mut v___x_6020_: *mut LeanObject,
    mut v___f_6021_: *mut LeanObject,
    mut v_funTypes_6022_: *mut LeanObject,
    mut v___y_6023_: *mut LeanObject,
    mut v___y_6024_: *mut LeanObject,
    mut v___y_6025_: *mut LeanObject,
    mut v___y_6026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6036_: u8 = 0;
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6040_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6028_ = lean_array_get_size(v_recArgInfos_6018_);
                v___x_6029_ = lean_mk_empty_array_with_capacity(v___x_6028_);
                v___x_6030_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_6019_, v_funTypes_6022_, v_recArgInfos_6018_, v___x_6028_, v___x_6020_, v___x_6029_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_);
                if lean_obj_tag(v___x_6030_) == 0 {
                    v_a_6031_ = lean_ctor_get(v___x_6030_, 0);
                    lean_inc(v_a_6031_);
                    lean_dec_ref_known(v___x_6030_, 1);
                    lean_inc(v___y_6026_);
                    lean_inc_ref(v___y_6025_);
                    lean_inc(v___y_6024_);
                    lean_inc_ref(v___y_6023_);
                    v___x_6032_ = lean_apply_7(
                        v___f_6021_,
                        v_funTypes_6022_,
                        v_a_6031_,
                        v___y_6023_,
                        v___y_6024_,
                        v___y_6025_,
                        v___y_6026_,
                        lean_box(0),
                    );
                    return v___x_6032_;
                } else {
                    lean_dec_ref(v_funTypes_6022_);
                    lean_dec_ref(v___f_6021_);
                    v_a_6033_ = lean_ctor_get(v___x_6030_, 0);
                    v_isSharedCheck_6040_ = (!lean_is_exclusive(v___x_6030_)) as u8;
                    if v_isSharedCheck_6040_ == 0 {
                        v___x_6035_ = v___x_6030_;
                        v_isShared_6036_ = v_isSharedCheck_6040_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6033_);
                        lean_dec(v___x_6030_);
                        v___x_6035_ = lean_box(0);
                        v_isShared_6036_ = v_isSharedCheck_6040_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6036_ == 0 {
                    v___x_6038_ = v___x_6035_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6039_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6039_, 0, v_a_6033_);
                    v___x_6038_ = v_reuseFailAlloc_6039_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed(
    mut v_recArgInfos_6041_: *mut LeanObject,
    mut v_a_6042_: *mut LeanObject,
    mut v___x_6043_: *mut LeanObject,
    mut v___f_6044_: *mut LeanObject,
    mut v_funTypes_6045_: *mut LeanObject,
    mut v___y_6046_: *mut LeanObject,
    mut v___y_6047_: *mut LeanObject,
    mut v___y_6048_: *mut LeanObject,
    mut v___y_6049_: *mut LeanObject,
    mut v___y_6050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6051_: *mut LeanObject = core::ptr::null_mut();
    v_res_6051_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3(v_recArgInfos_6041_, v_a_6042_, v___x_6043_, v___f_6044_, v_funTypes_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_);
    lean_dec(v___y_6049_);
    lean_dec_ref(v___y_6048_);
    lean_dec(v___y_6047_);
    lean_dec_ref(v___y_6046_);
    lean_dec_ref(v_a_6042_);
    lean_dec_ref(v_recArgInfos_6041_);
    return v_res_6051_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(
    mut v_msg_6052_: *mut LeanObject,
    mut v___y_6053_: *mut LeanObject,
    mut v___y_6054_: *mut LeanObject,
    mut v___y_6055_: *mut LeanObject,
    mut v___y_6056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6063_: u8 = 0;
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6058_ = lean_ctor_get(v___y_6055_, 5);
                v___x_6059_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11_spec__21(v_msg_6052_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_);
                v_a_6060_ = lean_ctor_get(v___x_6059_, 0);
                v_isSharedCheck_6068_ = (!lean_is_exclusive(v___x_6059_)) as u8;
                if v_isSharedCheck_6068_ == 0 {
                    v___x_6062_ = v___x_6059_;
                    v_isShared_6063_ = v_isSharedCheck_6068_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6060_);
                    lean_dec(v___x_6059_);
                    v___x_6062_ = lean_box(0);
                    v_isShared_6063_ = v_isSharedCheck_6068_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_6058_);
                v___x_6064_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6064_, 0, v_ref_6058_);
                lean_ctor_set(v___x_6064_, 1, v_a_6060_);
                if v_isShared_6063_ == 0 {
                    lean_ctor_set_tag(v___x_6062_, 1);
                    lean_ctor_set(v___x_6062_, 0, v___x_6064_);
                    v___x_6066_ = v___x_6062_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6067_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6067_, 0, v___x_6064_);
                    v___x_6066_ = v_reuseFailAlloc_6067_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg___boxed(
    mut v_msg_6069_: *mut LeanObject,
    mut v___y_6070_: *mut LeanObject,
    mut v___y_6071_: *mut LeanObject,
    mut v___y_6072_: *mut LeanObject,
    mut v___y_6073_: *mut LeanObject,
    mut v___y_6074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6075_: *mut LeanObject = core::ptr::null_mut();
    v_res_6075_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_);
    lean_dec(v___y_6073_);
    lean_dec_ref(v___y_6072_);
    lean_dec(v___y_6071_);
    lean_dec_ref(v___y_6070_);
    return v_res_6075_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    v___x_6077_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__0;
    v___x_6078_ = l_Lean_stringToMessageData(v___x_6077_);
    return v___x_6078_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    v___x_6080_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__2;
    v___x_6081_ = l_Lean_stringToMessageData(v___x_6080_);
    return v___x_6081_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(
    mut v_constName_6082_: *mut LeanObject,
    mut v___y_6083_: *mut LeanObject,
    mut v___y_6084_: *mut LeanObject,
    mut v___y_6085_: *mut LeanObject,
    mut v___y_6086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: u8 = 0;
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6101_: u8 = 0;
    let mut v___x_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6088_ = lean_st_ref_get(v___y_6086_);
                v_env_6089_ = lean_ctor_get(v___x_6088_, 0);
                lean_inc_ref(v_env_6089_);
                lean_dec(v___x_6088_);
                lean_inc(v_constName_6082_);
                v___x_6090_ = l_Lean_isInductiveCore_x3f(v_env_6089_, v_constName_6082_);
                if lean_obj_tag(v___x_6090_) == 0 {
                    v___x_6091_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__1);
                    v___x_6092_ = 0;
                    v___x_6093_ = l_Lean_MessageData_ofConstName(v_constName_6082_, v___x_6092_);
                    v___x_6094_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6094_, 0, v___x_6091_);
                    lean_ctor_set(v___x_6094_, 1, v___x_6093_);
                    v___x_6095_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___closed__3);
                    v___x_6096_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6096_, 0, v___x_6094_);
                    lean_ctor_set(v___x_6096_, 1, v___x_6095_);
                    v___x_6097_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_6096_, v___y_6083_, v___y_6084_, v___y_6085_, v___y_6086_);
                    return v___x_6097_;
                } else {
                    lean_dec(v_constName_6082_);
                    v_val_6098_ = lean_ctor_get(v___x_6090_, 0);
                    v_isSharedCheck_6105_ = (!lean_is_exclusive(v___x_6090_)) as u8;
                    if v_isSharedCheck_6105_ == 0 {
                        v___x_6100_ = v___x_6090_;
                        v_isShared_6101_ = v_isSharedCheck_6105_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6098_);
                        lean_dec(v___x_6090_);
                        v___x_6100_ = lean_box(0);
                        v_isShared_6101_ = v_isSharedCheck_6105_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6101_ == 0 {
                    lean_ctor_set_tag(v___x_6100_, 0);
                    v___x_6103_ = v___x_6100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6104_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6104_, 0, v_val_6098_);
                    v___x_6103_ = v_reuseFailAlloc_6104_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6103_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4___boxed(
    mut v_constName_6106_: *mut LeanObject,
    mut v___y_6107_: *mut LeanObject,
    mut v___y_6108_: *mut LeanObject,
    mut v___y_6109_: *mut LeanObject,
    mut v___y_6110_: *mut LeanObject,
    mut v___y_6111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6112_: *mut LeanObject = core::ptr::null_mut();
    v_res_6112_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v_constName_6106_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_);
    lean_dec(v___y_6110_);
    lean_dec_ref(v___y_6109_);
    lean_dec(v___y_6108_);
    lean_dec_ref(v___y_6107_);
    return v_res_6112_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(
    mut v_a_6113_: *mut LeanObject,
    mut v_a_6114_: *mut LeanObject,
    mut v_as_6115_: *mut LeanObject,
    mut v_i_6116_: *mut LeanObject,
    mut v_j_6117_: *mut LeanObject,
    mut v_bs_6118_: *mut LeanObject,
    mut v___y_6119_: *mut LeanObject,
    mut v___y_6120_: *mut LeanObject,
    mut v___y_6121_: *mut LeanObject,
    mut v___y_6122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6125_: u8 = 0;
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6141_: u8 = 0;
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6124_ = lean_unsigned_to_nat(0);
                v_isZero_6125_ = lean_nat_dec_eq(v_i_6116_, v_zero_6124_);
                if v_isZero_6125_ == 1 {
                    lean_dec(v_j_6117_);
                    lean_dec(v_i_6116_);
                    v___x_6126_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6126_, 0, v_bs_6118_);
                    return v___x_6126_;
                } else {
                    v___x_6127_ = l_Lean_instInhabitedExpr;
                    v___x_6128_ = lean_array_fget_borrowed(v_as_6115_, v_j_6117_);
                    v___x_6129_ = lean_array_get_borrowed(v___x_6127_, v_a_6113_, v_j_6117_);
                    v___x_6130_ = lean_array_get_borrowed(v___x_6127_, v_a_6114_, v_j_6117_);
                    lean_inc(v___x_6130_);
                    lean_inc(v___x_6129_);
                    lean_inc(v___x_6128_);
                    v___x_6131_ = l_Lean_Elab_Structural_mkBRecOnMotive(
                        v___x_6128_,
                        v___x_6129_,
                        v___x_6130_,
                        v___y_6119_,
                        v___y_6120_,
                        v___y_6121_,
                        v___y_6122_,
                    );
                    if lean_obj_tag(v___x_6131_) == 0 {
                        v_a_6132_ = lean_ctor_get(v___x_6131_, 0);
                        lean_inc(v_a_6132_);
                        lean_dec_ref_known(v___x_6131_, 1);
                        v_one_6133_ = lean_unsigned_to_nat(1);
                        v_n_6134_ = lean_nat_sub(v_i_6116_, v_one_6133_);
                        lean_dec(v_i_6116_);
                        v___x_6135_ = lean_nat_add(v_j_6117_, v_one_6133_);
                        lean_dec(v_j_6117_);
                        v___x_6136_ = lean_array_push(v_bs_6118_, v_a_6132_);
                        v_i_6116_ = v_n_6134_;
                        v_j_6117_ = v___x_6135_;
                        v_bs_6118_ = v___x_6136_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_6118_);
                        lean_dec(v_j_6117_);
                        lean_dec(v_i_6116_);
                        v_a_6138_ = lean_ctor_get(v___x_6131_, 0);
                        v_isSharedCheck_6145_ = (!lean_is_exclusive(v___x_6131_)) as u8;
                        if v_isSharedCheck_6145_ == 0 {
                            v___x_6140_ = v___x_6131_;
                            v_isShared_6141_ = v_isSharedCheck_6145_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6138_);
                            lean_dec(v___x_6131_);
                            v___x_6140_ = lean_box(0);
                            v_isShared_6141_ = v_isSharedCheck_6145_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6141_ == 0 {
                    v___x_6143_ = v___x_6140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6144_, 0, v_a_6138_);
                    v___x_6143_ = v_reuseFailAlloc_6144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg___boxed(
    mut v_a_6146_: *mut LeanObject,
    mut v_a_6147_: *mut LeanObject,
    mut v_as_6148_: *mut LeanObject,
    mut v_i_6149_: *mut LeanObject,
    mut v_j_6150_: *mut LeanObject,
    mut v_bs_6151_: *mut LeanObject,
    mut v___y_6152_: *mut LeanObject,
    mut v___y_6153_: *mut LeanObject,
    mut v___y_6154_: *mut LeanObject,
    mut v___y_6155_: *mut LeanObject,
    mut v___y_6156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6157_: *mut LeanObject = core::ptr::null_mut();
    v_res_6157_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_6146_, v_a_6147_, v_as_6148_, v_i_6149_, v_j_6150_, v_bs_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_);
    lean_dec(v___y_6155_);
    lean_dec_ref(v___y_6154_);
    lean_dec(v___y_6153_);
    lean_dec_ref(v___y_6152_);
    lean_dec_ref(v_as_6148_);
    lean_dec_ref(v_a_6147_);
    lean_dec_ref(v_a_6146_);
    return v_res_6157_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(
    mut v_hi_6158_: *mut LeanObject,
    mut v_pivot_6159_: *mut LeanObject,
    mut v_as_6160_: *mut LeanObject,
    mut v_i_6161_: *mut LeanObject,
    mut v_k_6162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6163_: u8 = 0;
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: u8 = 0;
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6163_ = lean_nat_dec_lt(v_k_6162_, v_hi_6158_);
                if v___x_6163_ == 0 {
                    lean_dec(v_k_6162_);
                    v___x_6164_ = lean_array_fswap(v_as_6160_, v_i_6161_, v_hi_6158_);
                    v___x_6165_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6165_, 0, v_i_6161_);
                    lean_ctor_set(v___x_6165_, 1, v___x_6164_);
                    return v___x_6165_;
                } else {
                    v___x_6166_ = lean_array_fget_borrowed(v_as_6160_, v_k_6162_);
                    v___x_6167_ = l_Nat_blt(v___x_6166_, v_pivot_6159_);
                    if v___x_6167_ == 0 {
                        v___x_6168_ = lean_unsigned_to_nat(1);
                        v___x_6169_ = lean_nat_add(v_k_6162_, v___x_6168_);
                        lean_dec(v_k_6162_);
                        v_k_6162_ = v___x_6169_;
                        state = 0;
                        continue;
                    } else {
                        v___x_6171_ = lean_array_fswap(v_as_6160_, v_i_6161_, v_k_6162_);
                        v___x_6172_ = lean_unsigned_to_nat(1);
                        v___x_6173_ = lean_nat_add(v_i_6161_, v___x_6172_);
                        lean_dec(v_i_6161_);
                        v___x_6174_ = lean_nat_add(v_k_6162_, v___x_6172_);
                        lean_dec(v_k_6162_);
                        v_as_6160_ = v___x_6171_;
                        v_i_6161_ = v___x_6173_;
                        v_k_6162_ = v___x_6174_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg___boxed(
    mut v_hi_6176_: *mut LeanObject,
    mut v_pivot_6177_: *mut LeanObject,
    mut v_as_6178_: *mut LeanObject,
    mut v_i_6179_: *mut LeanObject,
    mut v_k_6180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6181_: *mut LeanObject = core::ptr::null_mut();
    v_res_6181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_6176_, v_pivot_6177_, v_as_6178_, v_i_6179_, v_k_6180_);
    lean_dec(v_pivot_6177_);
    lean_dec(v_hi_6176_);
    return v_res_6181_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(
    mut v_n_6182_: *mut LeanObject,
    mut v_as_6183_: *mut LeanObject,
    mut v_lo_6184_: *mut LeanObject,
    mut v_hi_6185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: u8 = 0;
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: u8 = 0;
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: u8 = 0;
    let mut v___x_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: u8 = 0;
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: u8 = 0;
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6197_ = lean_nat_dec_lt(v_lo_6184_, v_hi_6185_);
                if v___x_6197_ == 0 {
                    lean_dec(v_lo_6184_);
                    return v_as_6183_;
                } else {
                    v___x_6198_ = lean_nat_add(v_lo_6184_, v_hi_6185_);
                    v___x_6199_ = lean_unsigned_to_nat(1);
                    v_mid_6200_ = lean_nat_shiftr(v___x_6198_, v___x_6199_);
                    lean_dec(v___x_6198_);
                    v___x_6213_ = lean_array_fget_borrowed(v_as_6183_, v_mid_6200_);
                    v___x_6214_ = lean_array_fget_borrowed(v_as_6183_, v_lo_6184_);
                    v___x_6215_ = l_Nat_blt(v___x_6213_, v___x_6214_);
                    if v___x_6215_ == 0 {
                        v___y_6208_ = v_as_6183_;
                        state = 3;
                        continue;
                    } else {
                        v___x_6216_ = lean_array_fswap(v_as_6183_, v_lo_6184_, v_mid_6200_);
                        v___y_6208_ = v___x_6216_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_6188_ = lean_array_fget(v___y_6187_, v_hi_6185_);
                lean_inc_n(v_lo_6184_, 2);
                v___x_6189_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_6185_, v_pivot_6188_, v___y_6187_, v_lo_6184_, v_lo_6184_);
                lean_dec(v_pivot_6188_);
                v_fst_6190_ = lean_ctor_get(v___x_6189_, 0);
                lean_inc(v_fst_6190_);
                v_snd_6191_ = lean_ctor_get(v___x_6189_, 1);
                lean_inc(v_snd_6191_);
                lean_dec_ref(v___x_6189_);
                v___x_6192_ = lean_nat_dec_le(v_hi_6185_, v_fst_6190_);
                if v___x_6192_ == 0 {
                    v___x_6193_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_6182_, v_snd_6191_, v_lo_6184_, v_fst_6190_);
                    v___x_6194_ = lean_unsigned_to_nat(1);
                    v___x_6195_ = lean_nat_add(v_fst_6190_, v___x_6194_);
                    lean_dec(v_fst_6190_);
                    v_as_6183_ = v___x_6193_;
                    v_lo_6184_ = v___x_6195_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_6190_);
                    lean_dec(v_lo_6184_);
                    return v_snd_6191_;
                }
            }
            2 => {
                v___x_6203_ = lean_array_fget_borrowed(v___y_6202_, v_mid_6200_);
                v___x_6204_ = lean_array_fget_borrowed(v___y_6202_, v_hi_6185_);
                v___x_6205_ = l_Nat_blt(v___x_6203_, v___x_6204_);
                if v___x_6205_ == 0 {
                    lean_dec(v_mid_6200_);
                    v___y_6187_ = v___y_6202_;
                    state = 1;
                    continue;
                } else {
                    v___x_6206_ = lean_array_fswap(v___y_6202_, v_mid_6200_, v_hi_6185_);
                    lean_dec(v_mid_6200_);
                    v___y_6187_ = v___x_6206_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6209_ = lean_array_fget_borrowed(v___y_6208_, v_hi_6185_);
                v___x_6210_ = lean_array_fget_borrowed(v___y_6208_, v_lo_6184_);
                v___x_6211_ = l_Nat_blt(v___x_6209_, v___x_6210_);
                if v___x_6211_ == 0 {
                    v___y_6202_ = v___y_6208_;
                    state = 2;
                    continue;
                } else {
                    v___x_6212_ = lean_array_fswap(v___y_6208_, v_lo_6184_, v_hi_6185_);
                    v___y_6202_ = v___x_6212_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg___boxed(
    mut v_n_6217_: *mut LeanObject,
    mut v_as_6218_: *mut LeanObject,
    mut v_lo_6219_: *mut LeanObject,
    mut v_hi_6220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6221_: *mut LeanObject = core::ptr::null_mut();
    v_res_6221_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_6217_, v_as_6218_, v_lo_6219_, v_hi_6220_);
    lean_dec(v_hi_6220_);
    lean_dec(v_n_6217_);
    return v_res_6221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(
    mut v_xs_6222_: *mut LeanObject,
    mut v_f_6223_: *mut LeanObject,
    mut v_x_6224_: *mut LeanObject,
    mut v_as_6225_: *mut LeanObject,
    mut v_i_6226_: usize,
    mut v_stop_6227_: usize,
    mut v_b_6228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: usize = 0;
    let mut v___x_6232_: usize = 0;
    let mut v___x_6234_: u8 = 0;
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: u8 = 0;
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6234_ = lean_usize_dec_eq(v_i_6226_, v_stop_6227_);
                if v___x_6234_ == 0 {
                    v___x_6235_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
                    v___x_6236_ = lean_array_uget_borrowed(v_as_6225_, v_i_6226_);
                    v___x_6237_ = lean_array_get_borrowed(v___x_6235_, v_xs_6222_, v___x_6236_);
                    lean_inc_ref(v_f_6223_);
                    lean_inc(v___x_6237_);
                    v___x_6238_ = lean_apply_1(v_f_6223_, v___x_6237_);
                    v___x_6239_ = lean_nat_dec_eq(v___x_6238_, v_x_6224_);
                    lean_dec(v___x_6238_);
                    if v___x_6239_ == 0 {
                        v___y_6230_ = v_b_6228_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_6236_);
                        v___x_6240_ = lean_array_push(v_b_6228_, v___x_6236_);
                        v___y_6230_ = v___x_6240_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_6223_);
                    return v_b_6228_;
                }
            }
            1 => {
                v___x_6231_ = 1usize;
                v___x_6232_ = lean_usize_add(v_i_6226_, v___x_6231_);
                v_i_6226_ = v___x_6232_;
                v_b_6228_ = v___y_6230_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6___boxed(
    mut v_xs_6241_: *mut LeanObject,
    mut v_f_6242_: *mut LeanObject,
    mut v_x_6243_: *mut LeanObject,
    mut v_as_6244_: *mut LeanObject,
    mut v_i_6245_: *mut LeanObject,
    mut v_stop_6246_: *mut LeanObject,
    mut v_b_6247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6248_: usize = 0;
    let mut v_stop_boxed_6249_: usize = 0;
    let mut v_res_6250_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6248_ = lean_unbox_usize(v_i_6245_);
    lean_dec(v_i_6245_);
    v_stop_boxed_6249_ = lean_unbox_usize(v_stop_6246_);
    lean_dec(v_stop_6246_);
    v_res_6250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_6241_, v_f_6242_, v_x_6243_, v_as_6244_, v_i_boxed_6248_, v_stop_boxed_6249_, v_b_6247_);
    lean_dec_ref(v_as_6244_);
    lean_dec(v_x_6243_);
    lean_dec_ref(v_xs_6241_);
    return v_res_6250_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(
    mut v_xs_6253_: *mut LeanObject,
    mut v_f_6254_: *mut LeanObject,
    mut v_sz_6255_: usize,
    mut v_i_6256_: usize,
    mut v_bs_6257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6258_: u8 = 0;
    let mut v_v_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: usize = 0;
    let mut v___x_6265_: usize = 0;
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: u8 = 0;
    let mut v___x_6273_: u8 = 0;
    let mut v___x_6274_: usize = 0;
    let mut v___x_6275_: usize = 0;
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: usize = 0;
    let mut v___x_6278_: usize = 0;
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6258_ = lean_usize_dec_lt(v_i_6256_, v_sz_6255_);
                if v___x_6258_ == 0 {
                    lean_dec_ref(v_f_6254_);
                    return v_bs_6257_;
                } else {
                    v_v_6259_ = lean_array_uget(v_bs_6257_, v_i_6256_);
                    v___x_6260_ = lean_unsigned_to_nat(0);
                    v_bs_x27_6261_ = lean_array_uset(v_bs_6257_, v_i_6256_, v___x_6260_);
                    v___x_6268_ = lean_array_get_size(v_xs_6253_);
                    v___x_6269_ = l_Array_range(v___x_6268_);
                    v___x_6270_ = lean_array_get_size(v___x_6269_);
                    v___x_6271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___closed__0;
                    v___x_6272_ = lean_nat_dec_lt(v___x_6260_, v___x_6270_);
                    if v___x_6272_ == 0 {
                        lean_dec_ref(v___x_6269_);
                        lean_dec(v_v_6259_);
                        v___y_6263_ = v___x_6271_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6273_ = lean_nat_dec_le(v___x_6270_, v___x_6270_);
                        if v___x_6273_ == 0 {
                            if v___x_6272_ == 0 {
                                lean_dec_ref(v___x_6269_);
                                lean_dec(v_v_6259_);
                                v___y_6263_ = v___x_6271_;
                                state = 1;
                                continue;
                            } else {
                                v___x_6274_ = 0usize;
                                v___x_6275_ = lean_usize_of_nat(v___x_6270_);
                                lean_inc_ref(v_f_6254_);
                                v___x_6276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_6253_, v_f_6254_, v_v_6259_, v___x_6269_, v___x_6274_, v___x_6275_, v___x_6271_);
                                lean_dec_ref(v___x_6269_);
                                lean_dec(v_v_6259_);
                                v___y_6263_ = v___x_6276_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_6277_ = 0usize;
                            v___x_6278_ = lean_usize_of_nat(v___x_6270_);
                            lean_inc_ref(v_f_6254_);
                            v___x_6279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__6(v_xs_6253_, v_f_6254_, v_v_6259_, v___x_6269_, v___x_6277_, v___x_6278_, v___x_6271_);
                            lean_dec_ref(v___x_6269_);
                            lean_dec(v_v_6259_);
                            v___y_6263_ = v___x_6279_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6264_ = 1usize;
                v___x_6265_ = lean_usize_add(v_i_6256_, v___x_6264_);
                v___x_6266_ = lean_array_uset(v_bs_x27_6261_, v_i_6256_, v___y_6263_);
                v_i_6256_ = v___x_6265_;
                v_bs_6257_ = v___x_6266_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8___boxed(
    mut v_xs_6280_: *mut LeanObject,
    mut v_f_6281_: *mut LeanObject,
    mut v_sz_6282_: *mut LeanObject,
    mut v_i_6283_: *mut LeanObject,
    mut v_bs_6284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6285_: usize = 0;
    let mut v_i_boxed_6286_: usize = 0;
    let mut v_res_6287_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6285_ = lean_unbox_usize(v_sz_6282_);
    lean_dec(v_sz_6282_);
    v_i_boxed_6286_ = lean_unbox_usize(v_i_6283_);
    lean_dec(v_i_6283_);
    v_res_6287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_6280_, v_f_6281_, v_sz_boxed_6285_, v_i_boxed_6286_, v_bs_6284_);
    lean_dec_ref(v_xs_6280_);
    return v_res_6287_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(
    mut v_as_6288_: *mut LeanObject,
    mut v_i_6289_: usize,
    mut v_stop_6290_: usize,
    mut v_b_6291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6292_: u8 = 0;
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: usize = 0;
    let mut v___x_6296_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6292_ = lean_usize_dec_eq(v_i_6289_, v_stop_6290_);
                if v___x_6292_ == 0 {
                    v___x_6293_ = lean_array_uget_borrowed(v_as_6288_, v_i_6289_);
                    v___x_6294_ = l_Array_append___redArg(v_b_6291_, v___x_6293_);
                    v___x_6295_ = 1usize;
                    v___x_6296_ = lean_usize_add(v_i_6289_, v___x_6295_);
                    v_i_6289_ = v___x_6296_;
                    v_b_6291_ = v___x_6294_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6291_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11___boxed(
    mut v_as_6298_: *mut LeanObject,
    mut v_i_6299_: *mut LeanObject,
    mut v_stop_6300_: *mut LeanObject,
    mut v_b_6301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6302_: usize = 0;
    let mut v_stop_boxed_6303_: usize = 0;
    let mut v_res_6304_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6302_ = lean_unbox_usize(v_i_6299_);
    lean_dec(v_i_6299_);
    v_stop_boxed_6303_ = lean_unbox_usize(v_stop_6300_);
    lean_dec(v_stop_6300_);
    v_res_6304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_as_6298_, v_i_boxed_6302_, v_stop_boxed_6303_, v_b_6301_);
    lean_dec_ref(v_as_6298_);
    return v_res_6304_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0()
-> *mut LeanObject {
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    v___x_6305_ = l_Array_instInhabited(lean_box(0));
    return v___x_6305_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(
    mut v_msg_6306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut LeanObject = core::ptr::null_mut();
    v___x_6307_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0_once), _init_l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7___closed__0);
    v___x_6308_ = lean_panic_fn_borrowed(v___x_6307_, v_msg_6306_);
    return v___x_6308_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(
    mut v_xs_6309_: *mut LeanObject,
    mut v_ys_6310_: *mut LeanObject,
    mut v_x_6311_: *mut LeanObject,
) -> u8 {
    let mut v_zero_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6313_: u8 = 0;
    let mut v_one_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6312_ = lean_unsigned_to_nat(0);
                v_isZero_6313_ = lean_nat_dec_eq(v_x_6311_, v_zero_6312_);
                if v_isZero_6313_ == 1 {
                    lean_dec(v_x_6311_);
                    return v_isZero_6313_;
                } else {
                    v_one_6314_ = lean_unsigned_to_nat(1);
                    v_n_6315_ = lean_nat_sub(v_x_6311_, v_one_6314_);
                    lean_dec(v_x_6311_);
                    v___x_6316_ = lean_array_fget_borrowed(v_xs_6309_, v_n_6315_);
                    v___x_6317_ = lean_array_fget_borrowed(v_ys_6310_, v_n_6315_);
                    v___x_6318_ = lean_nat_dec_eq(v___x_6316_, v___x_6317_);
                    if v___x_6318_ == 0 {
                        lean_dec(v_n_6315_);
                        return v___x_6318_;
                    } else {
                        v_x_6311_ = v_n_6315_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg___boxed(
    mut v_xs_6320_: *mut LeanObject,
    mut v_ys_6321_: *mut LeanObject,
    mut v_x_6322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6323_: u8 = 0;
    let mut v_r_6324_: *mut LeanObject = core::ptr::null_mut();
    v_res_6323_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_6320_, v_ys_6321_, v_x_6322_);
    lean_dec_ref(v_ys_6321_);
    lean_dec_ref(v_xs_6320_);
    v_r_6324_ = lean_box((v_res_6323_) as usize);
    return v_r_6324_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2()
-> *mut LeanObject {
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    v___x_6327_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__1;
    v___x_6328_ = lean_unsigned_to_nat(2);
    v___x_6329_ = lean_unsigned_to_nat(63);
    v___x_6330_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__0;
    v___x_6331_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg___closed__0;
    v___x_6332_ = l_mkPanicMessageWithDecl(
        v___x_6331_,
        v___x_6330_,
        v___x_6329_,
        v___x_6328_,
        v___x_6327_,
    );
    return v___x_6332_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(
    mut v_f_6335_: *mut LeanObject,
    mut v_xs_6336_: *mut LeanObject,
    mut v_ys_6337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6341_: usize = 0;
    let mut v___x_6342_: usize = 0;
    let mut v_positions_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: u8 = 0;
    let mut v___x_6351_: u8 = 0;
    let mut v___y_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: u8 = 0;
    let mut v___y_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: u8 = 0;
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: u8 = 0;
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: u8 = 0;
    let mut v___x_6376_: u8 = 0;
    let mut v___x_6377_: usize = 0;
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: usize = 0;
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_6341_ = lean_array_size(v_ys_6337_);
                v___x_6342_ = 0usize;
                v_positions_6343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__8(v_xs_6336_, v_f_6335_, v_sz_6341_, v___x_6342_, v_ys_6337_);
                v___x_6344_ = lean_array_get_size(v_xs_6336_);
                v___x_6345_ = l_Array_range(v___x_6344_);
                v___x_6372_ = lean_unsigned_to_nat(0);
                v___x_6373_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__3;
                v___x_6374_ = lean_array_get_size(v_positions_6343_);
                v___x_6375_ = lean_nat_dec_lt(v___x_6372_, v___x_6374_);
                if v___x_6375_ == 0 {
                    v___y_6365_ = v___x_6373_;
                    state = 5;
                    continue;
                } else {
                    v___x_6376_ = lean_nat_dec_le(v___x_6374_, v___x_6374_);
                    if v___x_6376_ == 0 {
                        if v___x_6375_ == 0 {
                            v___y_6365_ = v___x_6373_;
                            state = 5;
                            continue;
                        } else {
                            v___x_6377_ = lean_usize_of_nat(v___x_6374_);
                            v___x_6378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_6343_, v___x_6342_, v___x_6377_, v___x_6373_);
                            v___y_6365_ = v___x_6378_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_6379_ = lean_usize_of_nat(v___x_6374_);
                        v___x_6380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__11(v_positions_6343_, v___x_6342_, v___x_6379_, v___x_6373_);
                        v___y_6365_ = v___x_6380_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6339_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2_once), _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___closed__2);
                v___x_6340_ = l_panic___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__7(v___x_6339_);
                return v___x_6340_;
            }
            2 => {
                v___x_6348_ = lean_array_get_size(v___x_6345_);
                v___x_6349_ = lean_array_get_size(v___y_6347_);
                v___x_6350_ = lean_nat_dec_eq(v___x_6348_, v___x_6349_);
                if v___x_6350_ == 0 {
                    lean_dec_ref(v___y_6347_);
                    lean_dec_ref(v___x_6345_);
                    lean_dec_ref(v_positions_6343_);
                    state = 1;
                    continue;
                } else {
                    v___x_6351_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v___x_6345_, v___y_6347_, v___x_6348_);
                    lean_dec_ref(v___y_6347_);
                    lean_dec_ref(v___x_6345_);
                    if v___x_6351_ == 0 {
                        lean_dec_ref(v_positions_6343_);
                        state = 1;
                        continue;
                    } else {
                        return v_positions_6343_;
                    }
                }
            }
            3 => {
                v___x_6357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v___y_6354_, v___y_6353_, v___y_6355_, v___y_6356_);
                lean_dec(v___y_6356_);
                lean_dec(v___y_6354_);
                v___y_6347_ = v___x_6357_;
                state = 2;
                continue;
            }
            4 => {
                v___x_6363_ = lean_nat_dec_le(v___y_6362_, v___y_6359_);
                if v___x_6363_ == 0 {
                    lean_dec(v___y_6359_);
                    lean_inc(v___y_6362_);
                    v___y_6353_ = v___y_6360_;
                    v___y_6354_ = v___y_6361_;
                    v___y_6355_ = v___y_6362_;
                    v___y_6356_ = v___y_6362_;
                    state = 3;
                    continue;
                } else {
                    v___y_6353_ = v___y_6360_;
                    v___y_6354_ = v___y_6361_;
                    v___y_6355_ = v___y_6362_;
                    v___y_6356_ = v___y_6359_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_6366_ = lean_array_get_size(v___y_6365_);
                v___x_6367_ = lean_unsigned_to_nat(0);
                v___x_6368_ = lean_nat_dec_eq(v___x_6366_, v___x_6367_);
                if v___x_6368_ == 0 {
                    v___x_6369_ = lean_unsigned_to_nat(1);
                    v___x_6370_ = lean_nat_sub(v___x_6366_, v___x_6369_);
                    v___x_6371_ = lean_nat_dec_le(v___x_6367_, v___x_6370_);
                    if v___x_6371_ == 0 {
                        lean_inc(v___x_6370_);
                        v___y_6359_ = v___x_6370_;
                        v___y_6360_ = v___y_6365_;
                        v___y_6361_ = v___x_6366_;
                        v___y_6362_ = v___x_6370_;
                        state = 4;
                        continue;
                    } else {
                        v___y_6359_ = v___x_6370_;
                        v___y_6360_ = v___y_6365_;
                        v___y_6361_ = v___x_6366_;
                        v___y_6362_ = v___x_6367_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_6347_ = v___y_6365_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5___boxed(
    mut v_f_6381_: *mut LeanObject,
    mut v_xs_6382_: *mut LeanObject,
    mut v_ys_6383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6384_: *mut LeanObject = core::ptr::null_mut();
    v_res_6384_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v_f_6381_, v_xs_6382_, v_ys_6383_);
    lean_dec_ref(v_xs_6382_);
    return v_res_6384_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(
    mut v_fixedParamPerms_6385_: *mut LeanObject,
    mut v_xs_6386_: *mut LeanObject,
    mut v_as_6387_: *mut LeanObject,
    mut v_i_6388_: *mut LeanObject,
    mut v_j_6389_: *mut LeanObject,
    mut v_bs_6390_: *mut LeanObject,
    mut v___y_6391_: *mut LeanObject,
    mut v___y_6392_: *mut LeanObject,
    mut v___y_6393_: *mut LeanObject,
    mut v___y_6394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6397_: u8 = 0;
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perms_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6414_: u8 = 0;
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6396_ = lean_unsigned_to_nat(0);
                v_isZero_6397_ = lean_nat_dec_eq(v_i_6388_, v_zero_6396_);
                if v_isZero_6397_ == 1 {
                    lean_dec(v_j_6389_);
                    lean_dec(v_i_6388_);
                    lean_dec_ref(v_xs_6386_);
                    v___x_6398_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6398_, 0, v_bs_6390_);
                    return v___x_6398_;
                } else {
                    v_perms_6399_ = lean_ctor_get(v_fixedParamPerms_6385_, 1);
                    v___x_6400_ = lean_array_fget_borrowed(v_as_6387_, v_j_6389_);
                    v_value_6401_ = lean_ctor_get(v___x_6400_, 7);
                    v___x_6402_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
                    v___x_6403_ = lean_array_get_borrowed(v___x_6402_, v_perms_6399_, v_j_6389_);
                    lean_inc_ref(v_xs_6386_);
                    lean_inc_ref(v_value_6401_);
                    lean_inc(v___x_6403_);
                    v___x_6404_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(
                        v___x_6403_,
                        v_value_6401_,
                        v_xs_6386_,
                        v___y_6391_,
                        v___y_6392_,
                        v___y_6393_,
                        v___y_6394_,
                    );
                    if lean_obj_tag(v___x_6404_) == 0 {
                        v_a_6405_ = lean_ctor_get(v___x_6404_, 0);
                        lean_inc(v_a_6405_);
                        lean_dec_ref_known(v___x_6404_, 1);
                        v_one_6406_ = lean_unsigned_to_nat(1);
                        v_n_6407_ = lean_nat_sub(v_i_6388_, v_one_6406_);
                        lean_dec(v_i_6388_);
                        v___x_6408_ = lean_nat_add(v_j_6389_, v_one_6406_);
                        lean_dec(v_j_6389_);
                        v___x_6409_ = lean_array_push(v_bs_6390_, v_a_6405_);
                        v_i_6388_ = v_n_6407_;
                        v_j_6389_ = v___x_6408_;
                        v_bs_6390_ = v___x_6409_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_6390_);
                        lean_dec(v_j_6389_);
                        lean_dec(v_i_6388_);
                        lean_dec_ref(v_xs_6386_);
                        v_a_6411_ = lean_ctor_get(v___x_6404_, 0);
                        v_isSharedCheck_6418_ = (!lean_is_exclusive(v___x_6404_)) as u8;
                        if v_isSharedCheck_6418_ == 0 {
                            v___x_6413_ = v___x_6404_;
                            v_isShared_6414_ = v_isSharedCheck_6418_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6411_);
                            lean_dec(v___x_6404_);
                            v___x_6413_ = lean_box(0);
                            v_isShared_6414_ = v_isSharedCheck_6418_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6414_ == 0 {
                    v___x_6416_ = v___x_6413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6417_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6417_, 0, v_a_6411_);
                    v___x_6416_ = v_reuseFailAlloc_6417_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg___boxed(
    mut v_fixedParamPerms_6419_: *mut LeanObject,
    mut v_xs_6420_: *mut LeanObject,
    mut v_as_6421_: *mut LeanObject,
    mut v_i_6422_: *mut LeanObject,
    mut v_j_6423_: *mut LeanObject,
    mut v_bs_6424_: *mut LeanObject,
    mut v___y_6425_: *mut LeanObject,
    mut v___y_6426_: *mut LeanObject,
    mut v___y_6427_: *mut LeanObject,
    mut v___y_6428_: *mut LeanObject,
    mut v___y_6429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6430_: *mut LeanObject = core::ptr::null_mut();
    v_res_6430_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_6419_, v_xs_6420_, v_as_6421_, v_i_6422_, v_j_6423_, v_bs_6424_, v___y_6425_, v___y_6426_, v___y_6427_, v___y_6428_);
    lean_dec(v___y_6428_);
    lean_dec_ref(v___y_6427_);
    lean_dec(v___y_6426_);
    lean_dec_ref(v___y_6425_);
    lean_dec_ref(v_as_6421_);
    lean_dec_ref(v_fixedParamPerms_6419_);
    return v_res_6430_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(
    mut v_a_6431_: *mut LeanObject,
    mut v_a_6432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6438_: u8 = 0;
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6431_) == 0 {
                    v___x_6433_ = l_List_reverse___redArg(v_a_6432_);
                    return v___x_6433_;
                } else {
                    v_head_6434_ = lean_ctor_get(v_a_6431_, 0);
                    v_tail_6435_ = lean_ctor_get(v_a_6431_, 1);
                    v_isSharedCheck_6446_ = (!lean_is_exclusive(v_a_6431_)) as u8;
                    if v_isSharedCheck_6446_ == 0 {
                        v___x_6437_ = v_a_6431_;
                        v_isShared_6438_ = v_isSharedCheck_6446_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6435_);
                        lean_inc(v_head_6434_);
                        lean_dec(v_a_6431_);
                        v___x_6437_ = lean_box(0);
                        v_isShared_6438_ = v_isSharedCheck_6446_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6439_ = l_Nat_reprFast(v_head_6434_);
                v___x_6440_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6440_, 0, v___x_6439_);
                v___x_6441_ = l_Lean_MessageData_ofFormat(v___x_6440_);
                if v_isShared_6438_ == 0 {
                    lean_ctor_set(v___x_6437_, 1, v_a_6432_);
                    lean_ctor_set(v___x_6437_, 0, v___x_6441_);
                    v___x_6443_ = v___x_6437_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6445_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6445_, 0, v___x_6441_);
                    lean_ctor_set(v_reuseFailAlloc_6445_, 1, v_a_6432_);
                    v___x_6443_ = v_reuseFailAlloc_6445_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6431_ = v_tail_6435_;
                v_a_6432_ = v___x_6443_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(
    mut v_a_6447_: *mut LeanObject,
    mut v_a_6448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6454_: u8 = 0;
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6447_) == 0 {
                    v___x_6449_ = l_List_reverse___redArg(v_a_6448_);
                    return v___x_6449_;
                } else {
                    v_head_6450_ = lean_ctor_get(v_a_6447_, 0);
                    v_tail_6451_ = lean_ctor_get(v_a_6447_, 1);
                    v_isSharedCheck_6463_ = (!lean_is_exclusive(v_a_6447_)) as u8;
                    if v_isSharedCheck_6463_ == 0 {
                        v___x_6453_ = v_a_6447_;
                        v_isShared_6454_ = v_isSharedCheck_6463_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6451_);
                        lean_inc(v_head_6450_);
                        lean_dec(v_a_6447_);
                        v___x_6453_ = lean_box(0);
                        v_isShared_6454_ = v_isSharedCheck_6463_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6455_ = lean_array_to_list(v_head_6450_);
                v___x_6456_ = lean_box(0);
                v___x_6457_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_6455_, v___x_6456_);
                v___x_6458_ = l_Lean_MessageData_ofList(v___x_6457_);
                if v_isShared_6454_ == 0 {
                    lean_ctor_set(v___x_6453_, 1, v_a_6448_);
                    lean_ctor_set(v___x_6453_, 0, v___x_6458_);
                    v___x_6460_ = v___x_6453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6462_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6462_, 0, v___x_6458_);
                    lean_ctor_set(v_reuseFailAlloc_6462_, 1, v_a_6448_);
                    v___x_6460_ = v_reuseFailAlloc_6462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6447_ = v_tail_6451_;
                v_a_6448_ = v___x_6460_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(
    mut v_fixedParamPerms_6464_: *mut LeanObject,
    mut v_xs_6465_: *mut LeanObject,
    mut v_as_6466_: *mut LeanObject,
    mut v_i_6467_: *mut LeanObject,
    mut v_j_6468_: *mut LeanObject,
    mut v_bs_6469_: *mut LeanObject,
    mut v___y_6470_: *mut LeanObject,
    mut v___y_6471_: *mut LeanObject,
    mut v___y_6472_: *mut LeanObject,
    mut v___y_6473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6476_: u8 = 0;
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perms_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6493_: u8 = 0;
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6475_ = lean_unsigned_to_nat(0);
                v_isZero_6476_ = lean_nat_dec_eq(v_i_6467_, v_zero_6475_);
                if v_isZero_6476_ == 1 {
                    lean_dec(v_j_6468_);
                    lean_dec(v_i_6467_);
                    lean_dec_ref(v_xs_6465_);
                    v___x_6477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6477_, 0, v_bs_6469_);
                    return v___x_6477_;
                } else {
                    v_perms_6478_ = lean_ctor_get(v_fixedParamPerms_6464_, 1);
                    v___x_6479_ = lean_array_fget_borrowed(v_as_6466_, v_j_6468_);
                    v_type_6480_ = lean_ctor_get(v___x_6479_, 6);
                    v___x_6481_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
                    v___x_6482_ = lean_array_get_borrowed(v___x_6481_, v_perms_6478_, v_j_6468_);
                    lean_inc_ref(v_xs_6465_);
                    lean_inc_ref(v_type_6480_);
                    lean_inc(v___x_6482_);
                    v___x_6483_ = l_Lean_Elab_FixedParamPerm_instantiateForall(
                        v___x_6482_,
                        v_type_6480_,
                        v_xs_6465_,
                        v___y_6470_,
                        v___y_6471_,
                        v___y_6472_,
                        v___y_6473_,
                    );
                    if lean_obj_tag(v___x_6483_) == 0 {
                        v_a_6484_ = lean_ctor_get(v___x_6483_, 0);
                        lean_inc(v_a_6484_);
                        lean_dec_ref_known(v___x_6483_, 1);
                        v_one_6485_ = lean_unsigned_to_nat(1);
                        v_n_6486_ = lean_nat_sub(v_i_6467_, v_one_6485_);
                        lean_dec(v_i_6467_);
                        v___x_6487_ = lean_nat_add(v_j_6468_, v_one_6485_);
                        lean_dec(v_j_6468_);
                        v___x_6488_ = lean_array_push(v_bs_6469_, v_a_6484_);
                        v_i_6467_ = v_n_6486_;
                        v_j_6468_ = v___x_6487_;
                        v_bs_6469_ = v___x_6488_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_6469_);
                        lean_dec(v_j_6468_);
                        lean_dec(v_i_6467_);
                        lean_dec_ref(v_xs_6465_);
                        v_a_6490_ = lean_ctor_get(v___x_6483_, 0);
                        v_isSharedCheck_6497_ = (!lean_is_exclusive(v___x_6483_)) as u8;
                        if v_isSharedCheck_6497_ == 0 {
                            v___x_6492_ = v___x_6483_;
                            v_isShared_6493_ = v_isSharedCheck_6497_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6490_);
                            lean_dec(v___x_6483_);
                            v___x_6492_ = lean_box(0);
                            v_isShared_6493_ = v_isSharedCheck_6497_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6493_ == 0 {
                    v___x_6495_ = v___x_6492_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6496_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_a_6490_);
                    v___x_6495_ = v_reuseFailAlloc_6496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg___boxed(
    mut v_fixedParamPerms_6498_: *mut LeanObject,
    mut v_xs_6499_: *mut LeanObject,
    mut v_as_6500_: *mut LeanObject,
    mut v_i_6501_: *mut LeanObject,
    mut v_j_6502_: *mut LeanObject,
    mut v_bs_6503_: *mut LeanObject,
    mut v___y_6504_: *mut LeanObject,
    mut v___y_6505_: *mut LeanObject,
    mut v___y_6506_: *mut LeanObject,
    mut v___y_6507_: *mut LeanObject,
    mut v___y_6508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6509_: *mut LeanObject = core::ptr::null_mut();
    v_res_6509_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_6498_, v_xs_6499_, v_as_6500_, v_i_6501_, v_j_6502_, v_bs_6503_, v___y_6504_, v___y_6505_, v___y_6506_, v___y_6507_);
    lean_dec(v___y_6507_);
    lean_dec_ref(v___y_6506_);
    lean_dec(v___y_6505_);
    lean_dec_ref(v___y_6504_);
    lean_dec_ref(v_as_6500_);
    lean_dec_ref(v_fixedParamPerms_6498_);
    return v_res_6509_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9()
-> *mut LeanObject {
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    v___x_6524_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__8;
    v___x_6525_ = l_Lean_stringToMessageData(v___x_6524_);
    return v___x_6525_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11()
-> *mut LeanObject {
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    v___x_6527_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__10;
    v___x_6528_ = l_Lean_stringToMessageData(v___x_6527_);
    return v___x_6528_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(
    mut v_preDefs_6529_: *mut LeanObject,
    mut v_fixedParamPerms_6530_: *mut LeanObject,
    mut v_xs_6531_: *mut LeanObject,
    mut v_recArgInfos_6532_: *mut LeanObject,
    mut v_a_6533_: *mut LeanObject,
    mut v_a_6534_: *mut LeanObject,
    mut v_a_6535_: *mut LeanObject,
    mut v_a_6536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indGroupInst_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIndGroupInfo_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6552_: u8 = 0;
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: u8 = 0;
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: u8 = 0;
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6588_: u8 = 0;
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6592_: u8 = 0;
    let mut v___f_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6598_: u8 = 0;
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6602_: u8 = 0;
    let mut v___x_6603_: u8 = 0;
    let mut v_toConstantVal_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6621_: u8 = 0;
    let mut v___x_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6625_: u8 = 0;
    let mut v_reuseFailAlloc_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6630_: u8 = 0;
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6634_: u8 = 0;
    let mut v_isSharedCheck_6635_: u8 = 0;
    let mut v_unused_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6640_: u8 = 0;
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6644_: u8 = 0;
    let mut v_a_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6648_: u8 = 0;
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6538_ = lean_array_get_size(v_preDefs_6529_);
                v___x_6539_ = lean_unsigned_to_nat(0);
                v___x_6540_ = lean_mk_empty_array_with_capacity(v___x_6538_);
                lean_inc_ref(v___x_6540_);
                lean_inc_ref(v_xs_6531_);
                v___x_6541_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_6530_, v_xs_6531_, v_preDefs_6529_, v___x_6538_, v___x_6539_, v___x_6540_, v_a_6533_, v_a_6534_, v_a_6535_, v_a_6536_);
                if lean_obj_tag(v___x_6541_) == 0 {
                    v_a_6542_ = lean_ctor_get(v___x_6541_, 0);
                    lean_inc(v_a_6542_);
                    lean_dec_ref_known(v___x_6541_, 1);
                    lean_inc_ref(v_xs_6531_);
                    v___x_6543_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_6530_, v_xs_6531_, v_preDefs_6529_, v___x_6538_, v___x_6539_, v___x_6540_, v_a_6533_, v_a_6534_, v_a_6535_, v_a_6536_);
                    if lean_obj_tag(v___x_6543_) == 0 {
                        v_a_6544_ = lean_ctor_get(v___x_6543_, 0);
                        lean_inc(v_a_6544_);
                        lean_dec_ref_known(v___x_6543_, 1);
                        v___x_6545_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
                        v___x_6546_ =
                            lean_array_get_borrowed(v___x_6545_, v_recArgInfos_6532_, v___x_6539_);
                        v_indGroupInst_6547_ = lean_ctor_get(v___x_6546_, 4);
                        v_toIndGroupInfo_6548_ = lean_ctor_get(v_indGroupInst_6547_, 0);
                        lean_inc_ref(v_toIndGroupInfo_6548_);
                        v_all_6549_ = lean_ctor_get(v_toIndGroupInfo_6548_, 0);
                        v_isSharedCheck_6635_ = (!lean_is_exclusive(v_toIndGroupInfo_6548_)) as u8;
                        if v_isSharedCheck_6635_ == 0 {
                            v_unused_6636_ = lean_ctor_get(v_toIndGroupInfo_6548_, 1);
                            lean_dec(v_unused_6636_);
                            v___x_6551_ = v_toIndGroupInfo_6548_;
                            v_isShared_6552_ = v_isSharedCheck_6635_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_all_6549_);
                            lean_dec(v_toIndGroupInfo_6548_);
                            v___x_6551_ = lean_box(0);
                            v_isShared_6552_ = v_isSharedCheck_6635_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6542_);
                        lean_dec_ref(v_recArgInfos_6532_);
                        lean_dec_ref(v_xs_6531_);
                        lean_dec_ref(v_fixedParamPerms_6530_);
                        lean_dec_ref(v_preDefs_6529_);
                        v_a_6637_ = lean_ctor_get(v___x_6543_, 0);
                        v_isSharedCheck_6644_ = (!lean_is_exclusive(v___x_6543_)) as u8;
                        if v_isSharedCheck_6644_ == 0 {
                            v___x_6639_ = v___x_6543_;
                            v_isShared_6640_ = v_isSharedCheck_6644_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_6637_);
                            lean_dec(v___x_6543_);
                            v___x_6639_ = lean_box(0);
                            v_isShared_6640_ = v_isSharedCheck_6644_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_6540_);
                    lean_dec_ref(v_recArgInfos_6532_);
                    lean_dec_ref(v_xs_6531_);
                    lean_dec_ref(v_fixedParamPerms_6530_);
                    lean_dec_ref(v_preDefs_6529_);
                    v_a_6645_ = lean_ctor_get(v___x_6541_, 0);
                    v_isSharedCheck_6652_ = (!lean_is_exclusive(v___x_6541_)) as u8;
                    if v_isSharedCheck_6652_ == 0 {
                        v___x_6647_ = v___x_6541_;
                        v_isShared_6648_ = v_isSharedCheck_6652_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_6645_);
                        lean_dec(v___x_6541_);
                        v___x_6647_ = lean_box(0);
                        v_isShared_6648_ = v_isSharedCheck_6652_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6553_ = lean_box(0);
                v___x_6554_ = lean_array_get(v___x_6553_, v_all_6549_, v___x_6539_);
                lean_dec_ref(v_all_6549_);
                v___x_6555_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4(v___x_6554_, v_a_6533_, v_a_6534_, v_a_6535_, v_a_6536_);
                if lean_obj_tag(v___x_6555_) == 0 {
                    v_a_6556_ = lean_ctor_get(v___x_6555_, 0);
                    lean_inc(v_a_6556_);
                    lean_dec_ref_known(v___x_6555_, 1);
                    v___x_6557_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3;
                    v___f_6558_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__4;
                    v___x_6559_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_6557_, v_a_6533_, v_a_6534_, v_a_6535_, v_a_6536_);
                    v_a_6560_ = lean_ctor_get(v___x_6559_, 0);
                    lean_inc(v_a_6560_);
                    lean_dec_ref(v___x_6559_);
                    v___f_6561_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__5;
                    v___f_6562_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__6;
                    v___x_6563_ = l_Lean_InductiveVal_numTypeFormers(v_a_6556_);
                    v___x_6564_ = l_Array_range(v___x_6563_);
                    v___x_6565_ = l_Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5(v___f_6562_, v_recArgInfos_6532_, v___x_6564_);
                    v___x_6603_ = (lean_unbox(v_a_6560_) as u8);
                    lean_dec(v_a_6560_);
                    if v___x_6603_ == 0 {
                        lean_del_object(v___x_6551_);
                        v___y_6567_ = v_a_6533_;
                        v___y_6568_ = v_a_6534_;
                        v___y_6569_ = v_a_6535_;
                        v___y_6570_ = v_a_6536_;
                        state = 2;
                        continue;
                    } else {
                        v_toConstantVal_6604_ = lean_ctor_get(v_a_6556_, 0);
                        v_name_6605_ = lean_ctor_get(v_toConstantVal_6604_, 0);
                        v___x_6606_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__9);
                        lean_inc(v_name_6605_);
                        v___x_6607_ = l_Lean_MessageData_ofName(v_name_6605_);
                        if v_isShared_6552_ == 0 {
                            lean_ctor_set_tag(v___x_6551_, 7);
                            lean_ctor_set(v___x_6551_, 1, v___x_6607_);
                            lean_ctor_set(v___x_6551_, 0, v___x_6606_);
                            v___x_6609_ = v___x_6551_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_6626_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6626_, 0, v___x_6606_);
                            lean_ctor_set(v_reuseFailAlloc_6626_, 1, v___x_6607_);
                            v___x_6609_ = v_reuseFailAlloc_6626_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6551_);
                    lean_dec(v_a_6544_);
                    lean_dec(v_a_6542_);
                    lean_dec_ref(v_recArgInfos_6532_);
                    lean_dec_ref(v_xs_6531_);
                    lean_dec_ref(v_fixedParamPerms_6530_);
                    lean_dec_ref(v_preDefs_6529_);
                    v_a_6627_ = lean_ctor_get(v___x_6555_, 0);
                    v_isSharedCheck_6634_ = (!lean_is_exclusive(v___x_6555_)) as u8;
                    if v_isSharedCheck_6634_ == 0 {
                        v___x_6629_ = v___x_6555_;
                        v_isShared_6630_ = v_isSharedCheck_6634_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6627_);
                        lean_dec(v___x_6555_);
                        v___x_6629_ = lean_box(0);
                        v_isShared_6630_ = v_isSharedCheck_6634_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v_toConstantVal_6571_ = lean_ctor_get(v_a_6556_, 0);
                lean_inc_ref(v_toConstantVal_6571_);
                v_numIndices_6572_ = lean_ctor_get(v_a_6556_, 2);
                lean_inc(v_numIndices_6572_);
                lean_dec(v_a_6556_);
                v_name_6573_ = lean_ctor_get(v_toConstantVal_6571_, 0);
                lean_inc(v_name_6573_);
                lean_dec_ref(v_toConstantVal_6571_);
                v___x_6574_ = l_Lean_Meta_isInductivePredicate(
                    v_name_6573_,
                    v___y_6567_,
                    v___y_6568_,
                    v___y_6569_,
                    v___y_6570_,
                );
                if lean_obj_tag(v___x_6574_) == 0 {
                    v_a_6575_ = lean_ctor_get(v___x_6574_, 0);
                    lean_inc_n(v_a_6575_, 2);
                    lean_dec_ref_known(v___x_6574_, 1);
                    lean_inc(v_numIndices_6572_);
                    lean_inc_ref(v_preDefs_6529_);
                    lean_inc_ref(v_xs_6531_);
                    lean_inc_ref(v_fixedParamPerms_6530_);
                    lean_inc_ref(v___x_6565_);
                    lean_inc(v_a_6542_);
                    lean_inc_ref(v_recArgInfos_6532_);
                    v___f_6576_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2___boxed as *mut core::ffi::c_void, 19, 12);
                    lean_closure_set(v___f_6576_, 0, v___f_6558_);
                    lean_closure_set(v___f_6576_, 1, v_recArgInfos_6532_);
                    lean_closure_set(v___f_6576_, 2, v_a_6542_);
                    lean_closure_set(v___f_6576_, 3, v___x_6565_);
                    lean_closure_set(v___f_6576_, 4, v___x_6539_);
                    lean_closure_set(v___f_6576_, 5, v_fixedParamPerms_6530_);
                    lean_closure_set(v___f_6576_, 6, v_xs_6531_);
                    lean_closure_set(v___f_6576_, 7, v_preDefs_6529_);
                    lean_closure_set(v___f_6576_, 8, v_numIndices_6572_);
                    lean_closure_set(v___f_6576_, 9, v___f_6561_);
                    lean_closure_set(v___f_6576_, 10, v___x_6557_);
                    lean_closure_set(v___f_6576_, 11, v_a_6575_);
                    v___x_6577_ = (lean_unbox(v_a_6575_) as u8);
                    if v___x_6577_ == 0 {
                        lean_dec_ref(v___f_6576_);
                        v___x_6578_ = lean_array_get_size(v_recArgInfos_6532_);
                        v___x_6579_ = lean_mk_empty_array_with_capacity(v___x_6578_);
                        v___x_6580_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_6542_, v_a_6544_, v_recArgInfos_6532_, v___x_6578_, v___x_6539_, v___x_6579_, v___y_6567_, v___y_6568_, v___y_6569_, v___y_6570_);
                        lean_dec(v_a_6544_);
                        if lean_obj_tag(v___x_6580_) == 0 {
                            v_a_6581_ = lean_ctor_get(v___x_6580_, 0);
                            lean_inc(v_a_6581_);
                            lean_dec_ref_known(v___x_6580_, 1);
                            v___x_6582_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__7;
                            v___x_6583_ = (lean_unbox(v_a_6575_) as u8);
                            lean_dec(v_a_6575_);
                            v___x_6584_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__2(v___f_6558_, v_recArgInfos_6532_, v_a_6542_, v___x_6565_, v___x_6539_, v_fixedParamPerms_6530_, v_xs_6531_, v_preDefs_6529_, v_numIndices_6572_, v___f_6561_, v___x_6557_, v___x_6583_, v___x_6582_, v_a_6581_, v___y_6567_, v___y_6568_, v___y_6569_, v___y_6570_);
                            lean_dec(v_numIndices_6572_);
                            lean_dec(v_a_6542_);
                            return v___x_6584_;
                        } else {
                            lean_dec(v_a_6575_);
                            lean_dec(v_numIndices_6572_);
                            lean_dec_ref(v___x_6565_);
                            lean_dec(v_a_6542_);
                            lean_dec_ref(v_recArgInfos_6532_);
                            lean_dec_ref(v_xs_6531_);
                            lean_dec_ref(v_fixedParamPerms_6530_);
                            lean_dec_ref(v_preDefs_6529_);
                            v_a_6585_ = lean_ctor_get(v___x_6580_, 0);
                            v_isSharedCheck_6592_ = (!lean_is_exclusive(v___x_6580_)) as u8;
                            if v_isSharedCheck_6592_ == 0 {
                                v___x_6587_ = v___x_6580_;
                                v_isShared_6588_ = v_isSharedCheck_6592_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_6585_);
                                lean_dec(v___x_6580_);
                                v___x_6587_ = lean_box(0);
                                v_isShared_6588_ = v_isSharedCheck_6592_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6575_);
                        lean_dec(v_numIndices_6572_);
                        lean_dec_ref(v___x_6565_);
                        lean_dec(v_a_6544_);
                        lean_dec_ref(v_xs_6531_);
                        lean_dec_ref(v_fixedParamPerms_6530_);
                        lean_dec_ref(v_preDefs_6529_);
                        lean_inc(v_a_6542_);
                        v___f_6593_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__3___boxed as *mut core::ffi::c_void, 10, 4);
                        lean_closure_set(v___f_6593_, 0, v_recArgInfos_6532_);
                        lean_closure_set(v___f_6593_, 1, v_a_6542_);
                        lean_closure_set(v___f_6593_, 2, v___x_6539_);
                        lean_closure_set(v___f_6593_, 3, v___f_6576_);
                        v___x_6594_ = l_Lean_Elab_Structural_withFunTypes___redArg(
                            v_a_6542_,
                            v___f_6593_,
                            v___y_6567_,
                            v___y_6568_,
                            v___y_6569_,
                            v___y_6570_,
                        );
                        return v___x_6594_;
                    }
                } else {
                    lean_dec(v_numIndices_6572_);
                    lean_dec_ref(v___x_6565_);
                    lean_dec(v_a_6544_);
                    lean_dec(v_a_6542_);
                    lean_dec_ref(v_recArgInfos_6532_);
                    lean_dec_ref(v_xs_6531_);
                    lean_dec_ref(v_fixedParamPerms_6530_);
                    lean_dec_ref(v_preDefs_6529_);
                    v_a_6595_ = lean_ctor_get(v___x_6574_, 0);
                    v_isSharedCheck_6602_ = (!lean_is_exclusive(v___x_6574_)) as u8;
                    if v_isSharedCheck_6602_ == 0 {
                        v___x_6597_ = v___x_6574_;
                        v_isShared_6598_ = v_isSharedCheck_6602_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6595_);
                        lean_dec(v___x_6574_);
                        v___x_6597_ = lean_box(0);
                        v_isShared_6598_ = v_isSharedCheck_6602_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6588_ == 0 {
                    v___x_6590_ = v___x_6587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6591_, 0, v_a_6585_);
                    v___x_6590_ = v_reuseFailAlloc_6591_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6590_;
            }
            5 => {
                if v_isShared_6598_ == 0 {
                    v___x_6600_ = v___x_6597_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6601_, 0, v_a_6595_);
                    v___x_6600_ = v_reuseFailAlloc_6601_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6600_;
            }
            7 => {
                v___x_6610_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__11);
                v___x_6611_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6611_, 0, v___x_6609_);
                lean_ctor_set(v___x_6611_, 1, v___x_6610_);
                lean_inc_ref(v___x_6565_);
                v___x_6612_ = lean_array_to_list(v___x_6565_);
                v___x_6613_ = lean_box(0);
                v___x_6614_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__20(v___x_6612_, v___x_6613_);
                v___x_6615_ = l_Lean_MessageData_ofList(v___x_6614_);
                v___x_6616_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6616_, 0, v___x_6611_);
                lean_ctor_set(v___x_6616_, 1, v___x_6615_);
                v___x_6617_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_6557_, v___x_6616_, v_a_6533_, v_a_6534_, v_a_6535_, v_a_6536_);
                if lean_obj_tag(v___x_6617_) == 0 {
                    lean_dec_ref_known(v___x_6617_, 1);
                    v___y_6567_ = v_a_6533_;
                    v___y_6568_ = v_a_6534_;
                    v___y_6569_ = v_a_6535_;
                    v___y_6570_ = v_a_6536_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v___x_6565_);
                    lean_dec(v_a_6556_);
                    lean_dec(v_a_6544_);
                    lean_dec(v_a_6542_);
                    lean_dec_ref(v_recArgInfos_6532_);
                    lean_dec_ref(v_xs_6531_);
                    lean_dec_ref(v_fixedParamPerms_6530_);
                    lean_dec_ref(v_preDefs_6529_);
                    v_a_6618_ = lean_ctor_get(v___x_6617_, 0);
                    v_isSharedCheck_6625_ = (!lean_is_exclusive(v___x_6617_)) as u8;
                    if v_isSharedCheck_6625_ == 0 {
                        v___x_6620_ = v___x_6617_;
                        v_isShared_6621_ = v_isSharedCheck_6625_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6618_);
                        lean_dec(v___x_6617_);
                        v___x_6620_ = lean_box(0);
                        v_isShared_6621_ = v_isSharedCheck_6625_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_6621_ == 0 {
                    v___x_6623_ = v___x_6620_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6624_, 0, v_a_6618_);
                    v___x_6623_ = v_reuseFailAlloc_6624_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6623_;
            }
            10 => {
                if v_isShared_6630_ == 0 {
                    v___x_6632_ = v___x_6629_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6633_, 0, v_a_6627_);
                    v___x_6632_ = v_reuseFailAlloc_6633_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6632_;
            }
            12 => {
                if v_isShared_6640_ == 0 {
                    v___x_6642_ = v___x_6639_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6643_, 0, v_a_6637_);
                    v___x_6642_ = v_reuseFailAlloc_6643_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6642_;
            }
            14 => {
                if v_isShared_6648_ == 0 {
                    v___x_6650_ = v___x_6647_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6651_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6651_, 0, v_a_6645_);
                    v___x_6650_ = v_reuseFailAlloc_6651_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(
    mut v_preDefs_6653_: *mut LeanObject,
    mut v_fixedParamPerms_6654_: *mut LeanObject,
    mut v_xs_6655_: *mut LeanObject,
    mut v_recArgInfos_6656_: *mut LeanObject,
    mut v_a_6657_: *mut LeanObject,
    mut v_a_6658_: *mut LeanObject,
    mut v_a_6659_: *mut LeanObject,
    mut v_a_6660_: *mut LeanObject,
    mut v_a_6661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6662_: *mut LeanObject = core::ptr::null_mut();
    v_res_6662_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_preDefs_6653_, v_fixedParamPerms_6654_, v_xs_6655_, v_recArgInfos_6656_, v_a_6657_, v_a_6658_, v_a_6659_, v_a_6660_);
    lean_dec(v_a_6660_);
    lean_dec_ref(v_a_6659_);
    lean_dec(v_a_6658_);
    lean_dec_ref(v_a_6657_);
    return v_res_6662_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(
    mut v_fixedParamPerms_6663_: *mut LeanObject,
    mut v_xs_6664_: *mut LeanObject,
    mut v_as_6665_: *mut LeanObject,
    mut v_i_6666_: *mut LeanObject,
    mut v_j_6667_: *mut LeanObject,
    mut v_inv_6668_: *mut LeanObject,
    mut v_bs_6669_: *mut LeanObject,
    mut v___y_6670_: *mut LeanObject,
    mut v___y_6671_: *mut LeanObject,
    mut v___y_6672_: *mut LeanObject,
    mut v___y_6673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    v___x_6675_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___redArg(v_fixedParamPerms_6663_, v_xs_6664_, v_as_6665_, v_i_6666_, v_j_6667_, v_bs_6669_, v___y_6670_, v___y_6671_, v___y_6672_, v___y_6673_);
    return v___x_6675_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2___boxed(
    mut v_fixedParamPerms_6676_: *mut LeanObject,
    mut v_xs_6677_: *mut LeanObject,
    mut v_as_6678_: *mut LeanObject,
    mut v_i_6679_: *mut LeanObject,
    mut v_j_6680_: *mut LeanObject,
    mut v_inv_6681_: *mut LeanObject,
    mut v_bs_6682_: *mut LeanObject,
    mut v___y_6683_: *mut LeanObject,
    mut v___y_6684_: *mut LeanObject,
    mut v___y_6685_: *mut LeanObject,
    mut v___y_6686_: *mut LeanObject,
    mut v___y_6687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6688_: *mut LeanObject = core::ptr::null_mut();
    v_res_6688_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__2(v_fixedParamPerms_6676_, v_xs_6677_, v_as_6678_, v_i_6679_, v_j_6680_, v_inv_6681_, v_bs_6682_, v___y_6683_, v___y_6684_, v___y_6685_, v___y_6686_);
    lean_dec(v___y_6686_);
    lean_dec_ref(v___y_6685_);
    lean_dec(v___y_6684_);
    lean_dec_ref(v___y_6683_);
    lean_dec_ref(v_as_6678_);
    lean_dec_ref(v_fixedParamPerms_6676_);
    return v_res_6688_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(
    mut v_fixedParamPerms_6689_: *mut LeanObject,
    mut v_xs_6690_: *mut LeanObject,
    mut v_as_6691_: *mut LeanObject,
    mut v_i_6692_: *mut LeanObject,
    mut v_j_6693_: *mut LeanObject,
    mut v_inv_6694_: *mut LeanObject,
    mut v_bs_6695_: *mut LeanObject,
    mut v___y_6696_: *mut LeanObject,
    mut v___y_6697_: *mut LeanObject,
    mut v___y_6698_: *mut LeanObject,
    mut v___y_6699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    v___x_6701_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___redArg(v_fixedParamPerms_6689_, v_xs_6690_, v_as_6691_, v_i_6692_, v_j_6693_, v_bs_6695_, v___y_6696_, v___y_6697_, v___y_6698_, v___y_6699_);
    return v___x_6701_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3___boxed(
    mut v_fixedParamPerms_6702_: *mut LeanObject,
    mut v_xs_6703_: *mut LeanObject,
    mut v_as_6704_: *mut LeanObject,
    mut v_i_6705_: *mut LeanObject,
    mut v_j_6706_: *mut LeanObject,
    mut v_inv_6707_: *mut LeanObject,
    mut v_bs_6708_: *mut LeanObject,
    mut v___y_6709_: *mut LeanObject,
    mut v___y_6710_: *mut LeanObject,
    mut v___y_6711_: *mut LeanObject,
    mut v___y_6712_: *mut LeanObject,
    mut v___y_6713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6714_: *mut LeanObject = core::ptr::null_mut();
    v_res_6714_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__3(v_fixedParamPerms_6702_, v_xs_6703_, v_as_6704_, v_i_6705_, v_j_6706_, v_inv_6707_, v_bs_6708_, v___y_6709_, v___y_6710_, v___y_6711_, v___y_6712_);
    lean_dec(v___y_6712_);
    lean_dec_ref(v___y_6711_);
    lean_dec(v___y_6710_);
    lean_dec_ref(v___y_6709_);
    lean_dec_ref(v_as_6704_);
    lean_dec_ref(v_fixedParamPerms_6702_);
    return v_res_6714_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(
    mut v_00_u03b3_6715_: *mut LeanObject,
    mut v_msg_6716_: *mut LeanObject,
    mut v___y_6717_: *mut LeanObject,
    mut v___y_6718_: *mut LeanObject,
    mut v___y_6719_: *mut LeanObject,
    mut v___y_6720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    v___x_6722_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___redArg(v_msg_6716_, v___y_6717_, v___y_6718_, v___y_6719_, v___y_6720_);
    return v___x_6722_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14___boxed(
    mut v_00_u03b3_6723_: *mut LeanObject,
    mut v_msg_6724_: *mut LeanObject,
    mut v___y_6725_: *mut LeanObject,
    mut v___y_6726_: *mut LeanObject,
    mut v___y_6727_: *mut LeanObject,
    mut v___y_6728_: *mut LeanObject,
    mut v___y_6729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6730_: *mut LeanObject = core::ptr::null_mut();
    v_res_6730_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__14(v_00_u03b3_6723_, v_msg_6724_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_);
    lean_dec(v___y_6728_);
    lean_dec_ref(v___y_6727_);
    lean_dec(v___y_6726_);
    lean_dec_ref(v___y_6725_);
    return v_res_6730_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(
    mut v_00_u03b3_6731_: *mut LeanObject,
    mut v_00_u03b1_6732_: *mut LeanObject,
    mut v_f_6733_: *mut LeanObject,
    mut v_positions_6734_: *mut LeanObject,
    mut v_ys_6735_: *mut LeanObject,
    mut v_xs_6736_: *mut LeanObject,
    mut v___y_6737_: *mut LeanObject,
    mut v___y_6738_: *mut LeanObject,
    mut v___y_6739_: *mut LeanObject,
    mut v___y_6740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
    v___x_6742_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___redArg(v_f_6733_, v_positions_6734_, v_ys_6735_, v_xs_6736_, v___y_6737_, v___y_6738_, v___y_6739_, v___y_6740_);
    return v___x_6742_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6___boxed(
    mut v_00_u03b3_6743_: *mut LeanObject,
    mut v_00_u03b1_6744_: *mut LeanObject,
    mut v_f_6745_: *mut LeanObject,
    mut v_positions_6746_: *mut LeanObject,
    mut v_ys_6747_: *mut LeanObject,
    mut v_xs_6748_: *mut LeanObject,
    mut v___y_6749_: *mut LeanObject,
    mut v___y_6750_: *mut LeanObject,
    mut v___y_6751_: *mut LeanObject,
    mut v___y_6752_: *mut LeanObject,
    mut v___y_6753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6754_: *mut LeanObject = core::ptr::null_mut();
    v_res_6754_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6(v_00_u03b3_6743_, v_00_u03b1_6744_, v_f_6745_, v_positions_6746_, v_ys_6747_, v_xs_6748_, v___y_6749_, v___y_6750_, v___y_6751_, v___y_6752_);
    lean_dec(v___y_6752_);
    lean_dec_ref(v___y_6751_);
    lean_dec(v___y_6750_);
    lean_dec_ref(v___y_6749_);
    lean_dec_ref(v_xs_6748_);
    lean_dec_ref(v_ys_6747_);
    lean_dec_ref(v_positions_6746_);
    return v_res_6754_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(
    mut v___x_6755_: *mut LeanObject,
    mut v_a_6756_: *mut LeanObject,
    mut v_a_6757_: *mut LeanObject,
    mut v_funTypes_6758_: *mut LeanObject,
    mut v_as_6759_: *mut LeanObject,
    mut v_i_6760_: *mut LeanObject,
    mut v_j_6761_: *mut LeanObject,
    mut v_inv_6762_: *mut LeanObject,
    mut v_bs_6763_: *mut LeanObject,
    mut v___y_6764_: *mut LeanObject,
    mut v___y_6765_: *mut LeanObject,
    mut v___y_6766_: *mut LeanObject,
    mut v___y_6767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6769_: *mut LeanObject = core::ptr::null_mut();
    v___x_6769_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___redArg(v___x_6755_, v_a_6756_, v_a_6757_, v_funTypes_6758_, v_as_6759_, v_i_6760_, v_j_6761_, v_bs_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_);
    return v___x_6769_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7___boxed(
    mut v___x_6770_: *mut LeanObject,
    mut v_a_6771_: *mut LeanObject,
    mut v_a_6772_: *mut LeanObject,
    mut v_funTypes_6773_: *mut LeanObject,
    mut v_as_6774_: *mut LeanObject,
    mut v_i_6775_: *mut LeanObject,
    mut v_j_6776_: *mut LeanObject,
    mut v_inv_6777_: *mut LeanObject,
    mut v_bs_6778_: *mut LeanObject,
    mut v___y_6779_: *mut LeanObject,
    mut v___y_6780_: *mut LeanObject,
    mut v___y_6781_: *mut LeanObject,
    mut v___y_6782_: *mut LeanObject,
    mut v___y_6783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6784_: *mut LeanObject = core::ptr::null_mut();
    v_res_6784_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__7(v___x_6770_, v_a_6771_, v_a_6772_, v_funTypes_6773_, v_as_6774_, v_i_6775_, v_j_6776_, v_inv_6777_, v_bs_6778_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_);
    lean_dec(v___y_6782_);
    lean_dec_ref(v___y_6781_);
    lean_dec(v___y_6780_);
    lean_dec_ref(v___y_6779_);
    lean_dec_ref(v_as_6774_);
    return v_res_6784_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(
    mut v_fixedParamPerms_6785_: *mut LeanObject,
    mut v_xs_6786_: *mut LeanObject,
    mut v_as_6787_: *mut LeanObject,
    mut v_i_6788_: *mut LeanObject,
    mut v_j_6789_: *mut LeanObject,
    mut v_inv_6790_: *mut LeanObject,
    mut v_bs_6791_: *mut LeanObject,
    mut v___y_6792_: *mut LeanObject,
    mut v___y_6793_: *mut LeanObject,
    mut v___y_6794_: *mut LeanObject,
    mut v___y_6795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6797_: *mut LeanObject = core::ptr::null_mut();
    v___x_6797_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg(v_fixedParamPerms_6785_, v_xs_6786_, v_as_6787_, v_i_6788_, v_j_6789_, v_bs_6791_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_);
    return v___x_6797_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___boxed(
    mut v_fixedParamPerms_6798_: *mut LeanObject,
    mut v_xs_6799_: *mut LeanObject,
    mut v_as_6800_: *mut LeanObject,
    mut v_i_6801_: *mut LeanObject,
    mut v_j_6802_: *mut LeanObject,
    mut v_inv_6803_: *mut LeanObject,
    mut v_bs_6804_: *mut LeanObject,
    mut v___y_6805_: *mut LeanObject,
    mut v___y_6806_: *mut LeanObject,
    mut v___y_6807_: *mut LeanObject,
    mut v___y_6808_: *mut LeanObject,
    mut v___y_6809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6810_: *mut LeanObject = core::ptr::null_mut();
    v_res_6810_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8(v_fixedParamPerms_6798_, v_xs_6799_, v_as_6800_, v_i_6801_, v_j_6802_, v_inv_6803_, v_bs_6804_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_);
    lean_dec(v___y_6808_);
    lean_dec_ref(v___y_6807_);
    lean_dec(v___y_6806_);
    lean_dec_ref(v___y_6805_);
    lean_dec_ref(v_as_6800_);
    return v_res_6810_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(
    mut v_00_u03b1_6811_: *mut LeanObject,
    mut v_preDefs_6812_: *mut LeanObject,
    mut v_k_6813_: *mut LeanObject,
    mut v___y_6814_: *mut LeanObject,
    mut v___y_6815_: *mut LeanObject,
    mut v___y_6816_: *mut LeanObject,
    mut v___y_6817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6819_: *mut LeanObject = core::ptr::null_mut();
    v___x_6819_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_6812_, v_k_6813_, v___y_6814_, v___y_6815_, v___y_6816_, v___y_6817_);
    return v___x_6819_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___boxed(
    mut v_00_u03b1_6820_: *mut LeanObject,
    mut v_preDefs_6821_: *mut LeanObject,
    mut v_k_6822_: *mut LeanObject,
    mut v___y_6823_: *mut LeanObject,
    mut v___y_6824_: *mut LeanObject,
    mut v___y_6825_: *mut LeanObject,
    mut v___y_6826_: *mut LeanObject,
    mut v___y_6827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6828_: *mut LeanObject = core::ptr::null_mut();
    v_res_6828_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12(v_00_u03b1_6820_, v_preDefs_6821_, v_k_6822_, v___y_6823_, v___y_6824_, v___y_6825_, v___y_6826_);
    lean_dec(v___y_6826_);
    lean_dec_ref(v___y_6825_);
    lean_dec(v___y_6824_);
    lean_dec_ref(v___y_6823_);
    return v_res_6828_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(
    mut v_a_6829_: u8,
    mut v_a_6830_: *mut LeanObject,
    mut v_a_6831_: *mut LeanObject,
    mut v_recArgInfos_6832_: *mut LeanObject,
    mut v___x_6833_: *mut LeanObject,
    mut v_preDefs_6834_: *mut LeanObject,
    mut v_a_6835_: *mut LeanObject,
    mut v_as_6836_: *mut LeanObject,
    mut v_i_6837_: *mut LeanObject,
    mut v_j_6838_: *mut LeanObject,
    mut v_inv_6839_: *mut LeanObject,
    mut v_bs_6840_: *mut LeanObject,
    mut v___y_6841_: *mut LeanObject,
    mut v___y_6842_: *mut LeanObject,
    mut v___y_6843_: *mut LeanObject,
    mut v___y_6844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6846_: *mut LeanObject = core::ptr::null_mut();
    v___x_6846_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___redArg(v_a_6829_, v_a_6830_, v_a_6831_, v_recArgInfos_6832_, v___x_6833_, v_preDefs_6834_, v_a_6835_, v_as_6836_, v_i_6837_, v_j_6838_, v_bs_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_);
    return v___x_6846_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6847_: *mut LeanObject = *_args.add(0);
    let mut v_a_6848_: *mut LeanObject = *_args.add(1);
    let mut v_a_6849_: *mut LeanObject = *_args.add(2);
    let mut v_recArgInfos_6850_: *mut LeanObject = *_args.add(3);
    let mut v___x_6851_: *mut LeanObject = *_args.add(4);
    let mut v_preDefs_6852_: *mut LeanObject = *_args.add(5);
    let mut v_a_6853_: *mut LeanObject = *_args.add(6);
    let mut v_as_6854_: *mut LeanObject = *_args.add(7);
    let mut v_i_6855_: *mut LeanObject = *_args.add(8);
    let mut v_j_6856_: *mut LeanObject = *_args.add(9);
    let mut v_inv_6857_: *mut LeanObject = *_args.add(10);
    let mut v_bs_6858_: *mut LeanObject = *_args.add(11);
    let mut v___y_6859_: *mut LeanObject = *_args.add(12);
    let mut v___y_6860_: *mut LeanObject = *_args.add(13);
    let mut v___y_6861_: *mut LeanObject = *_args.add(14);
    let mut v___y_6862_: *mut LeanObject = *_args.add(15);
    let mut v___y_6863_: *mut LeanObject = *_args.add(16);
    let mut v_a_30507__boxed_6864_: u8 = 0;
    let mut v_res_6865_: *mut LeanObject = core::ptr::null_mut();
    v_a_30507__boxed_6864_ = (lean_unbox(v_a_6847_) as u8);
    v_res_6865_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__14(v_a_30507__boxed_6864_, v_a_6848_, v_a_6849_, v_recArgInfos_6850_, v___x_6851_, v_preDefs_6852_, v_a_6853_, v_as_6854_, v_i_6855_, v_j_6856_, v_inv_6857_, v_bs_6858_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_);
    lean_dec(v___y_6862_);
    lean_dec_ref(v___y_6861_);
    lean_dec(v___y_6860_);
    lean_dec_ref(v___y_6859_);
    lean_dec_ref(v_as_6854_);
    lean_dec_ref(v_a_6849_);
    lean_dec_ref(v_a_6848_);
    return v_res_6865_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(
    mut v_declName_6866_: *mut LeanObject,
    mut v_s_6867_: u8,
    mut v___y_6868_: *mut LeanObject,
    mut v___y_6869_: *mut LeanObject,
    mut v___y_6870_: *mut LeanObject,
    mut v___y_6871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    v___x_6873_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___redArg(v_declName_6866_, v_s_6867_, v___y_6869_, v___y_6871_);
    return v___x_6873_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29___boxed(
    mut v_declName_6874_: *mut LeanObject,
    mut v_s_6875_: *mut LeanObject,
    mut v___y_6876_: *mut LeanObject,
    mut v___y_6877_: *mut LeanObject,
    mut v___y_6878_: *mut LeanObject,
    mut v___y_6879_: *mut LeanObject,
    mut v___y_6880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_6881_: u8 = 0;
    let mut v_res_6882_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_6881_ = (lean_unbox(v_s_6875_) as u8);
    v_res_6882_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__16_spec__29(v_declName_6874_, v_s_boxed_6881_, v___y_6876_, v___y_6877_, v___y_6878_, v___y_6879_);
    lean_dec(v___y_6879_);
    lean_dec_ref(v___y_6878_);
    lean_dec(v___y_6877_);
    lean_dec_ref(v___y_6876_);
    return v_res_6882_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(
    mut v_xs_6883_: *mut LeanObject,
    mut v_a_6884_: u8,
    mut v_preDefs_6885_: *mut LeanObject,
    mut v___x_6886_: *mut LeanObject,
    mut v_as_6887_: *mut LeanObject,
    mut v_i_6888_: *mut LeanObject,
    mut v_j_6889_: *mut LeanObject,
    mut v_inv_6890_: *mut LeanObject,
    mut v_bs_6891_: *mut LeanObject,
    mut v___y_6892_: *mut LeanObject,
    mut v___y_6893_: *mut LeanObject,
    mut v___y_6894_: *mut LeanObject,
    mut v___y_6895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6897_: *mut LeanObject = core::ptr::null_mut();
    v___x_6897_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___redArg(v_xs_6883_, v_a_6884_, v_preDefs_6885_, v___x_6886_, v_as_6887_, v_i_6888_, v_j_6889_, v_bs_6891_, v___y_6892_, v___y_6893_, v___y_6894_, v___y_6895_);
    return v___x_6897_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17___boxed(
    mut v_xs_6898_: *mut LeanObject,
    mut v_a_6899_: *mut LeanObject,
    mut v_preDefs_6900_: *mut LeanObject,
    mut v___x_6901_: *mut LeanObject,
    mut v_as_6902_: *mut LeanObject,
    mut v_i_6903_: *mut LeanObject,
    mut v_j_6904_: *mut LeanObject,
    mut v_inv_6905_: *mut LeanObject,
    mut v_bs_6906_: *mut LeanObject,
    mut v___y_6907_: *mut LeanObject,
    mut v___y_6908_: *mut LeanObject,
    mut v___y_6909_: *mut LeanObject,
    mut v___y_6910_: *mut LeanObject,
    mut v___y_6911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_30556__boxed_6912_: u8 = 0;
    let mut v_res_6913_: *mut LeanObject = core::ptr::null_mut();
    v_a_30556__boxed_6912_ = (lean_unbox(v_a_6899_) as u8);
    v_res_6913_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__17(v_xs_6898_, v_a_30556__boxed_6912_, v_preDefs_6900_, v___x_6901_, v_as_6902_, v_i_6903_, v_j_6904_, v_inv_6905_, v_bs_6906_, v___y_6907_, v___y_6908_, v___y_6909_, v___y_6910_);
    lean_dec(v___y_6910_);
    lean_dec_ref(v___y_6909_);
    lean_dec(v___y_6908_);
    lean_dec_ref(v___y_6907_);
    lean_dec_ref(v_as_6902_);
    lean_dec_ref(v_preDefs_6900_);
    lean_dec_ref(v_xs_6898_);
    return v_res_6913_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(
    mut v_a_6914_: *mut LeanObject,
    mut v_funTypes_6915_: *mut LeanObject,
    mut v_as_6916_: *mut LeanObject,
    mut v_i_6917_: *mut LeanObject,
    mut v_j_6918_: *mut LeanObject,
    mut v_inv_6919_: *mut LeanObject,
    mut v_bs_6920_: *mut LeanObject,
    mut v___y_6921_: *mut LeanObject,
    mut v___y_6922_: *mut LeanObject,
    mut v___y_6923_: *mut LeanObject,
    mut v___y_6924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    v___x_6926_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___redArg(v_a_6914_, v_funTypes_6915_, v_as_6916_, v_i_6917_, v_j_6918_, v_bs_6920_, v___y_6921_, v___y_6922_, v___y_6923_, v___y_6924_);
    return v___x_6926_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18___boxed(
    mut v_a_6927_: *mut LeanObject,
    mut v_funTypes_6928_: *mut LeanObject,
    mut v_as_6929_: *mut LeanObject,
    mut v_i_6930_: *mut LeanObject,
    mut v_j_6931_: *mut LeanObject,
    mut v_inv_6932_: *mut LeanObject,
    mut v_bs_6933_: *mut LeanObject,
    mut v___y_6934_: *mut LeanObject,
    mut v___y_6935_: *mut LeanObject,
    mut v___y_6936_: *mut LeanObject,
    mut v___y_6937_: *mut LeanObject,
    mut v___y_6938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6939_: *mut LeanObject = core::ptr::null_mut();
    v_res_6939_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__18(v_a_6927_, v_funTypes_6928_, v_as_6929_, v_i_6930_, v_j_6931_, v_inv_6932_, v_bs_6933_, v___y_6934_, v___y_6935_, v___y_6936_, v___y_6937_);
    lean_dec(v___y_6937_);
    lean_dec_ref(v___y_6936_);
    lean_dec(v___y_6935_);
    lean_dec_ref(v___y_6934_);
    lean_dec_ref(v_as_6929_);
    lean_dec_ref(v_funTypes_6928_);
    lean_dec_ref(v_a_6927_);
    return v_res_6939_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(
    mut v_a_6940_: *mut LeanObject,
    mut v_a_6941_: *mut LeanObject,
    mut v_as_6942_: *mut LeanObject,
    mut v_i_6943_: *mut LeanObject,
    mut v_j_6944_: *mut LeanObject,
    mut v_inv_6945_: *mut LeanObject,
    mut v_bs_6946_: *mut LeanObject,
    mut v___y_6947_: *mut LeanObject,
    mut v___y_6948_: *mut LeanObject,
    mut v___y_6949_: *mut LeanObject,
    mut v___y_6950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    v___x_6952_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___redArg(v_a_6940_, v_a_6941_, v_as_6942_, v_i_6943_, v_j_6944_, v_bs_6946_, v___y_6947_, v___y_6948_, v___y_6949_, v___y_6950_);
    return v___x_6952_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19___boxed(
    mut v_a_6953_: *mut LeanObject,
    mut v_a_6954_: *mut LeanObject,
    mut v_as_6955_: *mut LeanObject,
    mut v_i_6956_: *mut LeanObject,
    mut v_j_6957_: *mut LeanObject,
    mut v_inv_6958_: *mut LeanObject,
    mut v_bs_6959_: *mut LeanObject,
    mut v___y_6960_: *mut LeanObject,
    mut v___y_6961_: *mut LeanObject,
    mut v___y_6962_: *mut LeanObject,
    mut v___y_6963_: *mut LeanObject,
    mut v___y_6964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6965_: *mut LeanObject = core::ptr::null_mut();
    v_res_6965_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__19(v_a_6953_, v_a_6954_, v_as_6955_, v_i_6956_, v_j_6957_, v_inv_6958_, v_bs_6959_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_);
    lean_dec(v___y_6963_);
    lean_dec_ref(v___y_6962_);
    lean_dec(v___y_6961_);
    lean_dec_ref(v___y_6960_);
    lean_dec_ref(v_as_6955_);
    lean_dec_ref(v_a_6954_);
    lean_dec_ref(v_a_6953_);
    return v_res_6965_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(
    mut v_00_u03b1_6966_: *mut LeanObject,
    mut v_msg_6967_: *mut LeanObject,
    mut v___y_6968_: *mut LeanObject,
    mut v___y_6969_: *mut LeanObject,
    mut v___y_6970_: *mut LeanObject,
    mut v___y_6971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    v___x_6973_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v_msg_6967_, v___y_6968_, v___y_6969_, v___y_6970_, v___y_6971_);
    return v___x_6973_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___boxed(
    mut v_00_u03b1_6974_: *mut LeanObject,
    mut v_msg_6975_: *mut LeanObject,
    mut v___y_6976_: *mut LeanObject,
    mut v___y_6977_: *mut LeanObject,
    mut v___y_6978_: *mut LeanObject,
    mut v___y_6979_: *mut LeanObject,
    mut v___y_6980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6981_: *mut LeanObject = core::ptr::null_mut();
    v_res_6981_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4(v_00_u03b1_6974_, v_msg_6975_, v___y_6976_, v___y_6977_, v___y_6978_, v___y_6979_);
    lean_dec(v___y_6979_);
    lean_dec_ref(v___y_6978_);
    lean_dec(v___y_6977_);
    lean_dec_ref(v___y_6976_);
    return v_res_6981_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(
    mut v_xs_6982_: *mut LeanObject,
    mut v_ys_6983_: *mut LeanObject,
    mut v_hsz_6984_: *mut LeanObject,
    mut v_x_6985_: *mut LeanObject,
    mut v_x_6986_: *mut LeanObject,
) -> u8 {
    let mut v___x_6987_: u8 = 0;
    v___x_6987_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___redArg(v_xs_6982_, v_ys_6983_, v_x_6985_);
    return v___x_6987_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9___boxed(
    mut v_xs_6988_: *mut LeanObject,
    mut v_ys_6989_: *mut LeanObject,
    mut v_hsz_6990_: *mut LeanObject,
    mut v_x_6991_: *mut LeanObject,
    mut v_x_6992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6993_: u8 = 0;
    let mut v_r_6994_: *mut LeanObject = core::ptr::null_mut();
    v_res_6993_ = l_Array_isEqvAux___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__9(v_xs_6988_, v_ys_6989_, v_hsz_6990_, v_x_6991_, v_x_6992_);
    lean_dec_ref(v_ys_6989_);
    lean_dec_ref(v_xs_6988_);
    v_r_6994_ = lean_box((v_res_6993_) as usize);
    return v_r_6994_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(
    mut v_n_6995_: *mut LeanObject,
    mut v_as_6996_: *mut LeanObject,
    mut v_lo_6997_: *mut LeanObject,
    mut v_hi_6998_: *mut LeanObject,
    mut v_w_6999_: *mut LeanObject,
    mut v_hlo_7000_: *mut LeanObject,
    mut v_hhi_7001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    v___x_7002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___redArg(v_n_6995_, v_as_6996_, v_lo_6997_, v_hi_6998_);
    return v___x_7002_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10___boxed(
    mut v_n_7003_: *mut LeanObject,
    mut v_as_7004_: *mut LeanObject,
    mut v_lo_7005_: *mut LeanObject,
    mut v_hi_7006_: *mut LeanObject,
    mut v_w_7007_: *mut LeanObject,
    mut v_hlo_7008_: *mut LeanObject,
    mut v_hhi_7009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7010_: *mut LeanObject = core::ptr::null_mut();
    v_res_7010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10(v_n_7003_, v_as_7004_, v_lo_7005_, v_hi_7006_, v_w_7007_, v_hlo_7008_, v_hhi_7009_);
    lean_dec(v_hi_7006_);
    lean_dec(v_n_7003_);
    return v_res_7010_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(
    mut v_00_u03b1_7011_: *mut LeanObject,
    mut v_00_u03b3_7012_: *mut LeanObject,
    mut v_xs_7013_: *mut LeanObject,
    mut v_f_7014_: *mut LeanObject,
    mut v_as_7015_: *mut LeanObject,
    mut v_bs_7016_: *mut LeanObject,
    mut v_i_7017_: *mut LeanObject,
    mut v_cs_7018_: *mut LeanObject,
    mut v___y_7019_: *mut LeanObject,
    mut v___y_7020_: *mut LeanObject,
    mut v___y_7021_: *mut LeanObject,
    mut v___y_7022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7024_: *mut LeanObject = core::ptr::null_mut();
    v___x_7024_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___redArg(v_xs_7013_, v_f_7014_, v_as_7015_, v_bs_7016_, v_i_7017_, v_cs_7018_, v___y_7019_, v___y_7020_, v___y_7021_, v___y_7022_);
    return v___x_7024_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15___boxed(
    mut v_00_u03b1_7025_: *mut LeanObject,
    mut v_00_u03b3_7026_: *mut LeanObject,
    mut v_xs_7027_: *mut LeanObject,
    mut v_f_7028_: *mut LeanObject,
    mut v_as_7029_: *mut LeanObject,
    mut v_bs_7030_: *mut LeanObject,
    mut v_i_7031_: *mut LeanObject,
    mut v_cs_7032_: *mut LeanObject,
    mut v___y_7033_: *mut LeanObject,
    mut v___y_7034_: *mut LeanObject,
    mut v___y_7035_: *mut LeanObject,
    mut v___y_7036_: *mut LeanObject,
    mut v___y_7037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7038_: *mut LeanObject = core::ptr::null_mut();
    v_res_7038_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__6_spec__15(v_00_u03b1_7025_, v_00_u03b3_7026_, v_xs_7027_, v_f_7028_, v_as_7029_, v_bs_7030_, v_i_7031_, v_cs_7032_, v___y_7033_, v___y_7034_, v___y_7035_, v___y_7036_);
    lean_dec(v___y_7036_);
    lean_dec_ref(v___y_7035_);
    lean_dec(v___y_7034_);
    lean_dec_ref(v___y_7033_);
    lean_dec_ref(v_bs_7030_);
    lean_dec_ref(v_as_7029_);
    lean_dec_ref(v_xs_7027_);
    return v_res_7038_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(
    mut v_env_7039_: *mut LeanObject,
    mut v___y_7040_: *mut LeanObject,
    mut v___y_7041_: *mut LeanObject,
    mut v___y_7042_: *mut LeanObject,
    mut v___y_7043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    v___x_7045_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___redArg(v_env_7039_, v___y_7041_, v___y_7043_);
    return v___x_7045_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25___boxed(
    mut v_env_7046_: *mut LeanObject,
    mut v___y_7047_: *mut LeanObject,
    mut v___y_7048_: *mut LeanObject,
    mut v___y_7049_: *mut LeanObject,
    mut v___y_7050_: *mut LeanObject,
    mut v___y_7051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7052_: *mut LeanObject = core::ptr::null_mut();
    v_res_7052_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23_spec__25(v_env_7046_, v___y_7047_, v___y_7048_, v___y_7049_, v___y_7050_);
    lean_dec(v___y_7050_);
    lean_dec_ref(v___y_7049_);
    lean_dec(v___y_7048_);
    lean_dec_ref(v___y_7047_);
    return v_res_7052_;
}
pub unsafe fn l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(
    mut v_00_u03b1_7053_: *mut LeanObject,
    mut v_env_7054_: *mut LeanObject,
    mut v_x_7055_: *mut LeanObject,
    mut v___y_7056_: *mut LeanObject,
    mut v___y_7057_: *mut LeanObject,
    mut v___y_7058_: *mut LeanObject,
    mut v___y_7059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    v___x_7061_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___redArg(v_env_7054_, v_x_7055_, v___y_7056_, v___y_7057_, v___y_7058_, v___y_7059_);
    return v___x_7061_;
}
pub unsafe fn l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23___boxed(
    mut v_00_u03b1_7062_: *mut LeanObject,
    mut v_env_7063_: *mut LeanObject,
    mut v_x_7064_: *mut LeanObject,
    mut v___y_7065_: *mut LeanObject,
    mut v___y_7066_: *mut LeanObject,
    mut v___y_7067_: *mut LeanObject,
    mut v___y_7068_: *mut LeanObject,
    mut v___y_7069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7070_: *mut LeanObject = core::ptr::null_mut();
    v_res_7070_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12_spec__23(v_00_u03b1_7062_, v_env_7063_, v_x_7064_, v___y_7065_, v___y_7066_, v___y_7067_, v___y_7068_);
    lean_dec(v___y_7068_);
    lean_dec_ref(v___y_7067_);
    lean_dec(v___y_7066_);
    lean_dec_ref(v___y_7065_);
    return v_res_7070_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(
    mut v_n_7071_: *mut LeanObject,
    mut v_lo_7072_: *mut LeanObject,
    mut v_hi_7073_: *mut LeanObject,
    mut v_hhi_7074_: *mut LeanObject,
    mut v_pivot_7075_: *mut LeanObject,
    mut v_as_7076_: *mut LeanObject,
    mut v_i_7077_: *mut LeanObject,
    mut v_k_7078_: *mut LeanObject,
    mut v_ilo_7079_: *mut LeanObject,
    mut v_ik_7080_: *mut LeanObject,
    mut v_w_7081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7082_: *mut LeanObject = core::ptr::null_mut();
    v___x_7082_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___redArg(v_hi_7073_, v_pivot_7075_, v_as_7076_, v_i_7077_, v_k_7078_);
    return v___x_7082_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11___boxed(
    mut v_n_7083_: *mut LeanObject,
    mut v_lo_7084_: *mut LeanObject,
    mut v_hi_7085_: *mut LeanObject,
    mut v_hhi_7086_: *mut LeanObject,
    mut v_pivot_7087_: *mut LeanObject,
    mut v_as_7088_: *mut LeanObject,
    mut v_i_7089_: *mut LeanObject,
    mut v_k_7090_: *mut LeanObject,
    mut v_ilo_7091_: *mut LeanObject,
    mut v_ik_7092_: *mut LeanObject,
    mut v_w_7093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7094_: *mut LeanObject = core::ptr::null_mut();
    v_res_7094_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Structural_Positions_groupAndSort___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__5_spec__10_spec__11(v_n_7083_, v_lo_7084_, v_hi_7085_, v_hhi_7086_, v_pivot_7087_, v_as_7088_, v_i_7089_, v_k_7090_, v_ilo_7091_, v_ik_7092_, v_w_7093_);
    lean_dec(v_pivot_7087_);
    lean_dec(v_hi_7085_);
    lean_dec(v_lo_7084_);
    lean_dec(v_n_7083_);
    return v_res_7094_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(
    mut v_x_7095_: *mut LeanObject,
) -> u8 {
    let mut v___x_7096_: u8 = 0;
    v___x_7096_ = 0;
    return v___x_7096_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0___boxed(
    mut v_x_7097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7098_: u8 = 0;
    let mut v_r_7099_: *mut LeanObject = core::ptr::null_mut();
    v_res_7098_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__0(v_x_7097_);
    lean_dec(v_x_7097_);
    v_r_7099_ = lean_box((v_res_7098_) as usize);
    return v_r_7099_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(
    mut v_fvarId_7100_: *mut LeanObject,
    mut v_x_7101_: *mut LeanObject,
) -> u8 {
    let mut v___x_7102_: u8 = 0;
    v___x_7102_ = l_Lean_instBEqFVarId_beq(v_fvarId_7100_, v_x_7101_);
    return v___x_7102_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed(
    mut v_fvarId_7103_: *mut LeanObject,
    mut v_x_7104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7105_: u8 = 0;
    let mut v_r_7106_: *mut LeanObject = core::ptr::null_mut();
    v_res_7105_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1(v_fvarId_7103_, v_x_7104_);
    lean_dec(v_x_7104_);
    lean_dec(v_fvarId_7103_);
    v_r_7106_ = lean_box((v_res_7105_) as usize);
    return v_r_7106_;
}
pub unsafe fn _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut LeanObject = core::ptr::null_mut();
    v___x_7108_ = lean_box(0);
    v___x_7109_ = lean_unsigned_to_nat(16);
    v___x_7110_ = lean_mk_array(v___x_7109_, v___x_7108_);
    return v___x_7110_;
}
pub unsafe fn _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    v___x_7111_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1_once), _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__1);
    v___x_7112_ = lean_unsigned_to_nat(0);
    v___x_7113_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7113_, 0, v___x_7112_);
    lean_ctor_set(v___x_7113_, 1, v___x_7111_);
    return v___x_7113_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(
    mut v_e_7114_: *mut LeanObject,
    mut v_fvarId_7115_: *mut LeanObject,
    mut v___y_7116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7120_: u8 = 0;
    let mut v_mctx_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7129_: u8 = 0;
    let mut v___x_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7136_: u8 = 0;
    let mut v_unused_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_7142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: u8 = 0;
    let mut v_mctx_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: u8 = 0;
    let mut v___x_7150_: u8 = 0;
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7118_ = lean_st_ref_get(v___y_7116_);
                v_mctx_7144_ = lean_ctor_get(v___x_7118_, 0);
                lean_inc_ref_n(v_mctx_7144_, 2);
                lean_dec(v___x_7118_);
                v___f_7145_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__0;
                v___f_7146_ = lean_alloc_closure(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_7146_, 0, v_fvarId_7115_);
                v___x_7147_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2_once), _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___closed__2);
                v___x_7148_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7148_, 0, v___x_7147_);
                lean_ctor_set(v___x_7148_, 1, v_mctx_7144_);
                v___x_7149_ = l_Lean_Expr_hasFVar(v_e_7114_);
                if v___x_7149_ == 0 {
                    v___x_7150_ = l_Lean_Expr_hasMVar(v_e_7114_);
                    if v___x_7150_ == 0 {
                        lean_dec_ref_known(v___x_7148_, 2);
                        lean_dec_ref(v___f_7146_);
                        lean_dec_ref(v_e_7114_);
                        v_fst_7120_ = v___x_7150_;
                        v_mctx_7121_ = v_mctx_7144_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_mctx_7144_);
                        v___x_7151_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_7146_,
                            v___f_7145_,
                            v_e_7114_,
                            v___x_7148_,
                        );
                        v___y_7139_ = v___x_7151_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_mctx_7144_);
                    v___x_7152_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                        v___f_7146_,
                        v___f_7145_,
                        v_e_7114_,
                        v___x_7148_,
                    );
                    v___y_7139_ = v___x_7152_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_7122_ = lean_st_ref_take(v___y_7116_);
                v_cache_7123_ = lean_ctor_get(v___x_7122_, 1);
                v_zetaDeltaFVarIds_7124_ = lean_ctor_get(v___x_7122_, 2);
                v_postponed_7125_ = lean_ctor_get(v___x_7122_, 3);
                v_diag_7126_ = lean_ctor_get(v___x_7122_, 4);
                v_isSharedCheck_7136_ = (!lean_is_exclusive(v___x_7122_)) as u8;
                if v_isSharedCheck_7136_ == 0 {
                    v_unused_7137_ = lean_ctor_get(v___x_7122_, 0);
                    lean_dec(v_unused_7137_);
                    v___x_7128_ = v___x_7122_;
                    v_isShared_7129_ = v_isSharedCheck_7136_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_diag_7126_);
                    lean_inc(v_postponed_7125_);
                    lean_inc(v_zetaDeltaFVarIds_7124_);
                    lean_inc(v_cache_7123_);
                    lean_dec(v___x_7122_);
                    v___x_7128_ = lean_box(0);
                    v_isShared_7129_ = v_isSharedCheck_7136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_7129_ == 0 {
                    lean_ctor_set(v___x_7128_, 0, v_mctx_7121_);
                    v___x_7131_ = v___x_7128_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7135_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7135_, 0, v_mctx_7121_);
                    lean_ctor_set(v_reuseFailAlloc_7135_, 1, v_cache_7123_);
                    lean_ctor_set(v_reuseFailAlloc_7135_, 2, v_zetaDeltaFVarIds_7124_);
                    lean_ctor_set(v_reuseFailAlloc_7135_, 3, v_postponed_7125_);
                    lean_ctor_set(v_reuseFailAlloc_7135_, 4, v_diag_7126_);
                    v___x_7131_ = v_reuseFailAlloc_7135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7132_ = lean_st_ref_set(v___y_7116_, v___x_7131_);
                v___x_7133_ = lean_box((v_fst_7120_) as usize);
                v___x_7134_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7134_, 0, v___x_7133_);
                return v___x_7134_;
            }
            4 => {
                v_snd_7140_ = lean_ctor_get(v___y_7139_, 1);
                lean_inc(v_snd_7140_);
                v_fst_7141_ = lean_ctor_get(v___y_7139_, 0);
                lean_inc(v_fst_7141_);
                lean_dec_ref(v___y_7139_);
                v_mctx_7142_ = lean_ctor_get(v_snd_7140_, 1);
                lean_inc_ref(v_mctx_7142_);
                lean_dec(v_snd_7140_);
                v___x_7143_ = (lean_unbox(v_fst_7141_) as u8);
                lean_dec(v_fst_7141_);
                v_fst_7120_ = v___x_7143_;
                v_mctx_7121_ = v_mctx_7142_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg___boxed(
    mut v_e_7153_: *mut LeanObject,
    mut v_fvarId_7154_: *mut LeanObject,
    mut v___y_7155_: *mut LeanObject,
    mut v___y_7156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7157_: *mut LeanObject = core::ptr::null_mut();
    v_res_7157_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_7153_, v_fvarId_7154_, v___y_7155_);
    lean_dec(v___y_7155_);
    return v_res_7157_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(
    mut v_e_7158_: *mut LeanObject,
    mut v_fvarId_7159_: *mut LeanObject,
    mut v___y_7160_: *mut LeanObject,
    mut v___y_7161_: *mut LeanObject,
    mut v___y_7162_: *mut LeanObject,
    mut v___y_7163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    v___x_7165_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_e_7158_, v_fvarId_7159_, v___y_7161_);
    return v___x_7165_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___boxed(
    mut v_e_7166_: *mut LeanObject,
    mut v_fvarId_7167_: *mut LeanObject,
    mut v___y_7168_: *mut LeanObject,
    mut v___y_7169_: *mut LeanObject,
    mut v___y_7170_: *mut LeanObject,
    mut v___y_7171_: *mut LeanObject,
    mut v___y_7172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7173_: *mut LeanObject = core::ptr::null_mut();
    v_res_7173_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5(v_e_7166_, v_fvarId_7167_, v___y_7168_, v___y_7169_, v___y_7170_, v___y_7171_);
    lean_dec(v___y_7171_);
    lean_dec_ref(v___y_7170_);
    lean_dec(v___y_7169_);
    lean_dec_ref(v___y_7168_);
    return v_res_7173_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(
    mut v_k_7174_: *mut LeanObject,
    mut v_b_7175_: *mut LeanObject,
    mut v___y_7176_: *mut LeanObject,
    mut v___y_7177_: *mut LeanObject,
    mut v___y_7178_: *mut LeanObject,
    mut v___y_7179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7181_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_7179_);
    lean_inc_ref(v___y_7178_);
    lean_inc(v___y_7177_);
    lean_inc_ref(v___y_7176_);
    v___x_7181_ = lean_apply_6(
        v_k_7174_,
        v_b_7175_,
        v___y_7176_,
        v___y_7177_,
        v___y_7178_,
        v___y_7179_,
        lean_box(0),
    );
    return v___x_7181_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed(
    mut v_k_7182_: *mut LeanObject,
    mut v_b_7183_: *mut LeanObject,
    mut v___y_7184_: *mut LeanObject,
    mut v___y_7185_: *mut LeanObject,
    mut v___y_7186_: *mut LeanObject,
    mut v___y_7187_: *mut LeanObject,
    mut v___y_7188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7189_: *mut LeanObject = core::ptr::null_mut();
    v_res_7189_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0(v_k_7182_, v_b_7183_, v___y_7184_, v___y_7185_, v___y_7186_, v___y_7187_);
    lean_dec(v___y_7187_);
    lean_dec_ref(v___y_7186_);
    lean_dec(v___y_7185_);
    lean_dec_ref(v___y_7184_);
    return v_res_7189_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(
    mut v_perm_7190_: *mut LeanObject,
    mut v_type_7191_: *mut LeanObject,
    mut v_k_7192_: *mut LeanObject,
    mut v___y_7193_: *mut LeanObject,
    mut v___y_7194_: *mut LeanObject,
    mut v___y_7195_: *mut LeanObject,
    mut v___y_7196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7203_: u8 = 0;
    let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7207_: u8 = 0;
    let mut v_a_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7211_: u8 = 0;
    let mut v___x_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7198_ = lean_alloc_closure(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_7198_, 0, v_k_7192_);
                v___x_7199_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_7190_, v_type_7191_, v___f_7198_, v___y_7193_, v___y_7194_, v___y_7195_, v___y_7196_);
                if lean_obj_tag(v___x_7199_) == 0 {
                    v_a_7200_ = lean_ctor_get(v___x_7199_, 0);
                    v_isSharedCheck_7207_ = (!lean_is_exclusive(v___x_7199_)) as u8;
                    if v_isSharedCheck_7207_ == 0 {
                        v___x_7202_ = v___x_7199_;
                        v_isShared_7203_ = v_isSharedCheck_7207_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7200_);
                        lean_dec(v___x_7199_);
                        v___x_7202_ = lean_box(0);
                        v_isShared_7203_ = v_isSharedCheck_7207_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7208_ = lean_ctor_get(v___x_7199_, 0);
                    v_isSharedCheck_7215_ = (!lean_is_exclusive(v___x_7199_)) as u8;
                    if v_isSharedCheck_7215_ == 0 {
                        v___x_7210_ = v___x_7199_;
                        v_isShared_7211_ = v_isSharedCheck_7215_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7208_);
                        lean_dec(v___x_7199_);
                        v___x_7210_ = lean_box(0);
                        v_isShared_7211_ = v_isSharedCheck_7215_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7203_ == 0 {
                    v___x_7205_ = v___x_7202_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7206_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7206_, 0, v_a_7200_);
                    v___x_7205_ = v_reuseFailAlloc_7206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7205_;
            }
            3 => {
                if v_isShared_7211_ == 0 {
                    v___x_7213_ = v___x_7210_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7214_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7214_, 0, v_a_7208_);
                    v___x_7213_ = v_reuseFailAlloc_7214_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7213_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg___boxed(
    mut v_perm_7216_: *mut LeanObject,
    mut v_type_7217_: *mut LeanObject,
    mut v_k_7218_: *mut LeanObject,
    mut v___y_7219_: *mut LeanObject,
    mut v___y_7220_: *mut LeanObject,
    mut v___y_7221_: *mut LeanObject,
    mut v___y_7222_: *mut LeanObject,
    mut v___y_7223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7224_: *mut LeanObject = core::ptr::null_mut();
    v_res_7224_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_7216_, v_type_7217_, v_k_7218_, v___y_7219_, v___y_7220_, v___y_7221_, v___y_7222_);
    lean_dec(v___y_7222_);
    lean_dec_ref(v___y_7221_);
    lean_dec(v___y_7220_);
    lean_dec_ref(v___y_7219_);
    return v_res_7224_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(
    mut v_00_u03b1_7225_: *mut LeanObject,
    mut v_perm_7226_: *mut LeanObject,
    mut v_type_7227_: *mut LeanObject,
    mut v_k_7228_: *mut LeanObject,
    mut v___y_7229_: *mut LeanObject,
    mut v___y_7230_: *mut LeanObject,
    mut v___y_7231_: *mut LeanObject,
    mut v___y_7232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7234_: *mut LeanObject = core::ptr::null_mut();
    v___x_7234_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v_perm_7226_, v_type_7227_, v_k_7228_, v___y_7229_, v___y_7230_, v___y_7231_, v___y_7232_);
    return v___x_7234_;
}
pub unsafe fn l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___boxed(
    mut v_00_u03b1_7235_: *mut LeanObject,
    mut v_perm_7236_: *mut LeanObject,
    mut v_type_7237_: *mut LeanObject,
    mut v_k_7238_: *mut LeanObject,
    mut v___y_7239_: *mut LeanObject,
    mut v___y_7240_: *mut LeanObject,
    mut v___y_7241_: *mut LeanObject,
    mut v___y_7242_: *mut LeanObject,
    mut v___y_7243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7244_: *mut LeanObject = core::ptr::null_mut();
    v_res_7244_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13(v_00_u03b1_7235_, v_perm_7236_, v_type_7237_, v_k_7238_, v___y_7239_, v___y_7240_, v___y_7241_, v___y_7242_);
    lean_dec(v___y_7242_);
    lean_dec_ref(v___y_7241_);
    lean_dec(v___y_7240_);
    lean_dec_ref(v___y_7239_);
    return v_res_7244_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(
    mut v_a_7245_: *mut LeanObject,
    mut v_fst_7246_: *mut LeanObject,
    mut v_fst_7247_: *mut LeanObject,
    mut v___x_7248_: *mut LeanObject,
    mut v___x_7249_: *mut LeanObject,
    mut v___y_7250_: *mut LeanObject,
    mut v___y_7251_: *mut LeanObject,
    mut v___y_7252_: *mut LeanObject,
    mut v___y_7253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7259_: u8 = 0;
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7265_: u8 = 0;
    let mut v_a_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7269_: u8 = 0;
    let mut v___x_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_fst_7246_);
                v___x_7255_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(v_a_7245_, v_fst_7246_, v_fst_7247_, v___x_7248_, v___y_7250_, v___y_7251_, v___y_7252_, v___y_7253_);
                if lean_obj_tag(v___x_7255_) == 0 {
                    v_a_7256_ = lean_ctor_get(v___x_7255_, 0);
                    v_isSharedCheck_7265_ = (!lean_is_exclusive(v___x_7255_)) as u8;
                    if v_isSharedCheck_7265_ == 0 {
                        v___x_7258_ = v___x_7255_;
                        v_isShared_7259_ = v_isSharedCheck_7265_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7256_);
                        lean_dec(v___x_7255_);
                        v___x_7258_ = lean_box(0);
                        v_isShared_7259_ = v_isSharedCheck_7265_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_7249_);
                    lean_dec_ref(v_fst_7246_);
                    v_a_7266_ = lean_ctor_get(v___x_7255_, 0);
                    v_isSharedCheck_7273_ = (!lean_is_exclusive(v___x_7255_)) as u8;
                    if v_isSharedCheck_7273_ == 0 {
                        v___x_7268_ = v___x_7255_;
                        v_isShared_7269_ = v_isSharedCheck_7273_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7266_);
                        lean_dec(v___x_7255_);
                        v___x_7268_ = lean_box(0);
                        v_isShared_7269_ = v_isSharedCheck_7273_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7260_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7260_, 0, v_a_7256_);
                lean_ctor_set(v___x_7260_, 1, v_fst_7246_);
                v___x_7261_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7261_, 0, v___x_7249_);
                lean_ctor_set(v___x_7261_, 1, v___x_7260_);
                if v_isShared_7259_ == 0 {
                    lean_ctor_set(v___x_7258_, 0, v___x_7261_);
                    v___x_7263_ = v___x_7258_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7264_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7264_, 0, v___x_7261_);
                    v___x_7263_ = v_reuseFailAlloc_7264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7263_;
            }
            3 => {
                if v_isShared_7269_ == 0 {
                    v___x_7271_ = v___x_7268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7272_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7272_, 0, v_a_7266_);
                    v___x_7271_ = v_reuseFailAlloc_7272_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed(
    mut v_a_7274_: *mut LeanObject,
    mut v_fst_7275_: *mut LeanObject,
    mut v_fst_7276_: *mut LeanObject,
    mut v___x_7277_: *mut LeanObject,
    mut v___x_7278_: *mut LeanObject,
    mut v___y_7279_: *mut LeanObject,
    mut v___y_7280_: *mut LeanObject,
    mut v___y_7281_: *mut LeanObject,
    mut v___y_7282_: *mut LeanObject,
    mut v___y_7283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7284_: *mut LeanObject = core::ptr::null_mut();
    v_res_7284_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1(v_a_7274_, v_fst_7275_, v_fst_7276_, v___x_7277_, v___x_7278_, v___y_7279_, v___y_7280_, v___y_7281_, v___y_7282_);
    lean_dec(v___y_7282_);
    lean_dec_ref(v___y_7281_);
    lean_dec(v___y_7280_);
    lean_dec_ref(v___y_7279_);
    return v_res_7284_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(
    mut v_sz_7285_: usize,
    mut v_i_7286_: usize,
    mut v_bs_7287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7288_: u8 = 0;
    let mut v_v_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: usize = 0;
    let mut v___x_7294_: usize = 0;
    let mut v___x_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7288_ = lean_usize_dec_lt(v_i_7286_, v_sz_7285_);
                if v___x_7288_ == 0 {
                    return v_bs_7287_;
                } else {
                    v_v_7289_ = lean_array_uget(v_bs_7287_, v_i_7286_);
                    v___x_7290_ = lean_unsigned_to_nat(0);
                    v_bs_x27_7291_ = lean_array_uset(v_bs_7287_, v_i_7286_, v___x_7290_);
                    v___x_7292_ = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(v_v_7289_);
                    v___x_7293_ = 1usize;
                    v___x_7294_ = lean_usize_add(v_i_7286_, v___x_7293_);
                    v___x_7295_ = lean_array_uset(v_bs_x27_7291_, v_i_7286_, v___x_7292_);
                    v_i_7286_ = v___x_7294_;
                    v_bs_7287_ = v___x_7295_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3___boxed(
    mut v_sz_7297_: *mut LeanObject,
    mut v_i_7298_: *mut LeanObject,
    mut v_bs_7299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7300_: usize = 0;
    let mut v_i_boxed_7301_: usize = 0;
    let mut v_res_7302_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7300_ = lean_unbox_usize(v_sz_7297_);
    lean_dec(v_sz_7297_);
    v_i_boxed_7301_ = lean_unbox_usize(v_i_7298_);
    lean_dec(v_i_7298_);
    v_res_7302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_boxed_7300_, v_i_boxed_7301_, v_bs_7299_);
    return v_res_7302_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(
    mut v_lctx_7303_: *mut LeanObject,
    mut v_localInsts_7304_: *mut LeanObject,
    mut v_x_7305_: *mut LeanObject,
    mut v___y_7306_: *mut LeanObject,
    mut v___y_7307_: *mut LeanObject,
    mut v___y_7308_: *mut LeanObject,
    mut v___y_7309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7315_: u8 = 0;
    let mut v___x_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7319_: u8 = 0;
    let mut v_a_7320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7323_: u8 = 0;
    let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7311_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    lean_box(0),
                    v_lctx_7303_,
                    v_localInsts_7304_,
                    v_x_7305_,
                    v___y_7306_,
                    v___y_7307_,
                    v___y_7308_,
                    v___y_7309_,
                );
                if lean_obj_tag(v___x_7311_) == 0 {
                    v_a_7312_ = lean_ctor_get(v___x_7311_, 0);
                    v_isSharedCheck_7319_ = (!lean_is_exclusive(v___x_7311_)) as u8;
                    if v_isSharedCheck_7319_ == 0 {
                        v___x_7314_ = v___x_7311_;
                        v_isShared_7315_ = v_isSharedCheck_7319_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7312_);
                        lean_dec(v___x_7311_);
                        v___x_7314_ = lean_box(0);
                        v_isShared_7315_ = v_isSharedCheck_7319_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7320_ = lean_ctor_get(v___x_7311_, 0);
                    v_isSharedCheck_7327_ = (!lean_is_exclusive(v___x_7311_)) as u8;
                    if v_isSharedCheck_7327_ == 0 {
                        v___x_7322_ = v___x_7311_;
                        v_isShared_7323_ = v_isSharedCheck_7327_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7320_);
                        lean_dec(v___x_7311_);
                        v___x_7322_ = lean_box(0);
                        v_isShared_7323_ = v_isSharedCheck_7327_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7315_ == 0 {
                    v___x_7317_ = v___x_7314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7318_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7318_, 0, v_a_7312_);
                    v___x_7317_ = v_reuseFailAlloc_7318_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7317_;
            }
            3 => {
                if v_isShared_7323_ == 0 {
                    v___x_7325_ = v___x_7322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7326_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7326_, 0, v_a_7320_);
                    v___x_7325_ = v_reuseFailAlloc_7326_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg___boxed(
    mut v_lctx_7328_: *mut LeanObject,
    mut v_localInsts_7329_: *mut LeanObject,
    mut v_x_7330_: *mut LeanObject,
    mut v___y_7331_: *mut LeanObject,
    mut v___y_7332_: *mut LeanObject,
    mut v___y_7333_: *mut LeanObject,
    mut v___y_7334_: *mut LeanObject,
    mut v___y_7335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7336_: *mut LeanObject = core::ptr::null_mut();
    v_res_7336_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_7328_, v_localInsts_7329_, v_x_7330_, v___y_7331_, v___y_7332_, v___y_7333_, v___y_7334_);
    lean_dec(v___y_7334_);
    lean_dec_ref(v___y_7333_);
    lean_dec(v___y_7332_);
    lean_dec_ref(v___y_7331_);
    return v_res_7336_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(
    mut v_as_7337_: *mut LeanObject,
    mut v_i_7338_: usize,
    mut v_stop_7339_: usize,
    mut v_b_7340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7341_: u8 = 0;
    let mut v___x_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: usize = 0;
    let mut v___x_7345_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7341_ = lean_usize_dec_eq(v_i_7338_, v_stop_7339_);
                if v___x_7341_ == 0 {
                    v___x_7342_ = lean_array_uget_borrowed(v_as_7337_, v_i_7338_);
                    lean_inc(v___x_7342_);
                    v___x_7343_ = lean_local_ctx_erase(v_b_7340_, v___x_7342_);
                    v___x_7344_ = 1usize;
                    v___x_7345_ = lean_usize_add(v_i_7338_, v___x_7344_);
                    v_i_7338_ = v___x_7345_;
                    v_b_7340_ = v___x_7343_;
                    state = 0;
                    continue;
                } else {
                    return v_b_7340_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12___boxed(
    mut v_as_7347_: *mut LeanObject,
    mut v_i_7348_: *mut LeanObject,
    mut v_stop_7349_: *mut LeanObject,
    mut v_b_7350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7351_: usize = 0;
    let mut v_stop_boxed_7352_: usize = 0;
    let mut v_res_7353_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7351_ = lean_unbox_usize(v_i_7348_);
    lean_dec(v_i_7348_);
    v_stop_boxed_7352_ = lean_unbox_usize(v_stop_7349_);
    lean_dec(v_stop_7349_);
    v_res_7353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_as_7347_, v_i_boxed_7351_, v_stop_boxed_7352_, v_b_7350_);
    lean_dec_ref(v_as_7347_);
    return v_res_7353_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(
    mut v_a_7354_: *mut LeanObject,
    mut v_as_7355_: *mut LeanObject,
    mut v_i_7356_: usize,
    mut v_stop_7357_: usize,
) -> u8 {
    let mut v___x_7358_: u8 = 0;
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: u8 = 0;
    let mut v___x_7361_: usize = 0;
    let mut v___x_7362_: usize = 0;
    let mut v___x_7364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7358_ = lean_usize_dec_eq(v_i_7356_, v_stop_7357_);
                if v___x_7358_ == 0 {
                    v___x_7359_ = lean_array_uget_borrowed(v_as_7355_, v_i_7356_);
                    v___x_7360_ = l_Lean_instBEqFVarId_beq(v_a_7354_, v___x_7359_);
                    if v___x_7360_ == 0 {
                        v___x_7361_ = 1usize;
                        v___x_7362_ = lean_usize_add(v_i_7356_, v___x_7361_);
                        v_i_7356_ = v___x_7362_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7360_;
                    }
                } else {
                    v___x_7364_ = 0;
                    return v___x_7364_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11___boxed(
    mut v_a_7365_: *mut LeanObject,
    mut v_as_7366_: *mut LeanObject,
    mut v_i_7367_: *mut LeanObject,
    mut v_stop_7368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7369_: usize = 0;
    let mut v_stop_boxed_7370_: usize = 0;
    let mut v_res_7371_: u8 = 0;
    let mut v_r_7372_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7369_ = lean_unbox_usize(v_i_7367_);
    lean_dec(v_i_7367_);
    v_stop_boxed_7370_ = lean_unbox_usize(v_stop_7368_);
    lean_dec(v_stop_7368_);
    v_res_7371_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_7365_, v_as_7366_, v_i_boxed_7369_, v_stop_boxed_7370_);
    lean_dec_ref(v_as_7366_);
    lean_dec(v_a_7365_);
    v_r_7372_ = lean_box((v_res_7371_) as usize);
    return v_r_7372_;
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(
    mut v_as_7373_: *mut LeanObject,
    mut v_a_7374_: *mut LeanObject,
) -> u8 {
    let mut v___x_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: u8 = 0;
    v___x_7375_ = lean_unsigned_to_nat(0);
    v___x_7376_ = lean_array_get_size(v_as_7373_);
    v___x_7377_ = lean_nat_dec_lt(v___x_7375_, v___x_7376_);
    if v___x_7377_ == 0 {
        return v___x_7377_;
    } else {
        if v___x_7377_ == 0 {
            return v___x_7377_;
        } else {
            let mut v___x_7378_: usize = 0;
            let mut v___x_7379_: usize = 0;
            let mut v___x_7380_: u8 = 0;
            v___x_7378_ = 0usize;
            v___x_7379_ = lean_usize_of_nat(v___x_7376_);
            v___x_7380_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9_spec__11(v_a_7374_, v_as_7373_, v___x_7378_, v___x_7379_);
            return v___x_7380_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9___boxed(
    mut v_as_7381_: *mut LeanObject,
    mut v_a_7382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7383_: u8 = 0;
    let mut v_r_7384_: *mut LeanObject = core::ptr::null_mut();
    v_res_7383_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_as_7381_, v_a_7382_);
    lean_dec(v_a_7382_);
    lean_dec_ref(v_as_7381_);
    v_r_7384_ = lean_box((v_res_7383_) as usize);
    return v_r_7384_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(
    mut v_fvarIds_7385_: *mut LeanObject,
    mut v_as_7386_: *mut LeanObject,
    mut v_i_7387_: usize,
    mut v_stop_7388_: usize,
    mut v_b_7389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: usize = 0;
    let mut v___x_7393_: usize = 0;
    let mut v___x_7395_: u8 = 0;
    let mut v___x_7396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvar_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7399_: u8 = 0;
    let mut v___x_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7395_ = lean_usize_dec_eq(v_i_7387_, v_stop_7388_);
                if v___x_7395_ == 0 {
                    v___x_7396_ = lean_array_uget_borrowed(v_as_7386_, v_i_7387_);
                    v_fvar_7397_ = lean_ctor_get(v___x_7396_, 1);
                    v___x_7398_ = l_Lean_Expr_fvarId_x21(v_fvar_7397_);
                    v___x_7399_ = l_Array_contains___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__9(v_fvarIds_7385_, v___x_7398_);
                    lean_dec(v___x_7398_);
                    if v___x_7399_ == 0 {
                        lean_inc(v___x_7396_);
                        v___x_7400_ = lean_array_push(v_b_7389_, v___x_7396_);
                        v___y_7391_ = v___x_7400_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7391_ = v_b_7389_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_7389_;
                }
            }
            1 => {
                v___x_7392_ = 1usize;
                v___x_7393_ = lean_usize_add(v_i_7387_, v___x_7392_);
                v_i_7387_ = v___x_7393_;
                v_b_7389_ = v___y_7391_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11___boxed(
    mut v_fvarIds_7401_: *mut LeanObject,
    mut v_as_7402_: *mut LeanObject,
    mut v_i_7403_: *mut LeanObject,
    mut v_stop_7404_: *mut LeanObject,
    mut v_b_7405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7406_: usize = 0;
    let mut v_stop_boxed_7407_: usize = 0;
    let mut v_res_7408_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7406_ = lean_unbox_usize(v_i_7403_);
    lean_dec(v_i_7403_);
    v_stop_boxed_7407_ = lean_unbox_usize(v_stop_7404_);
    lean_dec(v_stop_7404_);
    v_res_7408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_7401_, v_as_7402_, v_i_boxed_7406_, v_stop_boxed_7407_, v_b_7405_);
    lean_dec_ref(v_as_7402_);
    lean_dec_ref(v_fvarIds_7401_);
    return v_res_7408_;
}
pub unsafe fn l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(
    mut v_fvarIds_7411_: *mut LeanObject,
    mut v_k_7412_: *mut LeanObject,
    mut v___y_7413_: *mut LeanObject,
    mut v___y_7414_: *mut LeanObject,
    mut v___y_7415_: *mut LeanObject,
    mut v___y_7416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: u8 = 0;
    let mut v___x_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7427_: u8 = 0;
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7429_: usize = 0;
    let mut v___x_7430_: usize = 0;
    let mut v___x_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: usize = 0;
    let mut v___x_7434_: usize = 0;
    let mut v___x_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: u8 = 0;
    let mut v___x_7439_: u8 = 0;
    let mut v___x_7440_: usize = 0;
    let mut v___x_7441_: usize = 0;
    let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: usize = 0;
    let mut v___x_7444_: usize = 0;
    let mut v___x_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_7418_ = lean_ctor_get(v___y_7413_, 2);
                v_localInstances_7419_ = lean_ctor_get(v___y_7413_, 3);
                v___x_7420_ = lean_unsigned_to_nat(0);
                v___x_7437_ = lean_array_get_size(v_fvarIds_7411_);
                v___x_7438_ = lean_nat_dec_lt(v___x_7420_, v___x_7437_);
                if v___x_7438_ == 0 {
                    lean_inc_ref(v_lctx_7418_);
                    v___y_7422_ = v_lctx_7418_;
                    state = 1;
                    continue;
                } else {
                    v___x_7439_ = lean_nat_dec_le(v___x_7437_, v___x_7437_);
                    if v___x_7439_ == 0 {
                        if v___x_7438_ == 0 {
                            lean_inc_ref(v_lctx_7418_);
                            v___y_7422_ = v_lctx_7418_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7440_ = 0usize;
                            v___x_7441_ = lean_usize_of_nat(v___x_7437_);
                            lean_inc_ref(v_lctx_7418_);
                            v___x_7442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_7411_, v___x_7440_, v___x_7441_, v_lctx_7418_);
                            v___y_7422_ = v___x_7442_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7443_ = 0usize;
                        v___x_7444_ = lean_usize_of_nat(v___x_7437_);
                        lean_inc_ref(v_lctx_7418_);
                        v___x_7445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__12(v_fvarIds_7411_, v___x_7443_, v___x_7444_, v_lctx_7418_);
                        v___y_7422_ = v___x_7445_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7423_ = lean_array_get_size(v_localInstances_7419_);
                v___x_7424_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___closed__0;
                v___x_7425_ = lean_nat_dec_lt(v___x_7420_, v___x_7423_);
                if v___x_7425_ == 0 {
                    v___x_7426_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_7422_, v___x_7424_, v_k_7412_, v___y_7413_, v___y_7414_, v___y_7415_, v___y_7416_);
                    return v___x_7426_;
                } else {
                    v___x_7427_ = lean_nat_dec_le(v___x_7423_, v___x_7423_);
                    if v___x_7427_ == 0 {
                        if v___x_7425_ == 0 {
                            v___x_7428_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_7422_, v___x_7424_, v_k_7412_, v___y_7413_, v___y_7414_, v___y_7415_, v___y_7416_);
                            return v___x_7428_;
                        } else {
                            v___x_7429_ = 0usize;
                            v___x_7430_ = lean_usize_of_nat(v___x_7423_);
                            v___x_7431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_7411_, v_localInstances_7419_, v___x_7429_, v___x_7430_, v___x_7424_);
                            v___x_7432_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_7422_, v___x_7431_, v_k_7412_, v___y_7413_, v___y_7414_, v___y_7415_, v___y_7416_);
                            return v___x_7432_;
                        }
                    } else {
                        v___x_7433_ = 0usize;
                        v___x_7434_ = lean_usize_of_nat(v___x_7423_);
                        v___x_7435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__11(v_fvarIds_7411_, v_localInstances_7419_, v___x_7433_, v___x_7434_, v___x_7424_);
                        v___x_7436_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v___y_7422_, v___x_7435_, v_k_7412_, v___y_7413_, v___y_7414_, v___y_7415_, v___y_7416_);
                        return v___x_7436_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg___boxed(
    mut v_fvarIds_7446_: *mut LeanObject,
    mut v_k_7447_: *mut LeanObject,
    mut v___y_7448_: *mut LeanObject,
    mut v___y_7449_: *mut LeanObject,
    mut v___y_7450_: *mut LeanObject,
    mut v___y_7451_: *mut LeanObject,
    mut v___y_7452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7453_: *mut LeanObject = core::ptr::null_mut();
    v_res_7453_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_7446_, v_k_7447_, v___y_7448_, v___y_7449_, v___y_7450_, v___y_7451_);
    lean_dec(v___y_7451_);
    lean_dec_ref(v___y_7450_);
    lean_dec(v___y_7449_);
    lean_dec_ref(v___y_7448_);
    lean_dec_ref(v_fvarIds_7446_);
    return v_res_7453_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(
    mut v_x_7454_: *mut LeanObject,
    mut v_x_7455_: *mut LeanObject,
    mut v_x_7456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7461_: u8 = 0;
    let mut v___x_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7456_) == 0 {
                    lean_dec(v_x_7454_);
                    return v_x_7455_;
                } else {
                    v_head_7457_ = lean_ctor_get(v_x_7456_, 0);
                    v_tail_7458_ = lean_ctor_get(v_x_7456_, 1);
                    v_isSharedCheck_7468_ = (!lean_is_exclusive(v_x_7456_)) as u8;
                    if v_isSharedCheck_7468_ == 0 {
                        v___x_7460_ = v_x_7456_;
                        v_isShared_7461_ = v_isSharedCheck_7468_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7458_);
                        lean_inc(v_head_7457_);
                        lean_dec(v_x_7456_);
                        v___x_7460_ = lean_box(0);
                        v_isShared_7461_ = v_isSharedCheck_7468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_7454_);
                if v_isShared_7461_ == 0 {
                    lean_ctor_set_tag(v___x_7460_, 5);
                    lean_ctor_set(v___x_7460_, 1, v_x_7454_);
                    lean_ctor_set(v___x_7460_, 0, v_x_7455_);
                    v___x_7463_ = v___x_7460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7467_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7467_, 0, v_x_7455_);
                    lean_ctor_set(v_reuseFailAlloc_7467_, 1, v_x_7454_);
                    v___x_7463_ = v_reuseFailAlloc_7467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7464_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_7457_);
                v___x_7465_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_7465_, 0, v___x_7463_);
                lean_ctor_set(v___x_7465_, 1, v___x_7464_);
                v_x_7455_ = v___x_7465_;
                v_x_7456_ = v_tail_7458_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(
    mut v_x_7469_: *mut LeanObject,
    mut v_x_7470_: *mut LeanObject,
    mut v_x_7471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_7472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7476_: u8 = 0;
    let mut v___x_7478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7471_) == 0 {
                    lean_dec(v_x_7469_);
                    return v_x_7470_;
                } else {
                    v_head_7472_ = lean_ctor_get(v_x_7471_, 0);
                    v_tail_7473_ = lean_ctor_get(v_x_7471_, 1);
                    v_isSharedCheck_7483_ = (!lean_is_exclusive(v_x_7471_)) as u8;
                    if v_isSharedCheck_7483_ == 0 {
                        v___x_7475_ = v_x_7471_;
                        v_isShared_7476_ = v_isSharedCheck_7483_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7473_);
                        lean_inc(v_head_7472_);
                        lean_dec(v_x_7471_);
                        v___x_7475_ = lean_box(0);
                        v_isShared_7476_ = v_isSharedCheck_7483_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_7469_);
                if v_isShared_7476_ == 0 {
                    lean_ctor_set_tag(v___x_7475_, 5);
                    lean_ctor_set(v___x_7475_, 1, v_x_7469_);
                    lean_ctor_set(v___x_7475_, 0, v_x_7470_);
                    v___x_7478_ = v___x_7475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7482_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7482_, 0, v_x_7470_);
                    lean_ctor_set(v_reuseFailAlloc_7482_, 1, v_x_7469_);
                    v___x_7478_ = v_reuseFailAlloc_7482_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7479_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_7472_);
                v___x_7480_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_7480_, 0, v___x_7478_);
                lean_ctor_set(v___x_7480_, 1, v___x_7479_);
                v___x_7481_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17_spec__21(v_x_7469_, v___x_7480_, v_tail_7473_);
                return v___x_7481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(
    mut v_x_7484_: *mut LeanObject,
    mut v_x_7485_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_7484_) == 0 {
        let mut v___x_7486_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_7485_);
        v___x_7486_ = lean_box(0);
        return v___x_7486_;
    } else {
        let mut v_tail_7487_: *mut LeanObject = core::ptr::null_mut();
        v_tail_7487_ = lean_ctor_get(v_x_7484_, 1);
        if lean_obj_tag(v_tail_7487_) == 0 {
            let mut v_head_7488_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7489_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_7485_);
            v_head_7488_ = lean_ctor_get(v_x_7484_, 0);
            lean_inc(v_head_7488_);
            lean_dec_ref_known(v_x_7484_, 2);
            v___x_7489_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_7488_);
            return v___x_7489_;
        } else {
            let mut v_head_7490_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7491_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7492_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_7487_);
            v_head_7490_ = lean_ctor_get(v_x_7484_, 0);
            lean_inc(v_head_7490_);
            lean_dec_ref_known(v_x_7484_, 2);
            v___x_7491_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_7490_);
            v___x_7492_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14_spec__17(v_x_7485_, v___x_7491_, v_tail_7487_);
            return v___x_7492_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5()
-> *mut LeanObject {
    let mut v___x_7501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7502_: *mut LeanObject = core::ptr::null_mut();
    v___x_7501_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__0;
    v___x_7502_ = lean_string_length(v___x_7501_);
    return v___x_7502_;
}
pub unsafe fn _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6()
-> *mut LeanObject {
    let mut v___x_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut LeanObject = core::ptr::null_mut();
    v___x_7503_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5), core::ptr::addr_of_mut!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5_once), _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__5);
    v___x_7504_ = lean_nat_to_int(v___x_7503_);
    return v___x_7504_;
}
pub unsafe fn l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(
    mut v_xs_7512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: u8 = 0;
    v___x_7513_ = lean_array_get_size(v_xs_7512_);
    v___x_7514_ = lean_unsigned_to_nat(0);
    v___x_7515_ = lean_nat_dec_eq(v___x_7513_, v___x_7514_);
    if v___x_7515_ == 0 {
        let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7525_: *mut LeanObject = core::ptr::null_mut();
        v___x_7516_ = lean_array_to_list(v_xs_7512_);
        v___x_7517_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__3;
        v___x_7518_ = l_Std_Format_joinSep___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__14(v___x_7516_, v___x_7517_);
        v___x_7519_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6_once), _init_l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__6);
        v___x_7520_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__7;
        v___x_7521_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_7521_, 0, v___x_7520_);
        lean_ctor_set(v___x_7521_, 1, v___x_7518_);
        v___x_7522_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__8;
        v___x_7523_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_7523_, 0, v___x_7521_);
        lean_ctor_set(v___x_7523_, 1, v___x_7522_);
        v___x_7524_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_7524_, 0, v___x_7519_);
        lean_ctor_set(v___x_7524_, 1, v___x_7523_);
        v___x_7525_ = l_Std_Format_fill(v___x_7524_);
        return v___x_7525_;
    } else {
        let mut v___x_7526_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_7512_);
        v___x_7526_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10___closed__10;
        return v___x_7526_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(
    mut v_sz_7527_: usize,
    mut v_i_7528_: usize,
    mut v_bs_7529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7530_: u8 = 0;
    let mut v_v_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: usize = 0;
    let mut v___x_7536_: usize = 0;
    let mut v___x_7537_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7530_ = lean_usize_dec_lt(v_i_7528_, v_sz_7527_);
                if v___x_7530_ == 0 {
                    return v_bs_7529_;
                } else {
                    v_v_7531_ = lean_array_uget(v_bs_7529_, v_i_7528_);
                    v___x_7532_ = lean_unsigned_to_nat(0);
                    v_bs_x27_7533_ = lean_array_uset(v_bs_7529_, v_i_7528_, v___x_7532_);
                    v___x_7534_ = l_Lean_mkFVar(v_v_7531_);
                    v___x_7535_ = 1usize;
                    v___x_7536_ = lean_usize_add(v_i_7528_, v___x_7535_);
                    v___x_7537_ = lean_array_uset(v_bs_x27_7533_, v_i_7528_, v___x_7534_);
                    v_i_7528_ = v___x_7536_;
                    v_bs_7529_ = v___x_7537_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11___boxed(
    mut v_sz_7539_: *mut LeanObject,
    mut v_i_7540_: *mut LeanObject,
    mut v_bs_7541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7542_: usize = 0;
    let mut v_i_boxed_7543_: usize = 0;
    let mut v_res_7544_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7542_ = lean_unbox_usize(v_sz_7539_);
    lean_dec(v_sz_7539_);
    v_i_boxed_7543_ = lean_unbox_usize(v_i_7540_);
    lean_dec(v_i_7540_);
    v_res_7544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_boxed_7542_, v_i_boxed_7543_, v_bs_7541_);
    return v_res_7544_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(
    mut v_fst_7545_: *mut LeanObject,
    mut v_as_7546_: *mut LeanObject,
    mut v_i_7547_: *mut LeanObject,
    mut v_j_7548_: *mut LeanObject,
    mut v_bs_7549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_7550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7551_: u8 = 0;
    let mut v___x_7552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnName_7553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recArgPos_7554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_7555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indGroupInst_7556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indIdx_7557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7560_: u8 = 0;
    let mut v_perms_7561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_7563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7572_: u8 = 0;
    let mut v_unused_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7550_ = lean_unsigned_to_nat(0);
                v_isZero_7551_ = lean_nat_dec_eq(v_i_7547_, v_zero_7550_);
                if v_isZero_7551_ == 1 {
                    lean_dec(v_j_7548_);
                    lean_dec(v_i_7547_);
                    return v_bs_7549_;
                } else {
                    v___x_7552_ = lean_array_fget(v_as_7546_, v_j_7548_);
                    v_fnName_7553_ = lean_ctor_get(v___x_7552_, 0);
                    v_recArgPos_7554_ = lean_ctor_get(v___x_7552_, 2);
                    v_indicesPos_7555_ = lean_ctor_get(v___x_7552_, 3);
                    v_indGroupInst_7556_ = lean_ctor_get(v___x_7552_, 4);
                    v_indIdx_7557_ = lean_ctor_get(v___x_7552_, 5);
                    v_isSharedCheck_7572_ = (!lean_is_exclusive(v___x_7552_)) as u8;
                    if v_isSharedCheck_7572_ == 0 {
                        v_unused_7573_ = lean_ctor_get(v___x_7552_, 1);
                        lean_dec(v_unused_7573_);
                        v___x_7559_ = v___x_7552_;
                        v_isShared_7560_ = v_isSharedCheck_7572_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_indIdx_7557_);
                        lean_inc(v_indGroupInst_7556_);
                        lean_inc(v_indicesPos_7555_);
                        lean_inc(v_recArgPos_7554_);
                        lean_inc(v_fnName_7553_);
                        lean_dec(v___x_7552_);
                        v___x_7559_ = lean_box(0);
                        v_isShared_7560_ = v_isSharedCheck_7572_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_perms_7561_ = lean_ctor_get(v_fst_7545_, 1);
                v___x_7562_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
                v_one_7563_ = lean_unsigned_to_nat(1);
                v_n_7564_ = lean_nat_sub(v_i_7547_, v_one_7563_);
                lean_dec(v_i_7547_);
                v___x_7565_ = lean_array_get_borrowed(v___x_7562_, v_perms_7561_, v_j_7548_);
                lean_inc(v___x_7565_);
                if v_isShared_7560_ == 0 {
                    lean_ctor_set(v___x_7559_, 1, v___x_7565_);
                    v___x_7567_ = v___x_7559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7571_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7571_, 0, v_fnName_7553_);
                    lean_ctor_set(v_reuseFailAlloc_7571_, 1, v___x_7565_);
                    lean_ctor_set(v_reuseFailAlloc_7571_, 2, v_recArgPos_7554_);
                    lean_ctor_set(v_reuseFailAlloc_7571_, 3, v_indicesPos_7555_);
                    lean_ctor_set(v_reuseFailAlloc_7571_, 4, v_indGroupInst_7556_);
                    lean_ctor_set(v_reuseFailAlloc_7571_, 5, v_indIdx_7557_);
                    v___x_7567_ = v_reuseFailAlloc_7571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7568_ = lean_nat_add(v_j_7548_, v_one_7563_);
                lean_dec(v_j_7548_);
                v___x_7569_ = lean_array_push(v_bs_7549_, v___x_7567_);
                v_i_7547_ = v_n_7564_;
                v_j_7548_ = v___x_7568_;
                v_bs_7549_ = v___x_7569_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg___boxed(
    mut v_fst_7574_: *mut LeanObject,
    mut v_as_7575_: *mut LeanObject,
    mut v_i_7576_: *mut LeanObject,
    mut v_j_7577_: *mut LeanObject,
    mut v_bs_7578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7579_: *mut LeanObject = core::ptr::null_mut();
    v_res_7579_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_7574_, v_as_7575_, v_i_7576_, v_j_7577_, v_bs_7578_);
    lean_dec_ref(v_as_7575_);
    lean_dec_ref(v_fst_7574_);
    return v_res_7579_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(
    mut v_sz_7580_: usize,
    mut v_i_7581_: usize,
    mut v_bs_7582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7583_: u8 = 0;
    let mut v_v_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recArgPos_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: usize = 0;
    let mut v___x_7589_: usize = 0;
    let mut v___x_7590_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7583_ = lean_usize_dec_lt(v_i_7581_, v_sz_7580_);
                if v___x_7583_ == 0 {
                    return v_bs_7582_;
                } else {
                    v_v_7584_ = lean_array_uget_borrowed(v_bs_7582_, v_i_7581_);
                    v_recArgPos_7585_ = lean_ctor_get(v_v_7584_, 2);
                    lean_inc(v_recArgPos_7585_);
                    v___x_7586_ = lean_unsigned_to_nat(0);
                    v_bs_x27_7587_ = lean_array_uset(v_bs_7582_, v_i_7581_, v___x_7586_);
                    v___x_7588_ = 1usize;
                    v___x_7589_ = lean_usize_add(v_i_7581_, v___x_7588_);
                    v___x_7590_ = lean_array_uset(v_bs_x27_7587_, v_i_7581_, v_recArgPos_7585_);
                    v_i_7581_ = v___x_7589_;
                    v_bs_7582_ = v___x_7590_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2___boxed(
    mut v_sz_7592_: *mut LeanObject,
    mut v_i_7593_: *mut LeanObject,
    mut v_bs_7594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7595_: usize = 0;
    let mut v_i_boxed_7596_: usize = 0;
    let mut v_res_7597_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7595_ = lean_unbox_usize(v_sz_7592_);
    lean_dec(v_sz_7592_);
    v_i_boxed_7596_ = lean_unbox_usize(v_i_7593_);
    lean_dec(v_i_7593_);
    v_res_7597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_boxed_7595_, v_i_boxed_7596_, v_bs_7594_);
    return v_res_7597_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1()
-> *mut LeanObject {
    let mut v___x_7599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut LeanObject = core::ptr::null_mut();
    v___x_7599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__0;
    v___x_7600_ = l_Lean_stringToMessageData(v___x_7599_);
    return v___x_7600_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3()
-> *mut LeanObject {
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: *mut LeanObject = core::ptr::null_mut();
    v___x_7602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__2;
    v___x_7603_ = l_Lean_stringToMessageData(v___x_7602_);
    return v___x_7603_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5()
-> *mut LeanObject {
    let mut v___x_7605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7606_: *mut LeanObject = core::ptr::null_mut();
    v___x_7605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__4;
    v___x_7606_ = l_Lean_stringToMessageData(v___x_7605_);
    return v___x_7606_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(
    mut v_a_7607_: *mut LeanObject,
    mut v_as_7608_: *mut LeanObject,
    mut v_sz_7609_: usize,
    mut v_i_7610_: usize,
    mut v_b_7611_: *mut LeanObject,
    mut v___y_7612_: *mut LeanObject,
    mut v___y_7613_: *mut LeanObject,
    mut v___y_7614_: *mut LeanObject,
    mut v___y_7615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7619_: usize = 0;
    let mut v___x_7620_: usize = 0;
    let mut v___x_7622_: u8 = 0;
    let mut v___x_7623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7628_: u8 = 0;
    let mut v___x_7629_: u8 = 0;
    let mut v___x_7630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7650_: u8 = 0;
    let mut v___x_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7622_ = lean_usize_dec_lt(v_i_7610_, v_sz_7609_);
                if v___x_7622_ == 0 {
                    lean_dec_ref(v_a_7607_);
                    v___x_7623_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7623_, 0, v_b_7611_);
                    return v___x_7623_;
                } else {
                    v_a_7624_ = lean_array_uget_borrowed(v_as_7608_, v_i_7610_);
                    lean_inc(v_a_7624_);
                    lean_inc_ref(v_a_7607_);
                    v___x_7625_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__5___redArg(v_a_7607_, v_a_7624_, v___y_7613_);
                    if lean_obj_tag(v___x_7625_) == 0 {
                        v_a_7626_ = lean_ctor_get(v___x_7625_, 0);
                        lean_inc(v_a_7626_);
                        lean_dec_ref_known(v___x_7625_, 1);
                        v___x_7627_ = lean_box(0);
                        v___x_7628_ = (lean_unbox(v_a_7626_) as u8);
                        lean_dec(v_a_7626_);
                        if v___x_7628_ == 0 {
                            v_a_7618_ = v___x_7627_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7629_ = l_Lean_Expr_isFVarOf(v_a_7607_, v_a_7624_);
                            if v___x_7629_ == 0 {
                                v___x_7630_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
                                lean_inc_ref(v_a_7607_);
                                v___x_7631_ = l_Lean_indentExpr(v_a_7607_);
                                v___x_7632_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7632_, 0, v___x_7630_);
                                lean_ctor_set(v___x_7632_, 1, v___x_7631_);
                                v___x_7633_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__3);
                                v___x_7634_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7634_, 0, v___x_7632_);
                                lean_ctor_set(v___x_7634_, 1, v___x_7633_);
                                lean_inc(v_a_7624_);
                                v___x_7635_ = l_Lean_mkFVar(v_a_7624_);
                                v___x_7636_ = l_Lean_indentExpr(v___x_7635_);
                                v___x_7637_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7637_, 0, v___x_7634_);
                                lean_ctor_set(v___x_7637_, 1, v___x_7636_);
                                v___x_7638_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
                                v___x_7639_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7639_, 0, v___x_7637_);
                                lean_ctor_set(v___x_7639_, 1, v___x_7638_);
                                v___x_7640_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_7639_, v___y_7612_, v___y_7613_, v___y_7614_, v___y_7615_);
                                if lean_obj_tag(v___x_7640_) == 0 {
                                    lean_dec_ref_known(v___x_7640_, 1);
                                    v_a_7618_ = v___x_7627_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref(v_a_7607_);
                                    return v___x_7640_;
                                }
                            } else {
                                v___x_7641_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__1);
                                lean_inc_ref(v_a_7607_);
                                v___x_7642_ = l_Lean_indentExpr(v_a_7607_);
                                v___x_7643_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7643_, 0, v___x_7641_);
                                lean_ctor_set(v___x_7643_, 1, v___x_7642_);
                                v___x_7644_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___closed__5);
                                v___x_7645_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_7645_, 0, v___x_7643_);
                                lean_ctor_set(v___x_7645_, 1, v___x_7644_);
                                v___x_7646_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__4_spec__4___redArg(v___x_7645_, v___y_7612_, v___y_7613_, v___y_7614_, v___y_7615_);
                                if lean_obj_tag(v___x_7646_) == 0 {
                                    lean_dec_ref_known(v___x_7646_, 1);
                                    v_a_7618_ = v___x_7627_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref(v_a_7607_);
                                    return v___x_7646_;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_a_7607_);
                        v_a_7647_ = lean_ctor_get(v___x_7625_, 0);
                        v_isSharedCheck_7654_ = (!lean_is_exclusive(v___x_7625_)) as u8;
                        if v_isSharedCheck_7654_ == 0 {
                            v___x_7649_ = v___x_7625_;
                            v_isShared_7650_ = v_isSharedCheck_7654_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_7647_);
                            lean_dec(v___x_7625_);
                            v___x_7649_ = lean_box(0);
                            v_isShared_7650_ = v_isSharedCheck_7654_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7619_ = 1usize;
                v___x_7620_ = lean_usize_add(v_i_7610_, v___x_7619_);
                v_i_7610_ = v___x_7620_;
                v_b_7611_ = v_a_7618_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_7650_ == 0 {
                    v___x_7652_ = v___x_7649_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7653_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7653_, 0, v_a_7647_);
                    v___x_7652_ = v_reuseFailAlloc_7653_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6___boxed(
    mut v_a_7655_: *mut LeanObject,
    mut v_as_7656_: *mut LeanObject,
    mut v_sz_7657_: *mut LeanObject,
    mut v_i_7658_: *mut LeanObject,
    mut v_b_7659_: *mut LeanObject,
    mut v___y_7660_: *mut LeanObject,
    mut v___y_7661_: *mut LeanObject,
    mut v___y_7662_: *mut LeanObject,
    mut v___y_7663_: *mut LeanObject,
    mut v___y_7664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7665_: usize = 0;
    let mut v_i_boxed_7666_: usize = 0;
    let mut v_res_7667_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7665_ = lean_unbox_usize(v_sz_7657_);
    lean_dec(v_sz_7657_);
    v_i_boxed_7666_ = lean_unbox_usize(v_i_7658_);
    lean_dec(v_i_7658_);
    v_res_7667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_7655_, v_as_7656_, v_sz_boxed_7665_, v_i_boxed_7666_, v_b_7659_, v___y_7660_, v___y_7661_, v___y_7662_, v___y_7663_);
    lean_dec(v___y_7663_);
    lean_dec_ref(v___y_7662_);
    lean_dec(v___y_7661_);
    lean_dec_ref(v___y_7660_);
    lean_dec_ref(v_as_7656_);
    return v_res_7667_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(
    mut v_snd_7668_: *mut LeanObject,
    mut v_as_7669_: *mut LeanObject,
    mut v_sz_7670_: usize,
    mut v_i_7671_: usize,
    mut v_b_7672_: *mut LeanObject,
    mut v___y_7673_: *mut LeanObject,
    mut v___y_7674_: *mut LeanObject,
    mut v___y_7675_: *mut LeanObject,
    mut v___y_7676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7678_: u8 = 0;
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7682_: usize = 0;
    let mut v___x_7683_: usize = 0;
    let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: usize = 0;
    let mut v___x_7686_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7678_ = lean_usize_dec_lt(v_i_7671_, v_sz_7670_);
                if v___x_7678_ == 0 {
                    v___x_7679_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7679_, 0, v_b_7672_);
                    return v___x_7679_;
                } else {
                    v___x_7680_ = lean_box(0);
                    v_a_7681_ = lean_array_uget_borrowed(v_as_7669_, v_i_7671_);
                    v_sz_7682_ = lean_array_size(v_snd_7668_);
                    v___x_7683_ = 0usize;
                    lean_inc(v_a_7681_);
                    v___x_7684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__6(v_a_7681_, v_snd_7668_, v_sz_7682_, v___x_7683_, v___x_7680_, v___y_7673_, v___y_7674_, v___y_7675_, v___y_7676_);
                    if lean_obj_tag(v___x_7684_) == 0 {
                        lean_dec_ref_known(v___x_7684_, 1);
                        v___x_7685_ = 1usize;
                        v___x_7686_ = lean_usize_add(v_i_7671_, v___x_7685_);
                        v_i_7671_ = v___x_7686_;
                        v_b_7672_ = v___x_7680_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7684_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7___boxed(
    mut v_snd_7688_: *mut LeanObject,
    mut v_as_7689_: *mut LeanObject,
    mut v_sz_7690_: *mut LeanObject,
    mut v_i_7691_: *mut LeanObject,
    mut v_b_7692_: *mut LeanObject,
    mut v___y_7693_: *mut LeanObject,
    mut v___y_7694_: *mut LeanObject,
    mut v___y_7695_: *mut LeanObject,
    mut v___y_7696_: *mut LeanObject,
    mut v___y_7697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7698_: usize = 0;
    let mut v_i_boxed_7699_: usize = 0;
    let mut v_res_7700_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7698_ = lean_unbox_usize(v_sz_7690_);
    lean_dec(v_sz_7690_);
    v_i_boxed_7699_ = lean_unbox_usize(v_i_7691_);
    lean_dec(v_i_7691_);
    v_res_7700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_7688_, v_as_7689_, v_sz_boxed_7698_, v_i_boxed_7699_, v_b_7692_, v___y_7693_, v___y_7694_, v___y_7695_, v___y_7696_);
    lean_dec(v___y_7696_);
    lean_dec_ref(v___y_7695_);
    lean_dec(v___y_7694_);
    lean_dec_ref(v___y_7693_);
    lean_dec_ref(v_as_7689_);
    lean_dec_ref(v_snd_7688_);
    return v_res_7700_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(
    mut v_snd_7701_: *mut LeanObject,
    mut v_as_7702_: *mut LeanObject,
    mut v_sz_7703_: usize,
    mut v_i_7704_: usize,
    mut v_b_7705_: *mut LeanObject,
    mut v___y_7706_: *mut LeanObject,
    mut v___y_7707_: *mut LeanObject,
    mut v___y_7708_: *mut LeanObject,
    mut v___y_7709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7711_: u8 = 0;
    let mut v___x_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indGroupInst_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7717_: usize = 0;
    let mut v___x_7718_: usize = 0;
    let mut v___x_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7720_: usize = 0;
    let mut v___x_7721_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7711_ = lean_usize_dec_lt(v_i_7704_, v_sz_7703_);
                if v___x_7711_ == 0 {
                    v___x_7712_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7712_, 0, v_b_7705_);
                    return v___x_7712_;
                } else {
                    v_a_7713_ = lean_array_uget_borrowed(v_as_7702_, v_i_7704_);
                    v_indGroupInst_7714_ = lean_ctor_get(v_a_7713_, 4);
                    v_params_7715_ = lean_ctor_get(v_indGroupInst_7714_, 2);
                    v___x_7716_ = lean_box(0);
                    v_sz_7717_ = lean_array_size(v_params_7715_);
                    v___x_7718_ = 0usize;
                    v___x_7719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__7(v_snd_7701_, v_params_7715_, v_sz_7717_, v___x_7718_, v___x_7716_, v___y_7706_, v___y_7707_, v___y_7708_, v___y_7709_);
                    if lean_obj_tag(v___x_7719_) == 0 {
                        lean_dec_ref_known(v___x_7719_, 1);
                        v___x_7720_ = 1usize;
                        v___x_7721_ = lean_usize_add(v_i_7704_, v___x_7720_);
                        v_i_7704_ = v___x_7721_;
                        v_b_7705_ = v___x_7716_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7719_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8___boxed(
    mut v_snd_7723_: *mut LeanObject,
    mut v_as_7724_: *mut LeanObject,
    mut v_sz_7725_: *mut LeanObject,
    mut v_i_7726_: *mut LeanObject,
    mut v_b_7727_: *mut LeanObject,
    mut v___y_7728_: *mut LeanObject,
    mut v___y_7729_: *mut LeanObject,
    mut v___y_7730_: *mut LeanObject,
    mut v___y_7731_: *mut LeanObject,
    mut v___y_7732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7733_: usize = 0;
    let mut v_i_boxed_7734_: usize = 0;
    let mut v_res_7735_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7733_ = lean_unbox_usize(v_sz_7725_);
    lean_dec(v_sz_7725_);
    v_i_boxed_7734_ = lean_unbox_usize(v_i_7726_);
    lean_dec(v_i_7726_);
    v_res_7735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v_snd_7723_, v_as_7724_, v_sz_boxed_7733_, v_i_boxed_7734_, v_b_7727_, v___y_7728_, v___y_7729_, v___y_7730_, v___y_7731_);
    lean_dec(v___y_7731_);
    lean_dec_ref(v___y_7730_);
    lean_dec(v___y_7729_);
    lean_dec_ref(v___y_7728_);
    lean_dec_ref(v_as_7724_);
    lean_dec_ref(v_snd_7723_);
    return v_res_7735_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut LeanObject = core::ptr::null_mut();
    v___x_7736_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3;
    v___x_7737_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0___closed__1;
    v___x_7738_ = l_Lean_Name_append(v___x_7737_, v___x_7736_);
    return v___x_7738_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7741_: *mut LeanObject = core::ptr::null_mut();
    v___x_7740_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__1;
    v___x_7741_ = l_Lean_stringToMessageData(v___x_7740_);
    return v___x_7741_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7744_: *mut LeanObject = core::ptr::null_mut();
    v___x_7743_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__3;
    v___x_7744_ = l_Lean_stringToMessageData(v___x_7743_);
    return v___x_7744_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut LeanObject = core::ptr::null_mut();
    v___x_7746_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__5;
    v___x_7747_ = l_Lean_stringToMessageData(v___x_7746_);
    return v___x_7747_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8()
-> *mut LeanObject {
    let mut v___x_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    v___x_7749_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__7;
    v___x_7750_ = l_Lean_stringToMessageData(v___x_7749_);
    return v___x_7750_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10()
-> *mut LeanObject {
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut LeanObject = core::ptr::null_mut();
    v___x_7752_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__9;
    v___x_7753_ = l_Lean_stringToMessageData(v___x_7752_);
    return v___x_7753_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(
    mut v___x_7754_: usize,
    mut v_a_7755_: *mut LeanObject,
    mut v_xs_7756_: *mut LeanObject,
    mut v___x_7757_: *mut LeanObject,
    mut v_a_7758_: *mut LeanObject,
    mut v_recArgInfos_7759_: *mut LeanObject,
    mut v___y_7760_: *mut LeanObject,
    mut v___y_7761_: *mut LeanObject,
    mut v___y_7762_: *mut LeanObject,
    mut v___y_7763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7774_: usize = 0;
    let mut v___x_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7780_: u8 = 0;
    let mut v___x_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7784_: u8 = 0;
    let mut v___x_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7795_: u8 = 0;
    let mut v_inheritedTraceOptions_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7798_: u8 = 0;
    let mut v___x_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7807_: u8 = 0;
    let mut v___x_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7811_: u8 = 0;
    let mut v___x_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7814_: usize = 0;
    let mut v___x_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7827_: u8 = 0;
    let mut v_fst_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7832_: u8 = 0;
    let mut v___x_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: u8 = 0;
    let mut v___x_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7842_: u8 = 0;
    let mut v___x_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7859_: usize = 0;
    let mut v___x_7860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7869_: u8 = 0;
    let mut v___x_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7873_: u8 = 0;
    let mut v_reuseFailAlloc_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7877_: u8 = 0;
    let mut v_isSharedCheck_7878_: u8 = 0;
    let mut v___x_7879_: u8 = 0;
    let mut v___x_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7890_: u8 = 0;
    let mut v___x_7892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7785_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__3;
                v___x_7812_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_7785_, v___y_7760_, v___y_7761_, v___y_7762_, v___y_7763_);
                v_a_7813_ = lean_ctor_get(v___x_7812_, 0);
                lean_inc(v_a_7813_);
                lean_dec_ref(v___x_7812_);
                v_sz_7814_ = lean_array_size(v_recArgInfos_7759_);
                lean_inc_ref(v_recArgInfos_7759_);
                v___x_7815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__2(v_sz_7814_, v___x_7754_, v_recArgInfos_7759_);
                v___x_7879_ = (lean_unbox(v_a_7813_) as u8);
                lean_dec(v_a_7813_);
                if v___x_7879_ == 0 {
                    v___y_7817_ = v___y_7760_;
                    v___y_7818_ = v___y_7761_;
                    v___y_7819_ = v___y_7762_;
                    v___y_7820_ = v___y_7763_;
                    state = 7;
                    continue;
                } else {
                    v___x_7880_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__10);
                    lean_inc_ref(v___x_7815_);
                    v___x_7881_ = lean_array_to_list(v___x_7815_);
                    v___x_7882_ = lean_box(0);
                    v___x_7883_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__0(v___x_7881_, v___x_7882_);
                    v___x_7884_ = l_Lean_MessageData_ofList(v___x_7883_);
                    v___x_7885_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7885_, 0, v___x_7880_);
                    lean_ctor_set(v___x_7885_, 1, v___x_7884_);
                    v___x_7886_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_7785_, v___x_7885_, v___y_7760_, v___y_7761_, v___y_7762_, v___y_7763_);
                    if lean_obj_tag(v___x_7886_) == 0 {
                        lean_dec_ref_known(v___x_7886_, 1);
                        v___y_7817_ = v___y_7760_;
                        v___y_7818_ = v___y_7761_;
                        v___y_7819_ = v___y_7762_;
                        v___y_7820_ = v___y_7763_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec_ref(v___x_7815_);
                        lean_dec_ref(v_recArgInfos_7759_);
                        lean_dec_ref(v_a_7758_);
                        lean_dec(v___x_7757_);
                        lean_dec_ref(v_xs_7756_);
                        lean_dec_ref(v_a_7755_);
                        v_a_7887_ = lean_ctor_get(v___x_7886_, 0);
                        v_isSharedCheck_7894_ = (!lean_is_exclusive(v___x_7886_)) as u8;
                        if v_isSharedCheck_7894_ == 0 {
                            v___x_7889_ = v___x_7886_;
                            v_isShared_7890_ = v_isSharedCheck_7894_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_7887_);
                            lean_dec(v___x_7886_);
                            v___x_7889_ = lean_box(0);
                            v_isShared_7890_ = v_isSharedCheck_7894_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7773_ = lean_box(0);
                v_sz_7774_ = lean_array_size(v___y_7768_);
                v___x_7775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__8(v___y_7767_, v___y_7768_, v_sz_7774_, v___x_7754_, v___x_7773_, v___y_7769_, v___y_7770_, v___y_7771_, v___y_7772_);
                lean_dec_ref(v___y_7768_);
                if lean_obj_tag(v___x_7775_) == 0 {
                    lean_dec_ref_known(v___x_7775_, 1);
                    v___x_7776_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v___y_7767_, v___y_7766_, v___y_7769_, v___y_7770_, v___y_7771_, v___y_7772_);
                    lean_dec_ref(v___y_7767_);
                    return v___x_7776_;
                } else {
                    lean_dec_ref(v___y_7767_);
                    lean_dec_ref(v___y_7766_);
                    v_a_7777_ = lean_ctor_get(v___x_7775_, 0);
                    v_isSharedCheck_7784_ = (!lean_is_exclusive(v___x_7775_)) as u8;
                    if v_isSharedCheck_7784_ == 0 {
                        v___x_7779_ = v___x_7775_;
                        v_isShared_7780_ = v_isSharedCheck_7784_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7777_);
                        lean_dec(v___x_7775_);
                        v___x_7779_ = lean_box(0);
                        v_isShared_7780_ = v_isSharedCheck_7784_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7780_ == 0 {
                    v___x_7782_ = v___x_7779_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7783_, 0, v_a_7777_);
                    v___x_7782_ = v_reuseFailAlloc_7783_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7782_;
            }
            4 => {
                v_options_7794_ = lean_ctor_get(v___y_7792_, 2);
                v_hasTrace_7795_ = lean_ctor_get_uint8(
                    v_options_7794_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_7795_ == 0 {
                    v___y_7766_ = v___y_7787_;
                    v___y_7767_ = v___y_7788_;
                    v___y_7768_ = v___y_7789_;
                    v___y_7769_ = v___y_7790_;
                    v___y_7770_ = v___y_7791_;
                    v___y_7771_ = v___y_7792_;
                    v___y_7772_ = v___y_7793_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_7796_ = lean_ctor_get(v___y_7792_, 13);
                    v___x_7797_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__0);
                    v___x_7798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_7796_,
                        v_options_7794_,
                        v___x_7797_,
                    );
                    if v___x_7798_ == 0 {
                        v___y_7766_ = v___y_7787_;
                        v___y_7767_ = v___y_7788_;
                        v___y_7768_ = v___y_7789_;
                        v___y_7769_ = v___y_7790_;
                        v___y_7770_ = v___y_7791_;
                        v___y_7771_ = v___y_7792_;
                        v___y_7772_ = v___y_7793_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7799_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__2);
                        lean_inc_ref(v___y_7789_);
                        v___x_7800_ = l_Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10(v___y_7789_);
                        v___x_7801_ = l_Lean_MessageData_ofFormat(v___x_7800_);
                        v___x_7802_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7802_, 0, v___x_7799_);
                        lean_ctor_set(v___x_7802_, 1, v___x_7801_);
                        v___x_7803_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_7785_, v___x_7802_, v___y_7790_, v___y_7791_, v___y_7792_, v___y_7793_);
                        if lean_obj_tag(v___x_7803_) == 0 {
                            lean_dec_ref_known(v___x_7803_, 1);
                            v___y_7766_ = v___y_7787_;
                            v___y_7767_ = v___y_7788_;
                            v___y_7768_ = v___y_7789_;
                            v___y_7769_ = v___y_7790_;
                            v___y_7770_ = v___y_7791_;
                            v___y_7771_ = v___y_7792_;
                            v___y_7772_ = v___y_7793_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v___y_7789_);
                            lean_dec_ref(v___y_7788_);
                            lean_dec_ref(v___y_7787_);
                            v_a_7804_ = lean_ctor_get(v___x_7803_, 0);
                            v_isSharedCheck_7811_ = (!lean_is_exclusive(v___x_7803_)) as u8;
                            if v_isSharedCheck_7811_ == 0 {
                                v___x_7806_ = v___x_7803_;
                                v_isShared_7807_ = v_isSharedCheck_7811_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_7804_);
                                lean_dec(v___x_7803_);
                                v___x_7806_ = lean_box(0);
                                v_isShared_7807_ = v_isSharedCheck_7811_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                if v_isShared_7807_ == 0 {
                    v___x_7809_ = v___x_7806_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7810_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7810_, 0, v_a_7804_);
                    v___x_7809_ = v_reuseFailAlloc_7810_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7809_;
            }
            7 => {
                lean_inc_ref(v_recArgInfos_7759_);
                v___x_7821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__3(v_sz_7814_, v___x_7754_, v_recArgInfos_7759_);
                lean_inc_ref(v_xs_7756_);
                v___x_7822_ = l_Lean_Elab_FixedParamPerms_erase(v_a_7755_, v_xs_7756_, v___x_7821_);
                v_snd_7823_ = lean_ctor_get(v___x_7822_, 1);
                v_fst_7824_ = lean_ctor_get(v___x_7822_, 0);
                v_isSharedCheck_7878_ = (!lean_is_exclusive(v___x_7822_)) as u8;
                if v_isSharedCheck_7878_ == 0 {
                    v___x_7826_ = v___x_7822_;
                    v_isShared_7827_ = v_isSharedCheck_7878_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_snd_7823_);
                    lean_inc(v_fst_7824_);
                    lean_dec(v___x_7822_);
                    v___x_7826_ = lean_box(0);
                    v_isShared_7827_ = v_isSharedCheck_7878_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_fst_7828_ = lean_ctor_get(v_snd_7823_, 0);
                v_snd_7829_ = lean_ctor_get(v_snd_7823_, 1);
                v_isSharedCheck_7877_ = (!lean_is_exclusive(v_snd_7823_)) as u8;
                if v_isSharedCheck_7877_ == 0 {
                    v___x_7831_ = v_snd_7823_;
                    v_isShared_7832_ = v_isSharedCheck_7877_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_snd_7829_);
                    lean_inc(v_fst_7828_);
                    lean_dec(v_snd_7823_);
                    v___x_7831_ = lean_box(0);
                    v_isShared_7832_ = v_isSharedCheck_7877_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_7833_ = lean_array_get_size(v_recArgInfos_7759_);
                v___x_7834_ = lean_mk_empty_array_with_capacity(v___x_7833_);
                v___x_7835_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_7824_, v_recArgInfos_7759_, v___x_7833_, v___x_7757_, v___x_7834_);
                lean_dec_ref(v_recArgInfos_7759_);
                lean_inc_ref(v___x_7835_);
                lean_inc(v_fst_7828_);
                v___f_7836_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__1___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_7836_, 0, v_a_7758_);
                lean_closure_set(v___f_7836_, 1, v_fst_7824_);
                lean_closure_set(v___f_7836_, 2, v_fst_7828_);
                lean_closure_set(v___f_7836_, 3, v___x_7835_);
                lean_closure_set(v___f_7836_, 4, v___x_7815_);
                v___x_7837_ = lean_array_get_size(v_fst_7828_);
                v___x_7838_ = lean_array_get_size(v_xs_7756_);
                v___x_7839_ = lean_nat_dec_eq(v___x_7837_, v___x_7838_);
                if v___x_7839_ == 0 {
                    v___x_7840_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lam__0(v___x_7785_, v___y_7817_, v___y_7818_, v___y_7819_, v___y_7820_);
                    v_a_7841_ = lean_ctor_get(v___x_7840_, 0);
                    lean_inc(v_a_7841_);
                    lean_dec_ref(v___x_7840_);
                    v___x_7842_ = (lean_unbox(v_a_7841_) as u8);
                    lean_dec(v_a_7841_);
                    if v___x_7842_ == 0 {
                        lean_del_object(v___x_7831_);
                        lean_dec(v_fst_7828_);
                        lean_del_object(v___x_7826_);
                        lean_dec_ref(v_xs_7756_);
                        v___y_7787_ = v___f_7836_;
                        v___y_7788_ = v_snd_7829_;
                        v___y_7789_ = v___x_7835_;
                        v___y_7790_ = v___y_7817_;
                        v___y_7791_ = v___y_7818_;
                        v___y_7792_ = v___y_7819_;
                        v___y_7793_ = v___y_7820_;
                        state = 4;
                        continue;
                    } else {
                        v___x_7843_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__4);
                        v___x_7844_ = lean_array_to_list(v_xs_7756_);
                        v___x_7845_ = lean_box(0);
                        v___x_7846_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_7844_, v___x_7845_);
                        v___x_7847_ = l_Lean_MessageData_ofList(v___x_7846_);
                        if v_isShared_7832_ == 0 {
                            lean_ctor_set_tag(v___x_7831_, 7);
                            lean_ctor_set(v___x_7831_, 1, v___x_7847_);
                            lean_ctor_set(v___x_7831_, 0, v___x_7843_);
                            v___x_7849_ = v___x_7831_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_7875_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7875_, 0, v___x_7843_);
                            lean_ctor_set(v_reuseFailAlloc_7875_, 1, v___x_7847_);
                            v___x_7849_ = v_reuseFailAlloc_7875_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_7835_);
                    lean_del_object(v___x_7831_);
                    lean_dec(v_fst_7828_);
                    lean_del_object(v___x_7826_);
                    lean_dec_ref(v_xs_7756_);
                    v___x_7876_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_snd_7829_, v___f_7836_, v___y_7817_, v___y_7818_, v___y_7819_, v___y_7820_);
                    lean_dec(v_snd_7829_);
                    return v___x_7876_;
                }
            }
            10 => {
                v___x_7850_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__6);
                if v_isShared_7827_ == 0 {
                    lean_ctor_set_tag(v___x_7826_, 7);
                    lean_ctor_set(v___x_7826_, 1, v___x_7850_);
                    lean_ctor_set(v___x_7826_, 0, v___x_7849_);
                    v___x_7852_ = v___x_7826_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7874_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7874_, 0, v___x_7849_);
                    lean_ctor_set(v_reuseFailAlloc_7874_, 1, v___x_7850_);
                    v___x_7852_ = v_reuseFailAlloc_7874_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_7853_ = lean_array_to_list(v_fst_7828_);
                v___x_7854_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_7853_, v___x_7845_);
                v___x_7855_ = l_Lean_MessageData_ofList(v___x_7854_);
                v___x_7856_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7856_, 0, v___x_7852_);
                lean_ctor_set(v___x_7856_, 1, v___x_7855_);
                v___x_7857_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8_once), _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___closed__8);
                v___x_7858_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7858_, 0, v___x_7856_);
                lean_ctor_set(v___x_7858_, 1, v___x_7857_);
                v_sz_7859_ = lean_array_size(v_snd_7829_);
                lean_inc(v_snd_7829_);
                v___x_7860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__11(v_sz_7859_, v___x_7754_, v_snd_7829_);
                v___x_7861_ = lean_array_to_list(v___x_7860_);
                v___x_7862_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__10(v___x_7861_, v___x_7845_);
                v___x_7863_ = l_Lean_MessageData_ofList(v___x_7862_);
                v___x_7864_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7864_, 0, v___x_7858_);
                lean_ctor_set(v___x_7864_, 1, v___x_7863_);
                v___x_7865_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__11(v___x_7785_, v___x_7864_, v___y_7817_, v___y_7818_, v___y_7819_, v___y_7820_);
                if lean_obj_tag(v___x_7865_) == 0 {
                    lean_dec_ref_known(v___x_7865_, 1);
                    v___y_7787_ = v___f_7836_;
                    v___y_7788_ = v_snd_7829_;
                    v___y_7789_ = v___x_7835_;
                    v___y_7790_ = v___y_7817_;
                    v___y_7791_ = v___y_7818_;
                    v___y_7792_ = v___y_7819_;
                    v___y_7793_ = v___y_7820_;
                    state = 4;
                    continue;
                } else {
                    lean_dec_ref(v___f_7836_);
                    lean_dec_ref(v___x_7835_);
                    lean_dec(v_snd_7829_);
                    v_a_7866_ = lean_ctor_get(v___x_7865_, 0);
                    v_isSharedCheck_7873_ = (!lean_is_exclusive(v___x_7865_)) as u8;
                    if v_isSharedCheck_7873_ == 0 {
                        v___x_7868_ = v___x_7865_;
                        v_isShared_7869_ = v_isSharedCheck_7873_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_7866_);
                        lean_dec(v___x_7865_);
                        v___x_7868_ = lean_box(0);
                        v_isShared_7869_ = v_isSharedCheck_7873_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_7869_ == 0 {
                    v___x_7871_ = v___x_7868_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7872_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7872_, 0, v_a_7866_);
                    v___x_7871_ = v_reuseFailAlloc_7872_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7871_;
            }
            14 => {
                if v_isShared_7890_ == 0 {
                    v___x_7892_ = v___x_7889_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7893_, 0, v_a_7887_);
                    v___x_7892_ = v_reuseFailAlloc_7893_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed(
    mut v___x_7895_: *mut LeanObject,
    mut v_a_7896_: *mut LeanObject,
    mut v_xs_7897_: *mut LeanObject,
    mut v___x_7898_: *mut LeanObject,
    mut v_a_7899_: *mut LeanObject,
    mut v_recArgInfos_7900_: *mut LeanObject,
    mut v___y_7901_: *mut LeanObject,
    mut v___y_7902_: *mut LeanObject,
    mut v___y_7903_: *mut LeanObject,
    mut v___y_7904_: *mut LeanObject,
    mut v___y_7905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_15815__boxed_7906_: usize = 0;
    let mut v_res_7907_: *mut LeanObject = core::ptr::null_mut();
    v___x_15815__boxed_7906_ = lean_unbox_usize(v___x_7895_);
    lean_dec(v___x_7895_);
    v_res_7907_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0(v___x_15815__boxed_7906_, v_a_7896_, v_xs_7897_, v___x_7898_, v_a_7899_, v_recArgInfos_7900_, v___y_7901_, v___y_7902_, v___y_7903_, v___y_7904_);
    lean_dec(v___y_7904_);
    lean_dec_ref(v___y_7903_);
    lean_dec(v___y_7902_);
    lean_dec_ref(v___y_7901_);
    return v_res_7907_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(
    mut v___x_7908_: *mut LeanObject,
    mut v_xs_7909_: *mut LeanObject,
    mut v_as_7910_: *mut LeanObject,
    mut v_i_7911_: *mut LeanObject,
    mut v_j_7912_: *mut LeanObject,
    mut v_bs_7913_: *mut LeanObject,
    mut v___y_7914_: *mut LeanObject,
    mut v___y_7915_: *mut LeanObject,
    mut v___y_7916_: *mut LeanObject,
    mut v___y_7917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_7919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7920_: u8 = 0;
    let mut v___x_7921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_7923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_7928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7936_: u8 = 0;
    let mut v___x_7938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7919_ = lean_unsigned_to_nat(0);
                v_isZero_7920_ = lean_nat_dec_eq(v_i_7911_, v_zero_7919_);
                if v_isZero_7920_ == 1 {
                    lean_dec(v_j_7912_);
                    lean_dec(v_i_7911_);
                    lean_dec_ref(v_xs_7909_);
                    v___x_7921_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7921_, 0, v_bs_7913_);
                    return v___x_7921_;
                } else {
                    v___x_7922_ = lean_array_fget_borrowed(v_as_7910_, v_j_7912_);
                    v_value_7923_ = lean_ctor_get(v___x_7922_, 7);
                    v___x_7924_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
                    v___x_7925_ = lean_array_get_borrowed(v___x_7924_, v___x_7908_, v_j_7912_);
                    lean_inc_ref(v_xs_7909_);
                    lean_inc_ref(v_value_7923_);
                    lean_inc(v___x_7925_);
                    v___x_7926_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(
                        v___x_7925_,
                        v_value_7923_,
                        v_xs_7909_,
                        v___y_7914_,
                        v___y_7915_,
                        v___y_7916_,
                        v___y_7917_,
                    );
                    if lean_obj_tag(v___x_7926_) == 0 {
                        v_a_7927_ = lean_ctor_get(v___x_7926_, 0);
                        lean_inc(v_a_7927_);
                        lean_dec_ref_known(v___x_7926_, 1);
                        v_one_7928_ = lean_unsigned_to_nat(1);
                        v_n_7929_ = lean_nat_sub(v_i_7911_, v_one_7928_);
                        lean_dec(v_i_7911_);
                        v___x_7930_ = lean_nat_add(v_j_7912_, v_one_7928_);
                        lean_dec(v_j_7912_);
                        v___x_7931_ = lean_array_push(v_bs_7913_, v_a_7927_);
                        v_i_7911_ = v_n_7929_;
                        v_j_7912_ = v___x_7930_;
                        v_bs_7913_ = v___x_7931_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_7913_);
                        lean_dec(v_j_7912_);
                        lean_dec(v_i_7911_);
                        lean_dec_ref(v_xs_7909_);
                        v_a_7933_ = lean_ctor_get(v___x_7926_, 0);
                        v_isSharedCheck_7940_ = (!lean_is_exclusive(v___x_7926_)) as u8;
                        if v_isSharedCheck_7940_ == 0 {
                            v___x_7935_ = v___x_7926_;
                            v_isShared_7936_ = v_isSharedCheck_7940_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7933_);
                            lean_dec(v___x_7926_);
                            v___x_7935_ = lean_box(0);
                            v_isShared_7936_ = v_isSharedCheck_7940_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7936_ == 0 {
                    v___x_7938_ = v___x_7935_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7939_, 0, v_a_7933_);
                    v___x_7938_ = v_reuseFailAlloc_7939_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg___boxed(
    mut v___x_7941_: *mut LeanObject,
    mut v_xs_7942_: *mut LeanObject,
    mut v_as_7943_: *mut LeanObject,
    mut v_i_7944_: *mut LeanObject,
    mut v_j_7945_: *mut LeanObject,
    mut v_bs_7946_: *mut LeanObject,
    mut v___y_7947_: *mut LeanObject,
    mut v___y_7948_: *mut LeanObject,
    mut v___y_7949_: *mut LeanObject,
    mut v___y_7950_: *mut LeanObject,
    mut v___y_7951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7952_: *mut LeanObject = core::ptr::null_mut();
    v_res_7952_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_7941_, v_xs_7942_, v_as_7943_, v_i_7944_, v_j_7945_, v_bs_7946_, v___y_7947_, v___y_7948_, v___y_7949_, v___y_7950_);
    lean_dec(v___y_7950_);
    lean_dec_ref(v___y_7949_);
    lean_dec(v___y_7948_);
    lean_dec_ref(v___y_7947_);
    lean_dec_ref(v_as_7943_);
    lean_dec_ref(v___x_7941_);
    return v_res_7952_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(
    mut v_a_7953_: *mut LeanObject,
    mut v_perms_7954_: *mut LeanObject,
    mut v___x_7955_: *mut LeanObject,
    mut v_fnNames_7956_: *mut LeanObject,
    mut v_a_7957_: *mut LeanObject,
    mut v_termMeasure_x3fs_7958_: *mut LeanObject,
    mut v___x_7959_: usize,
    mut v_xs_7960_: *mut LeanObject,
    mut v___y_7961_: *mut LeanObject,
    mut v___y_7962_: *mut LeanObject,
    mut v___y_7963_: *mut LeanObject,
    mut v___y_7964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7979_: u8 = 0;
    let mut v___x_7981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7983_: u8 = 0;
    let mut v_a_7984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7987_: u8 = 0;
    let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7966_ = lean_array_get_size(v_a_7953_);
                v___x_7967_ = lean_mk_empty_array_with_capacity(v___x_7966_);
                lean_inc(v___x_7955_);
                lean_inc_ref(v_xs_7960_);
                v___x_7968_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v_perms_7954_, v_xs_7960_, v_a_7953_, v___x_7966_, v___x_7955_, v___x_7967_, v___y_7961_, v___y_7962_, v___y_7963_, v___y_7964_);
                if lean_obj_tag(v___x_7968_) == 0 {
                    v_a_7969_ = lean_ctor_get(v___x_7968_, 0);
                    lean_inc_n(v_a_7969_, 2);
                    lean_dec_ref_known(v___x_7968_, 1);
                    lean_inc_ref(v_xs_7960_);
                    lean_inc_ref(v_a_7957_);
                    lean_inc_ref(v_fnNames_7956_);
                    v___x_7970_ = lean_alloc_closure(
                        l_Lean_Elab_Structural_findRecArgCandidates___boxed
                            as *mut core::ffi::c_void,
                        10,
                        5,
                    );
                    lean_closure_set(v___x_7970_, 0, v_fnNames_7956_);
                    lean_closure_set(v___x_7970_, 1, v_a_7957_);
                    lean_closure_set(v___x_7970_, 2, v_xs_7960_);
                    lean_closure_set(v___x_7970_, 3, v_a_7969_);
                    lean_closure_set(v___x_7970_, 4, v_termMeasure_x3fs_7958_);
                    lean_inc_ref(v_a_7953_);
                    v___x_7971_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_7953_, v___x_7970_, v___y_7961_, v___y_7962_, v___y_7963_, v___y_7964_);
                    if lean_obj_tag(v___x_7971_) == 0 {
                        v_a_7972_ = lean_ctor_get(v___x_7971_, 0);
                        lean_inc(v_a_7972_);
                        lean_dec_ref_known(v___x_7971_, 1);
                        v___x_7973_ = lean_box_usize(v___x_7959_);
                        lean_inc_ref(v_xs_7960_);
                        v___f_7974_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                        lean_closure_set(v___f_7974_, 0, v___x_7973_);
                        lean_closure_set(v___f_7974_, 1, v_a_7957_);
                        lean_closure_set(v___f_7974_, 2, v_xs_7960_);
                        lean_closure_set(v___f_7974_, 3, v___x_7955_);
                        lean_closure_set(v___f_7974_, 4, v_a_7953_);
                        v___x_7975_ = l_Lean_Elab_Structural_tryCandidates___redArg(
                            v_fnNames_7956_,
                            v_xs_7960_,
                            v_a_7969_,
                            v_a_7972_,
                            v___f_7974_,
                            v___y_7961_,
                            v___y_7962_,
                            v___y_7963_,
                            v___y_7964_,
                        );
                        lean_dec_ref(v_fnNames_7956_);
                        return v___x_7975_;
                    } else {
                        lean_dec(v_a_7969_);
                        lean_dec_ref(v_xs_7960_);
                        lean_dec_ref(v_a_7957_);
                        lean_dec_ref(v_fnNames_7956_);
                        lean_dec(v___x_7955_);
                        lean_dec_ref(v_a_7953_);
                        v_a_7976_ = lean_ctor_get(v___x_7971_, 0);
                        v_isSharedCheck_7983_ = (!lean_is_exclusive(v___x_7971_)) as u8;
                        if v_isSharedCheck_7983_ == 0 {
                            v___x_7978_ = v___x_7971_;
                            v_isShared_7979_ = v_isSharedCheck_7983_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7976_);
                            lean_dec(v___x_7971_);
                            v___x_7978_ = lean_box(0);
                            v_isShared_7979_ = v_isSharedCheck_7983_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_xs_7960_);
                    lean_dec_ref(v_termMeasure_x3fs_7958_);
                    lean_dec_ref(v_a_7957_);
                    lean_dec_ref(v_fnNames_7956_);
                    lean_dec(v___x_7955_);
                    lean_dec_ref(v_a_7953_);
                    v_a_7984_ = lean_ctor_get(v___x_7968_, 0);
                    v_isSharedCheck_7991_ = (!lean_is_exclusive(v___x_7968_)) as u8;
                    if v_isSharedCheck_7991_ == 0 {
                        v___x_7986_ = v___x_7968_;
                        v_isShared_7987_ = v_isSharedCheck_7991_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7984_);
                        lean_dec(v___x_7968_);
                        v___x_7986_ = lean_box(0);
                        v_isShared_7987_ = v_isSharedCheck_7991_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7979_ == 0 {
                    v___x_7981_ = v___x_7978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7982_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7982_, 0, v_a_7976_);
                    v___x_7981_ = v_reuseFailAlloc_7982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7981_;
            }
            3 => {
                if v_isShared_7987_ == 0 {
                    v___x_7989_ = v___x_7986_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7990_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7990_, 0, v_a_7984_);
                    v___x_7989_ = v_reuseFailAlloc_7990_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed(
    mut v_a_7992_: *mut LeanObject,
    mut v_perms_7993_: *mut LeanObject,
    mut v___x_7994_: *mut LeanObject,
    mut v_fnNames_7995_: *mut LeanObject,
    mut v_a_7996_: *mut LeanObject,
    mut v_termMeasure_x3fs_7997_: *mut LeanObject,
    mut v___x_7998_: *mut LeanObject,
    mut v_xs_7999_: *mut LeanObject,
    mut v___y_8000_: *mut LeanObject,
    mut v___y_8001_: *mut LeanObject,
    mut v___y_8002_: *mut LeanObject,
    mut v___y_8003_: *mut LeanObject,
    mut v___y_8004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16172__boxed_8005_: usize = 0;
    let mut v_res_8006_: *mut LeanObject = core::ptr::null_mut();
    v___x_16172__boxed_8005_ = lean_unbox_usize(v___x_7998_);
    lean_dec(v___x_7998_);
    v_res_8006_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2(v_a_7992_, v_perms_7993_, v___x_7994_, v_fnNames_7995_, v_a_7996_, v_termMeasure_x3fs_7997_, v___x_16172__boxed_8005_, v_xs_7999_, v___y_8000_, v___y_8001_, v___y_8002_, v___y_8003_);
    lean_dec(v___y_8003_);
    lean_dec_ref(v___y_8002_);
    lean_dec(v___y_8001_);
    lean_dec_ref(v___y_8000_);
    lean_dec_ref(v_perms_7993_);
    return v_res_8006_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(
    mut v_sz_8007_: usize,
    mut v_i_8008_: usize,
    mut v_bs_8009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8010_: u8 = 0;
    let mut v_v_8011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8015_: usize = 0;
    let mut v___x_8016_: usize = 0;
    let mut v___x_8017_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8010_ = lean_usize_dec_lt(v_i_8008_, v_sz_8007_);
                if v___x_8010_ == 0 {
                    return v_bs_8009_;
                } else {
                    v_v_8011_ = lean_array_uget_borrowed(v_bs_8009_, v_i_8008_);
                    v_declName_8012_ = lean_ctor_get(v_v_8011_, 3);
                    lean_inc(v_declName_8012_);
                    v___x_8013_ = lean_unsigned_to_nat(0);
                    v_bs_x27_8014_ = lean_array_uset(v_bs_8009_, v_i_8008_, v___x_8013_);
                    v___x_8015_ = 1usize;
                    v___x_8016_ = lean_usize_add(v_i_8008_, v___x_8015_);
                    v___x_8017_ = lean_array_uset(v_bs_x27_8014_, v_i_8008_, v_declName_8012_);
                    v_i_8008_ = v___x_8016_;
                    v_bs_8009_ = v___x_8017_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0___boxed(
    mut v_sz_8019_: *mut LeanObject,
    mut v_i_8020_: *mut LeanObject,
    mut v_bs_8021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8022_: usize = 0;
    let mut v_i_boxed_8023_: usize = 0;
    let mut v_res_8024_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8022_ = lean_unbox_usize(v_sz_8019_);
    lean_dec(v_sz_8019_);
    v_i_boxed_8023_ = lean_unbox_usize(v_i_8020_);
    lean_dec(v_i_8020_);
    v_res_8024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_boxed_8022_, v_i_boxed_8023_, v_bs_8021_);
    return v_res_8024_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(
    mut v_fnNames_8025_: *mut LeanObject,
    mut v_numSectionVars_8026_: *mut LeanObject,
    mut v_sz_8027_: usize,
    mut v_i_8028_: usize,
    mut v_bs_8029_: *mut LeanObject,
    mut v___y_8030_: *mut LeanObject,
    mut v___y_8031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8033_: u8 = 0;
    let mut v___x_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_8035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_8037_: u8 = 0;
    let mut v_levelParams_8038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_8040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_8042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_8044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termination_8045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8048_: u8 = 0;
    let mut v___x_8049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8055_: usize = 0;
    let mut v___x_8056_: usize = 0;
    let mut v___x_8057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8063_: u8 = 0;
    let mut v___x_8065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8067_: u8 = 0;
    let mut v_isSharedCheck_8068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8033_ = lean_usize_dec_lt(v_i_8028_, v_sz_8027_);
                if v___x_8033_ == 0 {
                    lean_dec(v_numSectionVars_8026_);
                    lean_dec_ref(v_fnNames_8025_);
                    v___x_8034_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8034_, 0, v_bs_8029_);
                    return v___x_8034_;
                } else {
                    v_v_8035_ = lean_array_uget(v_bs_8029_, v_i_8028_);
                    v_ref_8036_ = lean_ctor_get(v_v_8035_, 0);
                    v_kind_8037_ = lean_ctor_get_uint8(
                        v_v_8035_,
                        (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                    );
                    v_levelParams_8038_ = lean_ctor_get(v_v_8035_, 1);
                    v_modifiers_8039_ = lean_ctor_get(v_v_8035_, 2);
                    v_declName_8040_ = lean_ctor_get(v_v_8035_, 3);
                    v_binders_8041_ = lean_ctor_get(v_v_8035_, 4);
                    v_numSectionVars_8042_ = lean_ctor_get(v_v_8035_, 5);
                    v_type_8043_ = lean_ctor_get(v_v_8035_, 6);
                    v_value_8044_ = lean_ctor_get(v_v_8035_, 7);
                    v_termination_8045_ = lean_ctor_get(v_v_8035_, 8);
                    v_isSharedCheck_8068_ = (!lean_is_exclusive(v_v_8035_)) as u8;
                    if v_isSharedCheck_8068_ == 0 {
                        v___x_8047_ = v_v_8035_;
                        v_isShared_8048_ = v_isSharedCheck_8068_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_termination_8045_);
                        lean_inc(v_value_8044_);
                        lean_inc(v_type_8043_);
                        lean_inc(v_numSectionVars_8042_);
                        lean_inc(v_binders_8041_);
                        lean_inc(v_declName_8040_);
                        lean_inc(v_modifiers_8039_);
                        lean_inc(v_levelParams_8038_);
                        lean_inc(v_ref_8036_);
                        lean_dec(v_v_8035_);
                        v___x_8047_ = lean_box(0);
                        v_isShared_8048_ = v_isSharedCheck_8068_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_numSectionVars_8026_);
                lean_inc_ref(v_fnNames_8025_);
                v___x_8049_ = l_Lean_Elab_Structural_preprocess(
                    v_value_8044_,
                    v_fnNames_8025_,
                    v_numSectionVars_8026_,
                    v___y_8030_,
                    v___y_8031_,
                );
                if lean_obj_tag(v___x_8049_) == 0 {
                    v_a_8050_ = lean_ctor_get(v___x_8049_, 0);
                    lean_inc(v_a_8050_);
                    lean_dec_ref_known(v___x_8049_, 1);
                    v___x_8051_ = lean_unsigned_to_nat(0);
                    v_bs_x27_8052_ = lean_array_uset(v_bs_8029_, v_i_8028_, v___x_8051_);
                    if v_isShared_8048_ == 0 {
                        lean_ctor_set(v___x_8047_, 7, v_a_8050_);
                        v___x_8054_ = v___x_8047_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8059_ = lean_alloc_ctor(0, 9, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8059_, 0, v_ref_8036_);
                        lean_ctor_set(v_reuseFailAlloc_8059_, 1, v_levelParams_8038_);
                        lean_ctor_set(v_reuseFailAlloc_8059_, 2, v_modifiers_8039_);
                        lean_ctor_set(v_reuseFailAlloc_8059_, 3, v_declName_8040_);
                        lean_ctor_set(v_reuseFailAlloc_8059_, 4, v_binders_8041_);
                        lean_ctor_set(v_reuseFailAlloc_8059_, 5, v_numSectionVars_8042_);
                        lean_ctor_set(v_reuseFailAlloc_8059_, 6, v_type_8043_);
                        lean_ctor_set(v_reuseFailAlloc_8059_, 7, v_a_8050_);
                        lean_ctor_set(v_reuseFailAlloc_8059_, 8, v_termination_8045_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_8059_,
                            (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                            v_kind_8037_,
                        );
                        v___x_8054_ = v_reuseFailAlloc_8059_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8047_);
                    lean_dec_ref(v_termination_8045_);
                    lean_dec_ref(v_type_8043_);
                    lean_dec(v_numSectionVars_8042_);
                    lean_dec(v_binders_8041_);
                    lean_dec(v_declName_8040_);
                    lean_dec_ref(v_modifiers_8039_);
                    lean_dec(v_levelParams_8038_);
                    lean_dec(v_ref_8036_);
                    lean_dec_ref(v_bs_8029_);
                    lean_dec(v_numSectionVars_8026_);
                    lean_dec_ref(v_fnNames_8025_);
                    v_a_8060_ = lean_ctor_get(v___x_8049_, 0);
                    v_isSharedCheck_8067_ = (!lean_is_exclusive(v___x_8049_)) as u8;
                    if v_isSharedCheck_8067_ == 0 {
                        v___x_8062_ = v___x_8049_;
                        v_isShared_8063_ = v_isSharedCheck_8067_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8060_);
                        lean_dec(v___x_8049_);
                        v___x_8062_ = lean_box(0);
                        v_isShared_8063_ = v_isSharedCheck_8067_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8055_ = 1usize;
                v___x_8056_ = lean_usize_add(v_i_8028_, v___x_8055_);
                v___x_8057_ = lean_array_uset(v_bs_x27_8052_, v_i_8028_, v___x_8054_);
                v_i_8028_ = v___x_8056_;
                v_bs_8029_ = v___x_8057_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_8063_ == 0 {
                    v___x_8065_ = v___x_8062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8066_, 0, v_a_8060_);
                    v___x_8065_ = v_reuseFailAlloc_8066_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg___boxed(
    mut v_fnNames_8069_: *mut LeanObject,
    mut v_numSectionVars_8070_: *mut LeanObject,
    mut v_sz_8071_: *mut LeanObject,
    mut v_i_8072_: *mut LeanObject,
    mut v_bs_8073_: *mut LeanObject,
    mut v___y_8074_: *mut LeanObject,
    mut v___y_8075_: *mut LeanObject,
    mut v___y_8076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8077_: usize = 0;
    let mut v_i_boxed_8078_: usize = 0;
    let mut v_res_8079_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8077_ = lean_unbox_usize(v_sz_8071_);
    lean_dec(v_sz_8071_);
    v_i_boxed_8078_ = lean_unbox_usize(v_i_8072_);
    lean_dec(v_i_8072_);
    v_res_8079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_8069_, v_numSectionVars_8070_, v_sz_boxed_8077_, v_i_boxed_8078_, v_bs_8073_, v___y_8074_, v___y_8075_);
    lean_dec(v___y_8075_);
    lean_dec_ref(v___y_8074_);
    return v_res_8079_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(
    mut v_fnNames_8080_: *mut LeanObject,
    mut v_numSectionVars_8081_: *mut LeanObject,
    mut v_sz_8082_: usize,
    mut v_i_8083_: usize,
    mut v_bs_8084_: *mut LeanObject,
    mut v___y_8085_: *mut LeanObject,
    mut v___y_8086_: *mut LeanObject,
    mut v___y_8087_: *mut LeanObject,
    mut v___y_8088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8090_: *mut LeanObject = core::ptr::null_mut();
    v___x_8090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___redArg(v_fnNames_8080_, v_numSectionVars_8081_, v_sz_8082_, v_i_8083_, v_bs_8084_, v___y_8087_, v___y_8088_);
    return v___x_8090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed(
    mut v_fnNames_8091_: *mut LeanObject,
    mut v_numSectionVars_8092_: *mut LeanObject,
    mut v_sz_8093_: *mut LeanObject,
    mut v_i_8094_: *mut LeanObject,
    mut v_bs_8095_: *mut LeanObject,
    mut v___y_8096_: *mut LeanObject,
    mut v___y_8097_: *mut LeanObject,
    mut v___y_8098_: *mut LeanObject,
    mut v___y_8099_: *mut LeanObject,
    mut v___y_8100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8101_: usize = 0;
    let mut v_i_boxed_8102_: usize = 0;
    let mut v_res_8103_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8101_ = lean_unbox_usize(v_sz_8093_);
    lean_dec(v_sz_8093_);
    v_i_boxed_8102_ = lean_unbox_usize(v_i_8094_);
    lean_dec(v_i_8094_);
    v_res_8103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1(v_fnNames_8091_, v_numSectionVars_8092_, v_sz_boxed_8101_, v_i_boxed_8102_, v_bs_8095_, v___y_8096_, v___y_8097_, v___y_8098_, v___y_8099_);
    lean_dec(v___y_8099_);
    lean_dec_ref(v___y_8098_);
    lean_dec(v___y_8097_);
    lean_dec_ref(v___y_8096_);
    return v_res_8103_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(
    mut v_preDefs_8104_: *mut LeanObject,
    mut v_termMeasure_x3fs_8105_: *mut LeanObject,
    mut v_a_8106_: *mut LeanObject,
    mut v_a_8107_: *mut LeanObject,
    mut v_a_8108_: *mut LeanObject,
    mut v_a_8109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8115_: usize = 0;
    let mut v___x_8116_: usize = 0;
    let mut v_fnNames_8117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perms_8126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8137_: u8 = 0;
    let mut v___x_8139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8141_: u8 = 0;
    let mut v_a_8142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8145_: u8 = 0;
    let mut v___x_8147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8111_ = l_Lean_Elab_instInhabitedPreDefinition_default;
                v___x_8112_ = lean_unsigned_to_nat(0);
                v___x_8113_ = lean_array_get_borrowed(v___x_8111_, v_preDefs_8104_, v___x_8112_);
                v_numSectionVars_8114_ = lean_ctor_get(v___x_8113_, 5);
                v_sz_8115_ = lean_array_size(v_preDefs_8104_);
                v___x_8116_ = 0usize;
                lean_inc_ref_n(v_preDefs_8104_, 2);
                v_fnNames_8117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_8115_, v___x_8116_, v_preDefs_8104_);
                v___x_8118_ = lean_box_usize(v_sz_8115_);
                v___x_8119_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1;
                lean_inc(v_numSectionVars_8114_);
                lean_inc_ref(v_fnNames_8117_);
                v___x_8120_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__1___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___x_8120_, 0, v_fnNames_8117_);
                lean_closure_set(v___x_8120_, 1, v_numSectionVars_8114_);
                lean_closure_set(v___x_8120_, 2, v___x_8118_);
                lean_closure_set(v___x_8120_, 3, v___x_8119_);
                lean_closure_set(v___x_8120_, 4, v_preDefs_8104_);
                v___x_8121_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_preDefs_8104_, v___x_8120_, v_a_8106_, v_a_8107_, v_a_8108_, v_a_8109_);
                if lean_obj_tag(v___x_8121_) == 0 {
                    v_a_8122_ = lean_ctor_get(v___x_8121_, 0);
                    lean_inc_n(v_a_8122_, 3);
                    lean_dec_ref_known(v___x_8121_, 1);
                    v___x_8123_ = lean_alloc_closure(
                        l_Lean_Elab_getFixedParamPerms___boxed as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    lean_closure_set(v___x_8123_, 0, v_a_8122_);
                    v___x_8124_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg(v_a_8122_, v___x_8123_, v_a_8106_, v_a_8107_, v_a_8108_, v_a_8109_);
                    if lean_obj_tag(v___x_8124_) == 0 {
                        v_a_8125_ = lean_ctor_get(v___x_8124_, 0);
                        lean_inc(v_a_8125_);
                        lean_dec_ref_known(v___x_8124_, 1);
                        v_perms_8126_ = lean_ctor_get(v_a_8125_, 1);
                        lean_inc_ref_n(v_perms_8126_, 2);
                        v___x_8127_ = lean_array_get_borrowed(v___x_8111_, v_a_8122_, v___x_8112_);
                        v_type_8128_ = lean_ctor_get(v___x_8127_, 6);
                        lean_inc_ref(v_type_8128_);
                        v___x_8129_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__8___redArg___closed__0);
                        v___x_8130_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_withRecFunsAsAxioms___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__12___redArg___boxed__const__1;
                        v___f_8131_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lam__2___boxed as *mut core::ffi::c_void, 13, 7);
                        lean_closure_set(v___f_8131_, 0, v_a_8122_);
                        lean_closure_set(v___f_8131_, 1, v_perms_8126_);
                        lean_closure_set(v___f_8131_, 2, v___x_8112_);
                        lean_closure_set(v___f_8131_, 3, v_fnNames_8117_);
                        lean_closure_set(v___f_8131_, 4, v_a_8125_);
                        lean_closure_set(v___f_8131_, 5, v_termMeasure_x3fs_8105_);
                        lean_closure_set(v___f_8131_, 6, v___x_8130_);
                        v___x_8132_ = lean_array_get(v___x_8129_, v_perms_8126_, v___x_8112_);
                        lean_dec_ref(v_perms_8126_);
                        v___x_8133_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__13___redArg(v___x_8132_, v_type_8128_, v___f_8131_, v_a_8106_, v_a_8107_, v_a_8108_, v_a_8109_);
                        return v___x_8133_;
                    } else {
                        lean_dec(v_a_8122_);
                        lean_dec_ref(v_fnNames_8117_);
                        lean_dec_ref(v_termMeasure_x3fs_8105_);
                        v_a_8134_ = lean_ctor_get(v___x_8124_, 0);
                        v_isSharedCheck_8141_ = (!lean_is_exclusive(v___x_8124_)) as u8;
                        if v_isSharedCheck_8141_ == 0 {
                            v___x_8136_ = v___x_8124_;
                            v_isShared_8137_ = v_isSharedCheck_8141_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8134_);
                            lean_dec(v___x_8124_);
                            v___x_8136_ = lean_box(0);
                            v_isShared_8137_ = v_isSharedCheck_8141_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_fnNames_8117_);
                    lean_dec_ref(v_termMeasure_x3fs_8105_);
                    v_a_8142_ = lean_ctor_get(v___x_8121_, 0);
                    v_isSharedCheck_8149_ = (!lean_is_exclusive(v___x_8121_)) as u8;
                    if v_isSharedCheck_8149_ == 0 {
                        v___x_8144_ = v___x_8121_;
                        v_isShared_8145_ = v_isSharedCheck_8149_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8142_);
                        lean_dec(v___x_8121_);
                        v___x_8144_ = lean_box(0);
                        v_isShared_8145_ = v_isSharedCheck_8149_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8137_ == 0 {
                    v___x_8139_ = v___x_8136_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8140_, 0, v_a_8134_);
                    v___x_8139_ = v_reuseFailAlloc_8140_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8139_;
            }
            3 => {
                if v_isShared_8145_ == 0 {
                    v___x_8147_ = v___x_8144_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8148_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8148_, 0, v_a_8142_);
                    v___x_8147_ = v_reuseFailAlloc_8148_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed(
    mut v_preDefs_8150_: *mut LeanObject,
    mut v_termMeasure_x3fs_8151_: *mut LeanObject,
    mut v_a_8152_: *mut LeanObject,
    mut v_a_8153_: *mut LeanObject,
    mut v_a_8154_: *mut LeanObject,
    mut v_a_8155_: *mut LeanObject,
    mut v_a_8156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8157_: *mut LeanObject = core::ptr::null_mut();
    v_res_8157_ =
        l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(
            v_preDefs_8150_,
            v_termMeasure_x3fs_8151_,
            v_a_8152_,
            v_a_8153_,
            v_a_8154_,
            v_a_8155_,
        );
    lean_dec(v_a_8155_);
    lean_dec_ref(v_a_8154_);
    lean_dec(v_a_8153_);
    lean_dec_ref(v_a_8152_);
    return v_res_8157_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(
    mut v_fst_8158_: *mut LeanObject,
    mut v_as_8159_: *mut LeanObject,
    mut v_i_8160_: *mut LeanObject,
    mut v_j_8161_: *mut LeanObject,
    mut v_inv_8162_: *mut LeanObject,
    mut v_bs_8163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8164_: *mut LeanObject = core::ptr::null_mut();
    v___x_8164_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___redArg(v_fst_8158_, v_as_8159_, v_i_8160_, v_j_8161_, v_bs_8163_);
    return v___x_8164_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4___boxed(
    mut v_fst_8165_: *mut LeanObject,
    mut v_as_8166_: *mut LeanObject,
    mut v_i_8167_: *mut LeanObject,
    mut v_j_8168_: *mut LeanObject,
    mut v_inv_8169_: *mut LeanObject,
    mut v_bs_8170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8171_: *mut LeanObject = core::ptr::null_mut();
    v_res_8171_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__4(v_fst_8165_, v_as_8166_, v_i_8167_, v_j_8168_, v_inv_8169_, v_bs_8170_);
    lean_dec_ref(v_as_8166_);
    lean_dec_ref(v_fst_8165_);
    return v_res_8171_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(
    mut v_00_u03b1_8172_: *mut LeanObject,
    mut v_lctx_8173_: *mut LeanObject,
    mut v_localInsts_8174_: *mut LeanObject,
    mut v_x_8175_: *mut LeanObject,
    mut v___y_8176_: *mut LeanObject,
    mut v___y_8177_: *mut LeanObject,
    mut v___y_8178_: *mut LeanObject,
    mut v___y_8179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8181_: *mut LeanObject = core::ptr::null_mut();
    v___x_8181_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___redArg(v_lctx_8173_, v_localInsts_8174_, v_x_8175_, v___y_8176_, v___y_8177_, v___y_8178_, v___y_8179_);
    return v___x_8181_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10___boxed(
    mut v_00_u03b1_8182_: *mut LeanObject,
    mut v_lctx_8183_: *mut LeanObject,
    mut v_localInsts_8184_: *mut LeanObject,
    mut v_x_8185_: *mut LeanObject,
    mut v___y_8186_: *mut LeanObject,
    mut v___y_8187_: *mut LeanObject,
    mut v___y_8188_: *mut LeanObject,
    mut v___y_8189_: *mut LeanObject,
    mut v___y_8190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8191_: *mut LeanObject = core::ptr::null_mut();
    v_res_8191_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9_spec__10(v_00_u03b1_8182_, v_lctx_8183_, v_localInsts_8184_, v_x_8185_, v___y_8186_, v___y_8187_, v___y_8188_, v___y_8189_);
    lean_dec(v___y_8189_);
    lean_dec_ref(v___y_8188_);
    lean_dec(v___y_8187_);
    lean_dec_ref(v___y_8186_);
    return v_res_8191_;
}
pub unsafe fn l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(
    mut v_00_u03b1_8192_: *mut LeanObject,
    mut v_fvarIds_8193_: *mut LeanObject,
    mut v_k_8194_: *mut LeanObject,
    mut v___y_8195_: *mut LeanObject,
    mut v___y_8196_: *mut LeanObject,
    mut v___y_8197_: *mut LeanObject,
    mut v___y_8198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8200_: *mut LeanObject = core::ptr::null_mut();
    v___x_8200_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___redArg(v_fvarIds_8193_, v_k_8194_, v___y_8195_, v___y_8196_, v___y_8197_, v___y_8198_);
    return v___x_8200_;
}
pub unsafe fn l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9___boxed(
    mut v_00_u03b1_8201_: *mut LeanObject,
    mut v_fvarIds_8202_: *mut LeanObject,
    mut v_k_8203_: *mut LeanObject,
    mut v___y_8204_: *mut LeanObject,
    mut v___y_8205_: *mut LeanObject,
    mut v___y_8206_: *mut LeanObject,
    mut v___y_8207_: *mut LeanObject,
    mut v___y_8208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8209_: *mut LeanObject = core::ptr::null_mut();
    v_res_8209_ = l_Lean_Meta_withErasedFVars___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__9(v_00_u03b1_8201_, v_fvarIds_8202_, v_k_8203_, v___y_8204_, v___y_8205_, v___y_8206_, v___y_8207_);
    lean_dec(v___y_8207_);
    lean_dec_ref(v___y_8206_);
    lean_dec(v___y_8205_);
    lean_dec_ref(v___y_8204_);
    lean_dec_ref(v_fvarIds_8202_);
    return v_res_8209_;
}
pub unsafe fn l_Nat_cast___at___00Array_repr___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__10_spec__15(
    mut v_a_8210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8211_: *mut LeanObject = core::ptr::null_mut();
    v___x_8211_ = lean_nat_to_int(v_a_8210_);
    return v___x_8211_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(
    mut v___x_8212_: *mut LeanObject,
    mut v_xs_8213_: *mut LeanObject,
    mut v_as_8214_: *mut LeanObject,
    mut v_i_8215_: *mut LeanObject,
    mut v_j_8216_: *mut LeanObject,
    mut v_inv_8217_: *mut LeanObject,
    mut v_bs_8218_: *mut LeanObject,
    mut v___y_8219_: *mut LeanObject,
    mut v___y_8220_: *mut LeanObject,
    mut v___y_8221_: *mut LeanObject,
    mut v___y_8222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8224_: *mut LeanObject = core::ptr::null_mut();
    v___x_8224_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___redArg(v___x_8212_, v_xs_8213_, v_as_8214_, v_i_8215_, v_j_8216_, v_bs_8218_, v___y_8219_, v___y_8220_, v___y_8221_, v___y_8222_);
    return v___x_8224_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12___boxed(
    mut v___x_8225_: *mut LeanObject,
    mut v_xs_8226_: *mut LeanObject,
    mut v_as_8227_: *mut LeanObject,
    mut v_i_8228_: *mut LeanObject,
    mut v_j_8229_: *mut LeanObject,
    mut v_inv_8230_: *mut LeanObject,
    mut v_bs_8231_: *mut LeanObject,
    mut v___y_8232_: *mut LeanObject,
    mut v___y_8233_: *mut LeanObject,
    mut v___y_8234_: *mut LeanObject,
    mut v___y_8235_: *mut LeanObject,
    mut v___y_8236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8237_: *mut LeanObject = core::ptr::null_mut();
    v_res_8237_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__12(v___x_8225_, v_xs_8226_, v_as_8227_, v_i_8228_, v_j_8229_, v_inv_8230_, v_bs_8231_, v___y_8232_, v___y_8233_, v___y_8234_, v___y_8235_);
    lean_dec(v___y_8235_);
    lean_dec_ref(v___y_8234_);
    lean_dec(v___y_8233_);
    lean_dec_ref(v___y_8232_);
    lean_dec_ref(v_as_8227_);
    lean_dec_ref(v___x_8225_);
    return v_res_8237_;
}
pub unsafe fn l_Lean_Elab_Structural_reportTermMeasure___lam__0(
    mut v___x_8238_: *mut LeanObject,
    mut v_recArgPos_8239_: *mut LeanObject,
    mut v_xs_8240_: *mut LeanObject,
    mut v_x_8241_: *mut LeanObject,
    mut v___y_8242_: *mut LeanObject,
    mut v___y_8243_: *mut LeanObject,
    mut v___y_8244_: *mut LeanObject,
    mut v___y_8245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8248_: u8 = 0;
    let mut v___x_8249_: u8 = 0;
    let mut v___x_8250_: u8 = 0;
    let mut v___x_8251_: *mut LeanObject = core::ptr::null_mut();
    v___x_8247_ = lean_array_get_borrowed(v___x_8238_, v_xs_8240_, v_recArgPos_8239_);
    v___x_8248_ = 0;
    v___x_8249_ = 1;
    v___x_8250_ = 1;
    lean_inc(v___x_8247_);
    v___x_8251_ = l_Lean_Meta_mkLambdaFVars(
        v_xs_8240_,
        v___x_8247_,
        v___x_8248_,
        v___x_8249_,
        v___x_8248_,
        v___x_8249_,
        v___x_8250_,
        v___y_8242_,
        v___y_8243_,
        v___y_8244_,
        v___y_8245_,
    );
    return v___x_8251_;
}
pub unsafe fn l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed(
    mut v___x_8252_: *mut LeanObject,
    mut v_recArgPos_8253_: *mut LeanObject,
    mut v_xs_8254_: *mut LeanObject,
    mut v_x_8255_: *mut LeanObject,
    mut v___y_8256_: *mut LeanObject,
    mut v___y_8257_: *mut LeanObject,
    mut v___y_8258_: *mut LeanObject,
    mut v___y_8259_: *mut LeanObject,
    mut v___y_8260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8261_: *mut LeanObject = core::ptr::null_mut();
    v_res_8261_ = l_Lean_Elab_Structural_reportTermMeasure___lam__0(
        v___x_8252_,
        v_recArgPos_8253_,
        v_xs_8254_,
        v_x_8255_,
        v___y_8256_,
        v___y_8257_,
        v___y_8258_,
        v___y_8259_,
    );
    lean_dec(v___y_8259_);
    lean_dec_ref(v___y_8258_);
    lean_dec(v___y_8257_);
    lean_dec_ref(v___y_8256_);
    lean_dec_ref(v_x_8255_);
    lean_dec_ref(v_xs_8254_);
    lean_dec(v_recArgPos_8253_);
    lean_dec_ref(v___x_8252_);
    return v_res_8261_;
}
pub unsafe fn l_Lean_Elab_Structural_reportTermMeasure___lam__1(
    mut v_xs_8262_: *mut LeanObject,
    mut v_x_8263_: *mut LeanObject,
    mut v___y_8264_: *mut LeanObject,
    mut v___y_8265_: *mut LeanObject,
    mut v___y_8266_: *mut LeanObject,
    mut v___y_8267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8270_: *mut LeanObject = core::ptr::null_mut();
    v___x_8269_ = lean_array_get_size(v_xs_8262_);
    v___x_8270_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8270_, 0, v___x_8269_);
    return v___x_8270_;
}
pub unsafe fn l_Lean_Elab_Structural_reportTermMeasure___lam__1___boxed(
    mut v_xs_8271_: *mut LeanObject,
    mut v_x_8272_: *mut LeanObject,
    mut v___y_8273_: *mut LeanObject,
    mut v___y_8274_: *mut LeanObject,
    mut v___y_8275_: *mut LeanObject,
    mut v___y_8276_: *mut LeanObject,
    mut v___y_8277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8278_: *mut LeanObject = core::ptr::null_mut();
    v_res_8278_ = l_Lean_Elab_Structural_reportTermMeasure___lam__1(
        v_xs_8271_,
        v_x_8272_,
        v___y_8273_,
        v___y_8274_,
        v___y_8275_,
        v___y_8276_,
    );
    lean_dec(v___y_8276_);
    lean_dec_ref(v___y_8275_);
    lean_dec(v___y_8274_);
    lean_dec_ref(v___y_8273_);
    lean_dec_ref(v_x_8272_);
    lean_dec_ref(v_xs_8271_);
    return v_res_8278_;
}
pub unsafe fn l_Lean_Elab_Structural_reportTermMeasure(
    mut v_preDef_8290_: *mut LeanObject,
    mut v_recArgPos_8291_: *mut LeanObject,
    mut v_a_8292_: *mut LeanObject,
    mut v_a_8293_: *mut LeanObject,
    mut v_a_8294_: *mut LeanObject,
    mut v_a_8295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_termination_8297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_terminationBy_x3f_x3f_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_8299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraParams_8300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8303_: u8 = 0;
    let mut v_val_8304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8307_: u8 = 0;
    let mut v___x_8308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8314_: u8 = 0;
    let mut v___x_8315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8324_: u8 = 0;
    let mut v___x_8325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8331_: u8 = 0;
    let mut v___x_8333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8335_: u8 = 0;
    let mut v_a_8336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8339_: u8 = 0;
    let mut v___x_8341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8343_: u8 = 0;
    let mut v_a_8344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8347_: u8 = 0;
    let mut v___x_8349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8351_: u8 = 0;
    let mut v_isSharedCheck_8352_: u8 = 0;
    let mut v_unused_8353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8359_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_termination_8297_ = lean_ctor_get(v_preDef_8290_, 8);
                lean_inc_ref(v_termination_8297_);
                v_terminationBy_x3f_x3f_8298_ = lean_ctor_get(v_termination_8297_, 1);
                lean_inc(v_terminationBy_x3f_x3f_8298_);
                if lean_obj_tag(v_terminationBy_x3f_x3f_8298_) == 1 {
                    v_value_8299_ = lean_ctor_get(v_preDef_8290_, 7);
                    lean_inc_ref(v_value_8299_);
                    lean_dec_ref(v_preDef_8290_);
                    v_extraParams_8300_ = lean_ctor_get(v_termination_8297_, 5);
                    v_isSharedCheck_8352_ = (!lean_is_exclusive(v_termination_8297_)) as u8;
                    if v_isSharedCheck_8352_ == 0 {
                        v_unused_8353_ = lean_ctor_get(v_termination_8297_, 4);
                        lean_dec(v_unused_8353_);
                        v_unused_8354_ = lean_ctor_get(v_termination_8297_, 3);
                        lean_dec(v_unused_8354_);
                        v_unused_8355_ = lean_ctor_get(v_termination_8297_, 2);
                        lean_dec(v_unused_8355_);
                        v_unused_8356_ = lean_ctor_get(v_termination_8297_, 1);
                        lean_dec(v_unused_8356_);
                        v_unused_8357_ = lean_ctor_get(v_termination_8297_, 0);
                        lean_dec(v_unused_8357_);
                        v___x_8302_ = v_termination_8297_;
                        v_isShared_8303_ = v_isSharedCheck_8352_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_extraParams_8300_);
                        lean_dec(v_termination_8297_);
                        v___x_8302_ = lean_box(0);
                        v_isShared_8303_ = v_isSharedCheck_8352_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_terminationBy_x3f_x3f_8298_);
                    lean_dec_ref(v_termination_8297_);
                    lean_dec(v_recArgPos_8291_);
                    lean_dec_ref(v_preDef_8290_);
                    v___x_8358_ = lean_box(0);
                    v___x_8359_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8359_, 0, v___x_8358_);
                    return v___x_8359_;
                }
            }
            1 => {
                v_val_8304_ = lean_ctor_get(v_terminationBy_x3f_x3f_8298_, 0);
                lean_inc(v_val_8304_);
                lean_dec_ref_known(v_terminationBy_x3f_x3f_8298_, 1);
                v___x_8305_ = l_Lean_instInhabitedExpr;
                v___f_8306_ = lean_alloc_closure(
                    l_Lean_Elab_Structural_reportTermMeasure___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    2,
                );
                lean_closure_set(v___f_8306_, 0, v___x_8305_);
                lean_closure_set(v___f_8306_, 1, v_recArgPos_8291_);
                v___x_8307_ = 0;
                lean_inc_ref(v_value_8299_);
                v___x_8308_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_8299_, v___f_8306_, v___x_8307_, v_a_8292_, v_a_8293_, v_a_8294_, v_a_8295_);
                if lean_obj_tag(v___x_8308_) == 0 {
                    v_a_8309_ = lean_ctor_get(v___x_8308_, 0);
                    lean_inc(v_a_8309_);
                    lean_dec_ref_known(v___x_8308_, 1);
                    v___f_8310_ = l_Lean_Elab_Structural_reportTermMeasure___closed__0;
                    v___x_8311_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion_spec__1___redArg(v_value_8299_, v___f_8310_, v___x_8307_, v_a_8292_, v_a_8293_, v_a_8294_, v_a_8295_);
                    if lean_obj_tag(v___x_8311_) == 0 {
                        v_a_8312_ = lean_ctor_get(v___x_8311_, 0);
                        lean_inc(v_a_8312_);
                        lean_dec_ref_known(v___x_8311_, 1);
                        v___x_8313_ = lean_box(0);
                        v___x_8314_ = 1;
                        v___x_8315_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v___x_8315_, 0, v___x_8313_);
                        lean_ctor_set(v___x_8315_, 1, v_a_8309_);
                        lean_ctor_set_uint8(
                            v___x_8315_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_8314_,
                        );
                        v___x_8316_ = l_Lean_Elab_TerminationMeasure_delab(
                            v_a_8312_,
                            v_extraParams_8300_,
                            v___x_8315_,
                            v_a_8292_,
                            v_a_8293_,
                            v_a_8294_,
                            v_a_8295_,
                        );
                        lean_dec(v_a_8312_);
                        if lean_obj_tag(v___x_8316_) == 0 {
                            v_a_8317_ = lean_ctor_get(v___x_8316_, 0);
                            lean_inc(v_a_8317_);
                            lean_dec_ref_known(v___x_8316_, 1);
                            v___x_8318_ = l_Lean_Elab_Structural_reportTermMeasure___closed__5;
                            v___x_8319_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_8319_, 0, v___x_8318_);
                            lean_ctor_set(v___x_8319_, 1, v_a_8317_);
                            v___x_8320_ = lean_box(0);
                            if v_isShared_8303_ == 0 {
                                lean_ctor_set(v___x_8302_, 5, v___x_8320_);
                                lean_ctor_set(v___x_8302_, 4, v___x_8320_);
                                lean_ctor_set(v___x_8302_, 3, v___x_8320_);
                                lean_ctor_set(v___x_8302_, 2, v___x_8320_);
                                lean_ctor_set(v___x_8302_, 1, v___x_8320_);
                                lean_ctor_set(v___x_8302_, 0, v___x_8319_);
                                v___x_8322_ = v___x_8302_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_8327_ = lean_alloc_ctor(0, 6, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_8327_, 0, v___x_8319_);
                                lean_ctor_set(v_reuseFailAlloc_8327_, 1, v___x_8320_);
                                lean_ctor_set(v_reuseFailAlloc_8327_, 2, v___x_8320_);
                                lean_ctor_set(v_reuseFailAlloc_8327_, 3, v___x_8320_);
                                lean_ctor_set(v_reuseFailAlloc_8327_, 4, v___x_8320_);
                                lean_ctor_set(v_reuseFailAlloc_8327_, 5, v___x_8320_);
                                v___x_8322_ = v_reuseFailAlloc_8327_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_8304_);
                            lean_del_object(v___x_8302_);
                            v_a_8328_ = lean_ctor_get(v___x_8316_, 0);
                            v_isSharedCheck_8335_ = (!lean_is_exclusive(v___x_8316_)) as u8;
                            if v_isSharedCheck_8335_ == 0 {
                                v___x_8330_ = v___x_8316_;
                                v_isShared_8331_ = v_isSharedCheck_8335_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_8328_);
                                lean_dec(v___x_8316_);
                                v___x_8330_ = lean_box(0);
                                v_isShared_8331_ = v_isSharedCheck_8335_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_8309_);
                        lean_dec(v_val_8304_);
                        lean_del_object(v___x_8302_);
                        lean_dec(v_extraParams_8300_);
                        v_a_8336_ = lean_ctor_get(v___x_8311_, 0);
                        v_isSharedCheck_8343_ = (!lean_is_exclusive(v___x_8311_)) as u8;
                        if v_isSharedCheck_8343_ == 0 {
                            v___x_8338_ = v___x_8311_;
                            v_isShared_8339_ = v_isSharedCheck_8343_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_8336_);
                            lean_dec(v___x_8311_);
                            v___x_8338_ = lean_box(0);
                            v_isShared_8339_ = v_isSharedCheck_8343_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_val_8304_);
                    lean_del_object(v___x_8302_);
                    lean_dec(v_extraParams_8300_);
                    lean_dec_ref(v_value_8299_);
                    v_a_8344_ = lean_ctor_get(v___x_8308_, 0);
                    v_isSharedCheck_8351_ = (!lean_is_exclusive(v___x_8308_)) as u8;
                    if v_isSharedCheck_8351_ == 0 {
                        v___x_8346_ = v___x_8308_;
                        v_isShared_8347_ = v_isSharedCheck_8351_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_8344_);
                        lean_dec(v___x_8308_);
                        v___x_8346_ = lean_box(0);
                        v_isShared_8347_ = v_isSharedCheck_8351_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8323_ = l_Lean_Elab_Structural_reportTermMeasure___closed__6;
                v___x_8324_ = 4;
                v___x_8325_ = l_Lean_MessageData_nil;
                v___x_8326_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_val_8304_,
                    v___x_8322_,
                    v___x_8320_,
                    v___x_8323_,
                    v___x_8320_,
                    v___x_8324_,
                    v___x_8325_,
                    v_a_8294_,
                    v_a_8295_,
                );
                return v___x_8326_;
            }
            3 => {
                if v_isShared_8331_ == 0 {
                    v___x_8333_ = v___x_8330_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8334_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8334_, 0, v_a_8328_);
                    v___x_8333_ = v_reuseFailAlloc_8334_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8333_;
            }
            5 => {
                if v_isShared_8339_ == 0 {
                    v___x_8341_ = v___x_8338_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8342_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8342_, 0, v_a_8336_);
                    v___x_8341_ = v_reuseFailAlloc_8342_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8341_;
            }
            7 => {
                if v_isShared_8347_ == 0 {
                    v___x_8349_ = v___x_8346_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8350_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8350_, 0, v_a_8344_);
                    v___x_8349_ = v_reuseFailAlloc_8350_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_reportTermMeasure___boxed(
    mut v_preDef_8360_: *mut LeanObject,
    mut v_recArgPos_8361_: *mut LeanObject,
    mut v_a_8362_: *mut LeanObject,
    mut v_a_8363_: *mut LeanObject,
    mut v_a_8364_: *mut LeanObject,
    mut v_a_8365_: *mut LeanObject,
    mut v_a_8366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8367_: *mut LeanObject = core::ptr::null_mut();
    v_res_8367_ = l_Lean_Elab_Structural_reportTermMeasure(
        v_preDef_8360_,
        v_recArgPos_8361_,
        v_a_8362_,
        v_a_8363_,
        v_a_8364_,
        v_a_8365_,
    );
    lean_dec(v_a_8365_);
    lean_dec_ref(v_a_8364_);
    lean_dec(v_a_8363_);
    lean_dec_ref(v_a_8362_);
    return v_res_8367_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(
    mut v_as_8368_: *mut LeanObject,
    mut v_sz_8369_: usize,
    mut v_i_8370_: usize,
    mut v_b_8371_: *mut LeanObject,
    mut v___y_8372_: *mut LeanObject,
    mut v___y_8373_: *mut LeanObject,
    mut v___y_8374_: *mut LeanObject,
    mut v___y_8375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8377_: u8 = 0;
    let mut v___x_8378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_8380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8383_: usize = 0;
    let mut v___x_8384_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8377_ = lean_usize_dec_lt(v_i_8370_, v_sz_8369_);
                if v___x_8377_ == 0 {
                    v___x_8378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8378_, 0, v_b_8371_);
                    return v___x_8378_;
                } else {
                    v_a_8379_ = lean_array_uget_borrowed(v_as_8368_, v_i_8370_);
                    v_declName_8380_ = lean_ctor_get(v_a_8379_, 3);
                    lean_inc(v_declName_8380_);
                    v___x_8381_ = l_Lean_Meta_saveEqnAffectingOptions(
                        v_declName_8380_,
                        v___y_8372_,
                        v___y_8373_,
                        v___y_8374_,
                        v___y_8375_,
                    );
                    if lean_obj_tag(v___x_8381_) == 0 {
                        lean_dec_ref_known(v___x_8381_, 1);
                        v___x_8382_ = lean_box(0);
                        v___x_8383_ = 1usize;
                        v___x_8384_ = lean_usize_add(v_i_8370_, v___x_8383_);
                        v_i_8370_ = v___x_8384_;
                        v_b_8371_ = v___x_8382_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_8381_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg___boxed(
    mut v_as_8386_: *mut LeanObject,
    mut v_sz_8387_: *mut LeanObject,
    mut v_i_8388_: *mut LeanObject,
    mut v_b_8389_: *mut LeanObject,
    mut v___y_8390_: *mut LeanObject,
    mut v___y_8391_: *mut LeanObject,
    mut v___y_8392_: *mut LeanObject,
    mut v___y_8393_: *mut LeanObject,
    mut v___y_8394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8395_: usize = 0;
    let mut v_i_boxed_8396_: usize = 0;
    let mut v_res_8397_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8395_ = lean_unbox_usize(v_sz_8387_);
    lean_dec(v_sz_8387_);
    v_i_boxed_8396_ = lean_unbox_usize(v_i_8388_);
    lean_dec(v_i_8388_);
    v_res_8397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_8386_, v_sz_boxed_8395_, v_i_boxed_8396_, v_b_8389_, v___y_8390_, v___y_8391_, v___y_8392_, v___y_8393_);
    lean_dec(v___y_8393_);
    lean_dec_ref(v___y_8392_);
    lean_dec(v___y_8391_);
    lean_dec_ref(v___y_8390_);
    lean_dec_ref(v_as_8386_);
    return v_res_8397_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(
    mut v_docCtx_8398_: *mut LeanObject,
    mut v_a_8399_: *mut LeanObject,
    mut v_snd_8400_: *mut LeanObject,
    mut v_as_8401_: *mut LeanObject,
    mut v_sz_8402_: usize,
    mut v_i_8403_: usize,
    mut v_b_8404_: *mut LeanObject,
    mut v___y_8405_: *mut LeanObject,
    mut v___y_8406_: *mut LeanObject,
    mut v___y_8407_: *mut LeanObject,
    mut v___y_8408_: *mut LeanObject,
    mut v___y_8409_: *mut LeanObject,
    mut v___y_8410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8412_: u8 = 0;
    let mut v___x_8413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_8415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_8416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8417_: u8 = 0;
    let mut v___x_8418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8421_: u8 = 0;
    let mut v_a_8422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_8423_: u8 = 0;
    let mut v_type_8424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preDef_8431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8439_: usize = 0;
    let mut v___x_8440_: usize = 0;
    let mut v_a_8442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8445_: u8 = 0;
    let mut v___x_8447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8449_: u8 = 0;
    let mut v___x_8450_: u8 = 0;
    let mut v___x_8451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8453_: u8 = 0;
    let mut v___x_8454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8456_: usize = 0;
    let mut v___x_8457_: usize = 0;
    let mut v___x_8458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8463_: u8 = 0;
    let mut v___x_8465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8467_: u8 = 0;
    let mut v_a_8468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8471_: u8 = 0;
    let mut v___x_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8475_: u8 = 0;
    let mut v_a_8476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8479_: u8 = 0;
    let mut v___x_8481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8483_: u8 = 0;
    let mut v_reuseFailAlloc_8484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8485_: u8 = 0;
    let mut v_unused_8486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8488_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8412_ = lean_usize_dec_lt(v_i_8403_, v_sz_8402_);
                if v___x_8412_ == 0 {
                    lean_dec_ref(v_snd_8400_);
                    lean_dec_ref(v_a_8399_);
                    lean_dec_ref(v_docCtx_8398_);
                    v___x_8413_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8413_, 0, v_b_8404_);
                    return v___x_8413_;
                } else {
                    v_array_8414_ = lean_ctor_get(v_b_8404_, 0);
                    v_start_8415_ = lean_ctor_get(v_b_8404_, 1);
                    v_stop_8416_ = lean_ctor_get(v_b_8404_, 2);
                    v___x_8417_ = lean_nat_dec_lt(v_start_8415_, v_stop_8416_);
                    if v___x_8417_ == 0 {
                        lean_dec_ref(v_snd_8400_);
                        lean_dec_ref(v_a_8399_);
                        lean_dec_ref(v_docCtx_8398_);
                        v___x_8418_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_8418_, 0, v_b_8404_);
                        return v___x_8418_;
                    } else {
                        lean_inc(v_stop_8416_);
                        lean_inc(v_start_8415_);
                        lean_inc_ref(v_array_8414_);
                        v_isSharedCheck_8485_ = (!lean_is_exclusive(v_b_8404_)) as u8;
                        if v_isSharedCheck_8485_ == 0 {
                            v_unused_8486_ = lean_ctor_get(v_b_8404_, 2);
                            lean_dec(v_unused_8486_);
                            v_unused_8487_ = lean_ctor_get(v_b_8404_, 1);
                            lean_dec(v_unused_8487_);
                            v_unused_8488_ = lean_ctor_get(v_b_8404_, 0);
                            lean_dec(v_unused_8488_);
                            v___x_8420_ = v_b_8404_;
                            v_isShared_8421_ = v_isSharedCheck_8485_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_b_8404_);
                            v___x_8420_ = lean_box(0);
                            v_isShared_8421_ = v_isSharedCheck_8485_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_a_8422_ = lean_array_uget_borrowed(v_as_8401_, v_i_8403_);
                v_kind_8423_ = lean_ctor_get_uint8(
                    v_a_8422_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                );
                v_type_8424_ = lean_ctor_get(v_a_8422_, 6);
                v___x_8425_ = lean_array_fget(v_array_8414_, v_start_8415_);
                v___x_8426_ = lean_unsigned_to_nat(1);
                v___x_8427_ = lean_nat_add(v_start_8415_, v___x_8426_);
                lean_dec(v_start_8415_);
                if v_isShared_8421_ == 0 {
                    lean_ctor_set(v___x_8420_, 1, v___x_8427_);
                    v___x_8429_ = v___x_8420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8484_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8484_, 0, v_array_8414_);
                    lean_ctor_set(v_reuseFailAlloc_8484_, 1, v___x_8427_);
                    lean_ctor_set(v_reuseFailAlloc_8484_, 2, v_stop_8416_);
                    v___x_8429_ = v_reuseFailAlloc_8484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8450_ = l_Lean_Elab_DefKind_isTheorem(v_kind_8423_);
                if v___x_8450_ == 0 {
                    lean_inc_ref(v_type_8424_);
                    v___x_8451_ = l_Lean_Meta_isProp(
                        v_type_8424_,
                        v___y_8407_,
                        v___y_8408_,
                        v___y_8409_,
                        v___y_8410_,
                    );
                    if lean_obj_tag(v___x_8451_) == 0 {
                        v_a_8452_ = lean_ctor_get(v___x_8451_, 0);
                        lean_inc(v_a_8452_);
                        lean_dec_ref_known(v___x_8451_, 1);
                        v___x_8453_ = (lean_unbox(v_a_8452_) as u8);
                        lean_dec(v_a_8452_);
                        if v___x_8453_ == 0 {
                            lean_inc(v_a_8422_);
                            v___x_8454_ = l_Lean_Elab_abstractNestedProofs(
                                v_a_8422_,
                                v___x_8417_,
                                v___y_8407_,
                                v___y_8408_,
                                v___y_8409_,
                                v___y_8410_,
                            );
                            if lean_obj_tag(v___x_8454_) == 0 {
                                v_a_8455_ = lean_ctor_get(v___x_8454_, 0);
                                lean_inc_n(v_a_8455_, 2);
                                lean_dec_ref_known(v___x_8454_, 1);
                                v_sz_8456_ = lean_array_size(v_a_8399_);
                                v___x_8457_ = 0usize;
                                lean_inc_ref(v_a_8399_);
                                v___x_8458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_8456_, v___x_8457_, v_a_8399_);
                                lean_inc_ref(v_snd_8400_);
                                lean_inc(v___x_8425_);
                                v___x_8459_ = l_Lean_Elab_Structural_registerEqnsInfo(
                                    v_a_8455_,
                                    v___x_8458_,
                                    v___x_8425_,
                                    v_snd_8400_,
                                    v___y_8409_,
                                    v___y_8410_,
                                );
                                if lean_obj_tag(v___x_8459_) == 0 {
                                    lean_dec_ref_known(v___x_8459_, 1);
                                    v_preDef_8431_ = v_a_8455_;
                                    v___y_8432_ = v___y_8405_;
                                    v___y_8433_ = v___y_8406_;
                                    v___y_8434_ = v___y_8407_;
                                    v___y_8435_ = v___y_8408_;
                                    v___y_8436_ = v___y_8409_;
                                    v___y_8437_ = v___y_8410_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_a_8455_);
                                    lean_dec_ref(v___x_8429_);
                                    lean_dec(v___x_8425_);
                                    lean_dec_ref(v_snd_8400_);
                                    lean_dec_ref(v_a_8399_);
                                    lean_dec_ref(v_docCtx_8398_);
                                    v_a_8460_ = lean_ctor_get(v___x_8459_, 0);
                                    v_isSharedCheck_8467_ = (!lean_is_exclusive(v___x_8459_)) as u8;
                                    if v_isSharedCheck_8467_ == 0 {
                                        v___x_8462_ = v___x_8459_;
                                        v_isShared_8463_ = v_isSharedCheck_8467_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_8460_);
                                        lean_dec(v___x_8459_);
                                        v___x_8462_ = lean_box(0);
                                        v_isShared_8463_ = v_isSharedCheck_8467_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_8429_);
                                lean_dec(v___x_8425_);
                                lean_dec_ref(v_snd_8400_);
                                lean_dec_ref(v_a_8399_);
                                lean_dec_ref(v_docCtx_8398_);
                                v_a_8468_ = lean_ctor_get(v___x_8454_, 0);
                                v_isSharedCheck_8475_ = (!lean_is_exclusive(v___x_8454_)) as u8;
                                if v_isSharedCheck_8475_ == 0 {
                                    v___x_8470_ = v___x_8454_;
                                    v_isShared_8471_ = v_isSharedCheck_8475_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_8468_);
                                    lean_dec(v___x_8454_);
                                    v___x_8470_ = lean_box(0);
                                    v_isShared_8471_ = v_isSharedCheck_8475_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc(v_a_8422_);
                            v_preDef_8431_ = v_a_8422_;
                            v___y_8432_ = v___y_8405_;
                            v___y_8433_ = v___y_8406_;
                            v___y_8434_ = v___y_8407_;
                            v___y_8435_ = v___y_8408_;
                            v___y_8436_ = v___y_8409_;
                            v___y_8437_ = v___y_8410_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_8429_);
                        lean_dec(v___x_8425_);
                        lean_dec_ref(v_snd_8400_);
                        lean_dec_ref(v_a_8399_);
                        lean_dec_ref(v_docCtx_8398_);
                        v_a_8476_ = lean_ctor_get(v___x_8451_, 0);
                        v_isSharedCheck_8483_ = (!lean_is_exclusive(v___x_8451_)) as u8;
                        if v_isSharedCheck_8483_ == 0 {
                            v___x_8478_ = v___x_8451_;
                            v_isShared_8479_ = v_isSharedCheck_8483_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_8476_);
                            lean_dec(v___x_8451_);
                            v___x_8478_ = lean_box(0);
                            v_isShared_8479_ = v_isSharedCheck_8483_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_a_8422_);
                    v_preDef_8431_ = v_a_8422_;
                    v___y_8432_ = v___y_8405_;
                    v___y_8433_ = v___y_8406_;
                    v___y_8434_ = v___y_8407_;
                    v___y_8435_ = v___y_8408_;
                    v___y_8436_ = v___y_8409_;
                    v___y_8437_ = v___y_8410_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v_docCtx_8398_);
                v___x_8438_ = l_Lean_Elab_Structural_addSmartUnfoldingDef(
                    v_docCtx_8398_,
                    v_preDef_8431_,
                    v___x_8425_,
                    v___y_8432_,
                    v___y_8433_,
                    v___y_8434_,
                    v___y_8435_,
                    v___y_8436_,
                    v___y_8437_,
                );
                if lean_obj_tag(v___x_8438_) == 0 {
                    lean_dec_ref_known(v___x_8438_, 1);
                    v___x_8439_ = 1usize;
                    v___x_8440_ = lean_usize_add(v_i_8403_, v___x_8439_);
                    v_i_8403_ = v___x_8440_;
                    v_b_8404_ = v___x_8429_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v___x_8429_);
                    lean_dec_ref(v_snd_8400_);
                    lean_dec_ref(v_a_8399_);
                    lean_dec_ref(v_docCtx_8398_);
                    v_a_8442_ = lean_ctor_get(v___x_8438_, 0);
                    v_isSharedCheck_8449_ = (!lean_is_exclusive(v___x_8438_)) as u8;
                    if v_isSharedCheck_8449_ == 0 {
                        v___x_8444_ = v___x_8438_;
                        v_isShared_8445_ = v_isSharedCheck_8449_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8442_);
                        lean_dec(v___x_8438_);
                        v___x_8444_ = lean_box(0);
                        v_isShared_8445_ = v_isSharedCheck_8449_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_8445_ == 0 {
                    v___x_8447_ = v___x_8444_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8448_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8448_, 0, v_a_8442_);
                    v___x_8447_ = v_reuseFailAlloc_8448_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8447_;
            }
            6 => {
                if v_isShared_8463_ == 0 {
                    v___x_8465_ = v___x_8462_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8466_, 0, v_a_8460_);
                    v___x_8465_ = v_reuseFailAlloc_8466_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8465_;
            }
            8 => {
                if v_isShared_8471_ == 0 {
                    v___x_8473_ = v___x_8470_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8474_, 0, v_a_8468_);
                    v___x_8473_ = v_reuseFailAlloc_8474_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8473_;
            }
            10 => {
                if v_isShared_8479_ == 0 {
                    v___x_8481_ = v___x_8478_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8482_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8482_, 0, v_a_8476_);
                    v___x_8481_ = v_reuseFailAlloc_8482_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1___boxed(
    mut v_docCtx_8489_: *mut LeanObject,
    mut v_a_8490_: *mut LeanObject,
    mut v_snd_8491_: *mut LeanObject,
    mut v_as_8492_: *mut LeanObject,
    mut v_sz_8493_: *mut LeanObject,
    mut v_i_8494_: *mut LeanObject,
    mut v_b_8495_: *mut LeanObject,
    mut v___y_8496_: *mut LeanObject,
    mut v___y_8497_: *mut LeanObject,
    mut v___y_8498_: *mut LeanObject,
    mut v___y_8499_: *mut LeanObject,
    mut v___y_8500_: *mut LeanObject,
    mut v___y_8501_: *mut LeanObject,
    mut v___y_8502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8503_: usize = 0;
    let mut v_i_boxed_8504_: usize = 0;
    let mut v_res_8505_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8503_ = lean_unbox_usize(v_sz_8493_);
    lean_dec(v_sz_8493_);
    v_i_boxed_8504_ = lean_unbox_usize(v_i_8494_);
    lean_dec(v_i_8494_);
    v_res_8505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_8489_, v_a_8490_, v_snd_8491_, v_as_8492_, v_sz_boxed_8503_, v_i_boxed_8504_, v_b_8495_, v___y_8496_, v___y_8497_, v___y_8498_, v___y_8499_, v___y_8500_, v___y_8501_);
    lean_dec(v___y_8501_);
    lean_dec_ref(v___y_8500_);
    lean_dec(v___y_8499_);
    lean_dec_ref(v___y_8498_);
    lean_dec(v___y_8497_);
    lean_dec_ref(v___y_8496_);
    lean_dec_ref(v_as_8492_);
    return v_res_8505_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0(
    mut v___x_8506_: *mut LeanObject,
    mut v_e_8507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8509_: *mut LeanObject = core::ptr::null_mut();
    v___x_8508_ = l_Lean_indentD(v_e_8507_);
    v___x_8509_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_8509_, 0, v___x_8506_);
    lean_ctor_set(v___x_8509_, 1, v___x_8508_);
    return v___x_8509_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(
    mut v_docCtx_8510_: *mut LeanObject,
    mut v_a_8511_: *mut LeanObject,
    mut v___x_8512_: u8,
    mut v___x_8513_: *mut LeanObject,
    mut v___x_8514_: u8,
    mut v___y_8515_: *mut LeanObject,
    mut v___y_8516_: *mut LeanObject,
    mut v___y_8517_: *mut LeanObject,
    mut v___y_8518_: *mut LeanObject,
    mut v___y_8519_: *mut LeanObject,
    mut v___y_8520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8522_: *mut LeanObject = core::ptr::null_mut();
    v___x_8522_ = l_Lean_Elab_addNonRec(
        v_docCtx_8510_,
        v_a_8511_,
        v___x_8512_,
        v___x_8513_,
        v___x_8514_,
        v___x_8512_,
        v___x_8514_,
        v___y_8515_,
        v___y_8516_,
        v___y_8517_,
        v___y_8518_,
        v___y_8519_,
        v___y_8520_,
    );
    return v___x_8522_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed(
    mut v_docCtx_8523_: *mut LeanObject,
    mut v_a_8524_: *mut LeanObject,
    mut v___x_8525_: *mut LeanObject,
    mut v___x_8526_: *mut LeanObject,
    mut v___x_8527_: *mut LeanObject,
    mut v___y_8528_: *mut LeanObject,
    mut v___y_8529_: *mut LeanObject,
    mut v___y_8530_: *mut LeanObject,
    mut v___y_8531_: *mut LeanObject,
    mut v___y_8532_: *mut LeanObject,
    mut v___y_8533_: *mut LeanObject,
    mut v___y_8534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9560__boxed_8535_: u8 = 0;
    let mut v___x_9562__boxed_8536_: u8 = 0;
    let mut v_res_8537_: *mut LeanObject = core::ptr::null_mut();
    v___x_9560__boxed_8535_ = (lean_unbox(v___x_8525_) as u8);
    v___x_9562__boxed_8536_ = (lean_unbox(v___x_8527_) as u8);
    v_res_8537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1(v_docCtx_8523_, v_a_8524_, v___x_9560__boxed_8535_, v___x_8526_, v___x_9562__boxed_8536_, v___y_8528_, v___y_8529_, v___y_8530_, v___y_8531_, v___y_8532_, v___y_8533_);
    lean_dec(v___y_8533_);
    lean_dec_ref(v___y_8532_);
    lean_dec(v___y_8531_);
    lean_dec_ref(v___y_8530_);
    lean_dec(v___y_8529_);
    lean_dec_ref(v___y_8528_);
    return v_res_8537_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1()
-> *mut LeanObject {
    let mut v___x_8539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8540_: *mut LeanObject = core::ptr::null_mut();
    v___x_8539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__0;
    v___x_8540_ = l_Lean_stringToMessageData(v___x_8539_);
    return v___x_8540_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2()
-> *mut LeanObject {
    let mut v___x_8541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8542_: *mut LeanObject = core::ptr::null_mut();
    v___x_8541_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__1);
    v___f_8542_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_8542_, 0, v___x_8541_);
    return v___f_8542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(
    mut v_names_8543_: *mut LeanObject,
    mut v_docCtx_8544_: *mut LeanObject,
    mut v_as_8545_: *mut LeanObject,
    mut v_i_8546_: usize,
    mut v_stop_8547_: usize,
    mut v_b_8548_: *mut LeanObject,
    mut v___y_8549_: *mut LeanObject,
    mut v___y_8550_: *mut LeanObject,
    mut v___y_8551_: *mut LeanObject,
    mut v___y_8552_: *mut LeanObject,
    mut v___y_8553_: *mut LeanObject,
    mut v___y_8554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8556_: u8 = 0;
    let mut v___x_8557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8562_: u8 = 0;
    let mut v___x_8563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8568_: usize = 0;
    let mut v___x_8569_: usize = 0;
    let mut v_a_8571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8574_: u8 = 0;
    let mut v___x_8576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8578_: u8 = 0;
    let mut v_a_8579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8582_: u8 = 0;
    let mut v___x_8584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8586_: u8 = 0;
    let mut v___x_8587_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8556_ = lean_usize_dec_eq(v_i_8546_, v_stop_8547_);
                if v___x_8556_ == 0 {
                    v___x_8557_ = lean_array_uget_borrowed(v_as_8545_, v_i_8546_);
                    lean_inc(v___x_8557_);
                    v___x_8558_ =
                        l_Lean_Elab_eraseRecAppSyntax(v___x_8557_, v___y_8553_, v___y_8554_);
                    if lean_obj_tag(v___x_8558_) == 0 {
                        v_a_8559_ = lean_ctor_get(v___x_8558_, 0);
                        lean_inc(v_a_8559_);
                        lean_dec_ref_known(v___x_8558_, 1);
                        v___f_8560_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___closed__2);
                        lean_inc_ref(v_names_8543_);
                        v___x_8561_ = lean_array_to_list(v_names_8543_);
                        v___x_8562_ = 1;
                        v___x_8563_ = lean_box((v___x_8556_) as usize);
                        v___x_8564_ = lean_box((v___x_8562_) as usize);
                        lean_inc(v___y_8550_);
                        lean_inc_ref(v___y_8549_);
                        lean_inc_ref(v_docCtx_8544_);
                        v___f_8565_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___lam__1___boxed as *mut core::ffi::c_void, 12, 7);
                        lean_closure_set(v___f_8565_, 0, v_docCtx_8544_);
                        lean_closure_set(v___f_8565_, 1, v_a_8559_);
                        lean_closure_set(v___f_8565_, 2, v___x_8563_);
                        lean_closure_set(v___f_8565_, 3, v___x_8561_);
                        lean_closure_set(v___f_8565_, 4, v___x_8564_);
                        lean_closure_set(v___f_8565_, 5, v___y_8549_);
                        lean_closure_set(v___f_8565_, 6, v___y_8550_);
                        v___x_8566_ = l_Lean_Meta_mapErrorImp___redArg(
                            v___f_8565_,
                            v___f_8560_,
                            v___y_8551_,
                            v___y_8552_,
                            v___y_8553_,
                            v___y_8554_,
                        );
                        if lean_obj_tag(v___x_8566_) == 0 {
                            if lean_obj_tag(v___x_8566_) == 0 {
                                v_a_8567_ = lean_ctor_get(v___x_8566_, 0);
                                lean_inc(v_a_8567_);
                                lean_dec_ref_known(v___x_8566_, 1);
                                v___x_8568_ = 1usize;
                                v___x_8569_ = lean_usize_add(v_i_8546_, v___x_8568_);
                                v_i_8546_ = v___x_8569_;
                                v_b_8548_ = v_a_8567_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec_ref(v_docCtx_8544_);
                                lean_dec_ref(v_names_8543_);
                                return v___x_8566_;
                            }
                        } else {
                            lean_dec_ref(v_docCtx_8544_);
                            lean_dec_ref(v_names_8543_);
                            v_a_8571_ = lean_ctor_get(v___x_8566_, 0);
                            v_isSharedCheck_8578_ = (!lean_is_exclusive(v___x_8566_)) as u8;
                            if v_isSharedCheck_8578_ == 0 {
                                v___x_8573_ = v___x_8566_;
                                v_isShared_8574_ = v_isSharedCheck_8578_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_8571_);
                                lean_dec(v___x_8566_);
                                v___x_8573_ = lean_box(0);
                                v_isShared_8574_ = v_isSharedCheck_8578_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_docCtx_8544_);
                        lean_dec_ref(v_names_8543_);
                        v_a_8579_ = lean_ctor_get(v___x_8558_, 0);
                        v_isSharedCheck_8586_ = (!lean_is_exclusive(v___x_8558_)) as u8;
                        if v_isSharedCheck_8586_ == 0 {
                            v___x_8581_ = v___x_8558_;
                            v_isShared_8582_ = v_isSharedCheck_8586_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_8579_);
                            lean_dec(v___x_8558_);
                            v___x_8581_ = lean_box(0);
                            v_isShared_8582_ = v_isSharedCheck_8586_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_docCtx_8544_);
                    lean_dec_ref(v_names_8543_);
                    v___x_8587_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8587_, 0, v_b_8548_);
                    return v___x_8587_;
                }
            }
            1 => {
                if v_isShared_8574_ == 0 {
                    v___x_8576_ = v___x_8573_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8577_, 0, v_a_8571_);
                    v___x_8576_ = v_reuseFailAlloc_8577_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8576_;
            }
            3 => {
                if v_isShared_8582_ == 0 {
                    v___x_8584_ = v___x_8581_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8585_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8585_, 0, v_a_8579_);
                    v___x_8584_ = v_reuseFailAlloc_8585_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5___boxed(
    mut v_names_8588_: *mut LeanObject,
    mut v_docCtx_8589_: *mut LeanObject,
    mut v_as_8590_: *mut LeanObject,
    mut v_i_8591_: *mut LeanObject,
    mut v_stop_8592_: *mut LeanObject,
    mut v_b_8593_: *mut LeanObject,
    mut v___y_8594_: *mut LeanObject,
    mut v___y_8595_: *mut LeanObject,
    mut v___y_8596_: *mut LeanObject,
    mut v___y_8597_: *mut LeanObject,
    mut v___y_8598_: *mut LeanObject,
    mut v___y_8599_: *mut LeanObject,
    mut v___y_8600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_8601_: usize = 0;
    let mut v_stop_boxed_8602_: usize = 0;
    let mut v_res_8603_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_8601_ = lean_unbox_usize(v_i_8591_);
    lean_dec(v_i_8591_);
    v_stop_boxed_8602_ = lean_unbox_usize(v_stop_8592_);
    lean_dec(v_stop_8592_);
    v_res_8603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_8588_, v_docCtx_8589_, v_as_8590_, v_i_boxed_8601_, v_stop_boxed_8602_, v_b_8593_, v___y_8594_, v___y_8595_, v___y_8596_, v___y_8597_, v___y_8598_, v___y_8599_);
    lean_dec(v___y_8599_);
    lean_dec_ref(v___y_8598_);
    lean_dec(v___y_8597_);
    lean_dec_ref(v___y_8596_);
    lean_dec(v___y_8595_);
    lean_dec_ref(v___y_8594_);
    lean_dec_ref(v_as_8590_);
    return v_res_8603_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(
    mut v_as_8604_: *mut LeanObject,
    mut v_sz_8605_: usize,
    mut v_i_8606_: usize,
    mut v_b_8607_: *mut LeanObject,
    mut v___y_8608_: *mut LeanObject,
    mut v___y_8609_: *mut LeanObject,
    mut v___y_8610_: *mut LeanObject,
    mut v___y_8611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8613_: u8 = 0;
    let mut v___x_8614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_8615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_8616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_8617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8618_: u8 = 0;
    let mut v___x_8619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8622_: u8 = 0;
    let mut v_a_8623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8630_: usize = 0;
    let mut v___x_8631_: usize = 0;
    let mut v_reuseFailAlloc_8633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8637_: u8 = 0;
    let mut v___x_8639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8641_: u8 = 0;
    let mut v_isSharedCheck_8642_: u8 = 0;
    let mut v_unused_8643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8645_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8613_ = lean_usize_dec_lt(v_i_8606_, v_sz_8605_);
                if v___x_8613_ == 0 {
                    v___x_8614_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8614_, 0, v_b_8607_);
                    return v___x_8614_;
                } else {
                    v_array_8615_ = lean_ctor_get(v_b_8607_, 0);
                    v_start_8616_ = lean_ctor_get(v_b_8607_, 1);
                    v_stop_8617_ = lean_ctor_get(v_b_8607_, 2);
                    v___x_8618_ = lean_nat_dec_lt(v_start_8616_, v_stop_8617_);
                    if v___x_8618_ == 0 {
                        v___x_8619_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_8619_, 0, v_b_8607_);
                        return v___x_8619_;
                    } else {
                        lean_inc(v_stop_8617_);
                        lean_inc(v_start_8616_);
                        lean_inc_ref(v_array_8615_);
                        v_isSharedCheck_8642_ = (!lean_is_exclusive(v_b_8607_)) as u8;
                        if v_isSharedCheck_8642_ == 0 {
                            v_unused_8643_ = lean_ctor_get(v_b_8607_, 2);
                            lean_dec(v_unused_8643_);
                            v_unused_8644_ = lean_ctor_get(v_b_8607_, 1);
                            lean_dec(v_unused_8644_);
                            v_unused_8645_ = lean_ctor_get(v_b_8607_, 0);
                            lean_dec(v_unused_8645_);
                            v___x_8621_ = v_b_8607_;
                            v_isShared_8622_ = v_isSharedCheck_8642_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_b_8607_);
                            v___x_8621_ = lean_box(0);
                            v_isShared_8622_ = v_isSharedCheck_8642_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_a_8623_ = lean_array_uget_borrowed(v_as_8604_, v_i_8606_);
                v___x_8624_ = lean_array_fget_borrowed(v_array_8615_, v_start_8616_);
                lean_inc(v_a_8623_);
                lean_inc(v___x_8624_);
                v___x_8625_ = l_Lean_Elab_Structural_reportTermMeasure(
                    v___x_8624_,
                    v_a_8623_,
                    v___y_8608_,
                    v___y_8609_,
                    v___y_8610_,
                    v___y_8611_,
                );
                if lean_obj_tag(v___x_8625_) == 0 {
                    lean_dec_ref_known(v___x_8625_, 1);
                    v___x_8626_ = lean_unsigned_to_nat(1);
                    v___x_8627_ = lean_nat_add(v_start_8616_, v___x_8626_);
                    lean_dec(v_start_8616_);
                    if v_isShared_8622_ == 0 {
                        lean_ctor_set(v___x_8621_, 1, v___x_8627_);
                        v___x_8629_ = v___x_8621_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8633_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8633_, 0, v_array_8615_);
                        lean_ctor_set(v_reuseFailAlloc_8633_, 1, v___x_8627_);
                        lean_ctor_set(v_reuseFailAlloc_8633_, 2, v_stop_8617_);
                        v___x_8629_ = v_reuseFailAlloc_8633_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8621_);
                    lean_dec(v_stop_8617_);
                    lean_dec(v_start_8616_);
                    lean_dec_ref(v_array_8615_);
                    v_a_8634_ = lean_ctor_get(v___x_8625_, 0);
                    v_isSharedCheck_8641_ = (!lean_is_exclusive(v___x_8625_)) as u8;
                    if v_isSharedCheck_8641_ == 0 {
                        v___x_8636_ = v___x_8625_;
                        v_isShared_8637_ = v_isSharedCheck_8641_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8634_);
                        lean_dec(v___x_8625_);
                        v___x_8636_ = lean_box(0);
                        v_isShared_8637_ = v_isSharedCheck_8641_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8630_ = 1usize;
                v___x_8631_ = lean_usize_add(v_i_8606_, v___x_8630_);
                v_i_8606_ = v___x_8631_;
                v_b_8607_ = v___x_8629_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_8637_ == 0 {
                    v___x_8639_ = v___x_8636_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8640_, 0, v_a_8634_);
                    v___x_8639_ = v_reuseFailAlloc_8640_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg___boxed(
    mut v_as_8646_: *mut LeanObject,
    mut v_sz_8647_: *mut LeanObject,
    mut v_i_8648_: *mut LeanObject,
    mut v_b_8649_: *mut LeanObject,
    mut v___y_8650_: *mut LeanObject,
    mut v___y_8651_: *mut LeanObject,
    mut v___y_8652_: *mut LeanObject,
    mut v___y_8653_: *mut LeanObject,
    mut v___y_8654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8655_: usize = 0;
    let mut v_i_boxed_8656_: usize = 0;
    let mut v_res_8657_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8655_ = lean_unbox_usize(v_sz_8647_);
    lean_dec(v_sz_8647_);
    v_i_boxed_8656_ = lean_unbox_usize(v_i_8648_);
    lean_dec(v_i_8648_);
    v_res_8657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_8646_, v_sz_boxed_8655_, v_i_boxed_8656_, v_b_8649_, v___y_8650_, v___y_8651_, v___y_8652_, v___y_8653_);
    lean_dec(v___y_8653_);
    lean_dec_ref(v___y_8652_);
    lean_dec(v___y_8651_);
    lean_dec_ref(v___y_8650_);
    lean_dec_ref(v_as_8646_);
    return v_res_8657_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(
    mut v_sz_8658_: usize,
    mut v_i_8659_: usize,
    mut v_bs_8660_: *mut LeanObject,
    mut v___y_8661_: *mut LeanObject,
    mut v___y_8662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8664_: u8 = 0;
    let mut v___x_8665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_8666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8671_: usize = 0;
    let mut v___x_8672_: usize = 0;
    let mut v___x_8673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8678_: u8 = 0;
    let mut v___x_8680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8664_ = lean_usize_dec_lt(v_i_8659_, v_sz_8658_);
                if v___x_8664_ == 0 {
                    v___x_8665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8665_, 0, v_bs_8660_);
                    return v___x_8665_;
                } else {
                    v_v_8666_ = lean_array_uget_borrowed(v_bs_8660_, v_i_8659_);
                    lean_inc(v_v_8666_);
                    v___x_8667_ =
                        l_Lean_Elab_eraseRecAppSyntax(v_v_8666_, v___y_8661_, v___y_8662_);
                    if lean_obj_tag(v___x_8667_) == 0 {
                        v_a_8668_ = lean_ctor_get(v___x_8667_, 0);
                        lean_inc(v_a_8668_);
                        lean_dec_ref_known(v___x_8667_, 1);
                        v___x_8669_ = lean_unsigned_to_nat(0);
                        v_bs_x27_8670_ = lean_array_uset(v_bs_8660_, v_i_8659_, v___x_8669_);
                        v___x_8671_ = 1usize;
                        v___x_8672_ = lean_usize_add(v_i_8659_, v___x_8671_);
                        v___x_8673_ = lean_array_uset(v_bs_x27_8670_, v_i_8659_, v_a_8668_);
                        v_i_8659_ = v___x_8672_;
                        v_bs_8660_ = v___x_8673_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_8660_);
                        v_a_8675_ = lean_ctor_get(v___x_8667_, 0);
                        v_isSharedCheck_8682_ = (!lean_is_exclusive(v___x_8667_)) as u8;
                        if v_isSharedCheck_8682_ == 0 {
                            v___x_8677_ = v___x_8667_;
                            v_isShared_8678_ = v_isSharedCheck_8682_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8675_);
                            lean_dec(v___x_8667_);
                            v___x_8677_ = lean_box(0);
                            v_isShared_8678_ = v_isSharedCheck_8682_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8678_ == 0 {
                    v___x_8680_ = v___x_8677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8681_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8681_, 0, v_a_8675_);
                    v___x_8680_ = v_reuseFailAlloc_8681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg___boxed(
    mut v_sz_8683_: *mut LeanObject,
    mut v_i_8684_: *mut LeanObject,
    mut v_bs_8685_: *mut LeanObject,
    mut v___y_8686_: *mut LeanObject,
    mut v___y_8687_: *mut LeanObject,
    mut v___y_8688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8689_: usize = 0;
    let mut v_i_boxed_8690_: usize = 0;
    let mut v_res_8691_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8689_ = lean_unbox_usize(v_sz_8683_);
    lean_dec(v_sz_8683_);
    v_i_boxed_8690_ = lean_unbox_usize(v_i_8684_);
    lean_dec(v_i_8684_);
    v_res_8691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_boxed_8689_, v_i_boxed_8690_, v_bs_8685_, v___y_8686_, v___y_8687_);
    lean_dec(v___y_8687_);
    lean_dec_ref(v___y_8686_);
    return v_res_8691_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(
    mut v_as_8692_: *mut LeanObject,
    mut v_sz_8693_: usize,
    mut v_i_8694_: usize,
    mut v_b_8695_: *mut LeanObject,
    mut v___y_8696_: *mut LeanObject,
    mut v___y_8697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8699_: u8 = 0;
    let mut v___x_8700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_8702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8705_: usize = 0;
    let mut v___x_8706_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8699_ = lean_usize_dec_lt(v_i_8694_, v_sz_8693_);
                if v___x_8699_ == 0 {
                    v___x_8700_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8700_, 0, v_b_8695_);
                    return v___x_8700_;
                } else {
                    v_a_8701_ = lean_array_uget_borrowed(v_as_8692_, v_i_8694_);
                    v_declName_8702_ = lean_ctor_get(v_a_8701_, 3);
                    lean_inc(v_declName_8702_);
                    v___x_8703_ = l_Lean_enableRealizationsForConst(
                        v_declName_8702_,
                        v___y_8696_,
                        v___y_8697_,
                    );
                    if lean_obj_tag(v___x_8703_) == 0 {
                        lean_dec_ref_known(v___x_8703_, 1);
                        v___x_8704_ = lean_box(0);
                        v___x_8705_ = 1usize;
                        v___x_8706_ = lean_usize_add(v_i_8694_, v___x_8705_);
                        v_i_8694_ = v___x_8706_;
                        v_b_8695_ = v___x_8704_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_8703_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg___boxed(
    mut v_as_8708_: *mut LeanObject,
    mut v_sz_8709_: *mut LeanObject,
    mut v_i_8710_: *mut LeanObject,
    mut v_b_8711_: *mut LeanObject,
    mut v___y_8712_: *mut LeanObject,
    mut v___y_8713_: *mut LeanObject,
    mut v___y_8714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8715_: usize = 0;
    let mut v_i_boxed_8716_: usize = 0;
    let mut v_res_8717_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8715_ = lean_unbox_usize(v_sz_8709_);
    lean_dec(v_sz_8709_);
    v_i_boxed_8716_ = lean_unbox_usize(v_i_8710_);
    lean_dec(v_i_8710_);
    v_res_8717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_8708_, v_sz_boxed_8715_, v_i_boxed_8716_, v_b_8711_, v___y_8712_, v___y_8713_);
    lean_dec(v___y_8713_);
    lean_dec_ref(v___y_8712_);
    lean_dec_ref(v_as_8708_);
    return v_res_8717_;
}
pub unsafe fn l_Lean_Elab_Structural_structuralRecursion(
    mut v_docCtx_8718_: *mut LeanObject,
    mut v_preDefs_8719_: *mut LeanObject,
    mut v_termMeasure_x3fs_8720_: *mut LeanObject,
    mut v_a_8721_: *mut LeanObject,
    mut v_a_8722_: *mut LeanObject,
    mut v_a_8723_: *mut LeanObject,
    mut v_a_8724_: *mut LeanObject,
    mut v_a_8725_: *mut LeanObject,
    mut v_a_8726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_8728_: usize = 0;
    let mut v___x_8729_: usize = 0;
    let mut v_names_8730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8744_: usize = 0;
    let mut v___x_8745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8749_: u8 = 0;
    let mut v___x_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8754_: u8 = 0;
    let mut v___x_8756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8758_: u8 = 0;
    let mut v_a_8759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8762_: u8 = 0;
    let mut v___x_8764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8766_: u8 = 0;
    let mut v___y_8768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8772_: usize = 0;
    let mut v___x_8773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8775_: u8 = 0;
    let mut v___x_8776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8777_: u8 = 0;
    let mut v___x_8778_: usize = 0;
    let mut v___x_8779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8780_: usize = 0;
    let mut v___x_8781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8785_: u8 = 0;
    let mut v___x_8787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8789_: u8 = 0;
    let mut v_a_8790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8793_: u8 = 0;
    let mut v___x_8795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_8728_ = lean_array_size(v_preDefs_8719_);
                v___x_8729_ = 0usize;
                lean_inc_ref_n(v_preDefs_8719_, 2);
                v_names_8730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos_spec__0(v_sz_8728_, v___x_8729_, v_preDefs_8719_);
                v___x_8731_ = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(v_preDefs_8719_, v_termMeasure_x3fs_8720_, v_a_8723_, v_a_8724_, v_a_8725_, v_a_8726_);
                if lean_obj_tag(v___x_8731_) == 0 {
                    v_a_8732_ = lean_ctor_get(v___x_8731_, 0);
                    lean_inc(v_a_8732_);
                    lean_dec_ref_known(v___x_8731_, 1);
                    v_snd_8733_ = lean_ctor_get(v_a_8732_, 1);
                    lean_inc(v_snd_8733_);
                    v_fst_8734_ = lean_ctor_get(v_a_8732_, 0);
                    lean_inc(v_fst_8734_);
                    lean_dec(v_a_8732_);
                    v_fst_8735_ = lean_ctor_get(v_snd_8733_, 0);
                    lean_inc(v_fst_8735_);
                    v_snd_8736_ = lean_ctor_get(v_snd_8733_, 1);
                    lean_inc(v_snd_8736_);
                    lean_dec(v_snd_8733_);
                    v___x_8769_ = lean_unsigned_to_nat(0);
                    v___x_8770_ = lean_array_get_size(v_preDefs_8719_);
                    lean_inc_ref(v_preDefs_8719_);
                    v___x_8771_ =
                        l_Array_toSubarray___redArg(v_preDefs_8719_, v___x_8769_, v___x_8770_);
                    v_sz_8772_ = lean_array_size(v_fst_8734_);
                    v___x_8773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_fst_8734_, v_sz_8772_, v___x_8729_, v___x_8771_, v_a_8723_, v_a_8724_, v_a_8725_, v_a_8726_);
                    if lean_obj_tag(v___x_8773_) == 0 {
                        lean_dec_ref_known(v___x_8773_, 1);
                        v___x_8774_ = lean_array_get_size(v_fst_8735_);
                        v___x_8775_ = lean_nat_dec_lt(v___x_8769_, v___x_8774_);
                        if v___x_8775_ == 0 {
                            lean_dec_ref(v_names_8730_);
                            state = 1;
                            continue;
                        } else {
                            v___x_8776_ = lean_box(0);
                            v___x_8777_ = lean_nat_dec_le(v___x_8774_, v___x_8774_);
                            if v___x_8777_ == 0 {
                                if v___x_8775_ == 0 {
                                    lean_dec_ref(v_names_8730_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_8778_ = lean_usize_of_nat(v___x_8774_);
                                    lean_inc_ref(v_docCtx_8718_);
                                    v___x_8779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_8730_, v_docCtx_8718_, v_fst_8735_, v___x_8729_, v___x_8778_, v___x_8776_, v_a_8721_, v_a_8722_, v_a_8723_, v_a_8724_, v_a_8725_, v_a_8726_);
                                    v___y_8768_ = v___x_8779_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                v___x_8780_ = lean_usize_of_nat(v___x_8774_);
                                lean_inc_ref(v_docCtx_8718_);
                                v___x_8781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_structuralRecursion_spec__5(v_names_8730_, v_docCtx_8718_, v_fst_8735_, v___x_8729_, v___x_8780_, v___x_8776_, v_a_8721_, v_a_8722_, v_a_8723_, v_a_8724_, v_a_8725_, v_a_8726_);
                                v___y_8768_ = v___x_8781_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_snd_8736_);
                        lean_dec(v_fst_8735_);
                        lean_dec(v_fst_8734_);
                        lean_dec_ref(v_names_8730_);
                        lean_dec_ref(v_preDefs_8719_);
                        lean_dec_ref(v_docCtx_8718_);
                        v_a_8782_ = lean_ctor_get(v___x_8773_, 0);
                        v_isSharedCheck_8789_ = (!lean_is_exclusive(v___x_8773_)) as u8;
                        if v_isSharedCheck_8789_ == 0 {
                            v___x_8784_ = v___x_8773_;
                            v_isShared_8785_ = v_isSharedCheck_8789_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_8782_);
                            lean_dec(v___x_8773_);
                            v___x_8784_ = lean_box(0);
                            v_isShared_8785_ = v_isSharedCheck_8789_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_names_8730_);
                    lean_dec_ref(v_preDefs_8719_);
                    lean_dec_ref(v_docCtx_8718_);
                    v_a_8790_ = lean_ctor_get(v___x_8731_, 0);
                    v_isSharedCheck_8797_ = (!lean_is_exclusive(v___x_8731_)) as u8;
                    if v_isSharedCheck_8797_ == 0 {
                        v___x_8792_ = v___x_8731_;
                        v_isShared_8793_ = v_isSharedCheck_8797_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_8790_);
                        lean_dec(v___x_8731_);
                        v___x_8792_ = lean_box(0);
                        v_isShared_8793_ = v_isSharedCheck_8797_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_8728_, v___x_8729_, v_preDefs_8719_, v_a_8725_, v_a_8726_);
                if lean_obj_tag(v___x_8738_) == 0 {
                    v_a_8739_ = lean_ctor_get(v___x_8738_, 0);
                    lean_inc_n(v_a_8739_, 2);
                    lean_dec_ref_known(v___x_8738_, 1);
                    lean_inc_ref(v_docCtx_8718_);
                    v___x_8740_ = l_Lean_Elab_addAndCompilePartialRec(
                        v_docCtx_8718_,
                        v_a_8739_,
                        v_a_8721_,
                        v_a_8722_,
                        v_a_8723_,
                        v_a_8724_,
                        v_a_8725_,
                        v_a_8726_,
                    );
                    if lean_obj_tag(v___x_8740_) == 0 {
                        lean_dec_ref_known(v___x_8740_, 1);
                        v___x_8741_ = lean_unsigned_to_nat(0);
                        v___x_8742_ = lean_array_get_size(v_fst_8734_);
                        v___x_8743_ =
                            l_Array_toSubarray___redArg(v_fst_8734_, v___x_8741_, v___x_8742_);
                        v_sz_8744_ = lean_array_size(v_a_8739_);
                        lean_inc(v_a_8739_);
                        v___x_8745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__1(v_docCtx_8718_, v_a_8739_, v_snd_8736_, v_a_8739_, v_sz_8744_, v___x_8729_, v___x_8743_, v_a_8721_, v_a_8722_, v_a_8723_, v_a_8724_, v_a_8725_, v_a_8726_);
                        if lean_obj_tag(v___x_8745_) == 0 {
                            lean_dec_ref_known(v___x_8745_, 1);
                            v___x_8746_ = lean_box(0);
                            v___x_8747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_a_8739_, v_sz_8744_, v___x_8729_, v___x_8746_, v_a_8723_, v_a_8724_, v_a_8725_, v_a_8726_);
                            if lean_obj_tag(v___x_8747_) == 0 {
                                lean_dec_ref_known(v___x_8747_, 1);
                                v___x_8748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_a_8739_, v_sz_8744_, v___x_8729_, v___x_8746_, v_a_8725_, v_a_8726_);
                                lean_dec(v_a_8739_);
                                if lean_obj_tag(v___x_8748_) == 0 {
                                    lean_dec_ref_known(v___x_8748_, 1);
                                    v___x_8749_ = 1;
                                    v___x_8750_ = l_Lean_Elab_applyAttributesOf(
                                        v_fst_8735_,
                                        v___x_8749_,
                                        v_a_8721_,
                                        v_a_8722_,
                                        v_a_8723_,
                                        v_a_8724_,
                                        v_a_8725_,
                                        v_a_8726_,
                                    );
                                    lean_dec(v_fst_8735_);
                                    return v___x_8750_;
                                } else {
                                    lean_dec(v_fst_8735_);
                                    return v___x_8748_;
                                }
                            } else {
                                lean_dec(v_a_8739_);
                                lean_dec(v_fst_8735_);
                                return v___x_8747_;
                            }
                        } else {
                            lean_dec(v_a_8739_);
                            lean_dec(v_fst_8735_);
                            v_a_8751_ = lean_ctor_get(v___x_8745_, 0);
                            v_isSharedCheck_8758_ = (!lean_is_exclusive(v___x_8745_)) as u8;
                            if v_isSharedCheck_8758_ == 0 {
                                v___x_8753_ = v___x_8745_;
                                v_isShared_8754_ = v_isSharedCheck_8758_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_8751_);
                                lean_dec(v___x_8745_);
                                v___x_8753_ = lean_box(0);
                                v_isShared_8754_ = v_isSharedCheck_8758_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_8739_);
                        lean_dec(v_snd_8736_);
                        lean_dec(v_fst_8735_);
                        lean_dec(v_fst_8734_);
                        lean_dec_ref(v_docCtx_8718_);
                        return v___x_8740_;
                    }
                } else {
                    lean_dec(v_snd_8736_);
                    lean_dec(v_fst_8735_);
                    lean_dec(v_fst_8734_);
                    lean_dec_ref(v_docCtx_8718_);
                    v_a_8759_ = lean_ctor_get(v___x_8738_, 0);
                    v_isSharedCheck_8766_ = (!lean_is_exclusive(v___x_8738_)) as u8;
                    if v_isSharedCheck_8766_ == 0 {
                        v___x_8761_ = v___x_8738_;
                        v_isShared_8762_ = v_isSharedCheck_8766_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8759_);
                        lean_dec(v___x_8738_);
                        v___x_8761_ = lean_box(0);
                        v_isShared_8762_ = v_isSharedCheck_8766_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8754_ == 0 {
                    v___x_8756_ = v___x_8753_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8757_, 0, v_a_8751_);
                    v___x_8756_ = v_reuseFailAlloc_8757_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8756_;
            }
            4 => {
                if v_isShared_8762_ == 0 {
                    v___x_8764_ = v___x_8761_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8765_, 0, v_a_8759_);
                    v___x_8764_ = v_reuseFailAlloc_8765_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8764_;
            }
            6 => {
                if lean_obj_tag(v___y_8768_) == 0 {
                    lean_dec_ref_known(v___y_8768_, 1);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_snd_8736_);
                    lean_dec(v_fst_8735_);
                    lean_dec(v_fst_8734_);
                    lean_dec_ref(v_preDefs_8719_);
                    lean_dec_ref(v_docCtx_8718_);
                    return v___y_8768_;
                }
            }
            7 => {
                if v_isShared_8785_ == 0 {
                    v___x_8787_ = v___x_8784_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8788_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8788_, 0, v_a_8782_);
                    v___x_8787_ = v_reuseFailAlloc_8788_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8787_;
            }
            9 => {
                if v_isShared_8793_ == 0 {
                    v___x_8795_ = v___x_8792_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8796_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8796_, 0, v_a_8790_);
                    v___x_8795_ = v_reuseFailAlloc_8796_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_structuralRecursion___boxed(
    mut v_docCtx_8798_: *mut LeanObject,
    mut v_preDefs_8799_: *mut LeanObject,
    mut v_termMeasure_x3fs_8800_: *mut LeanObject,
    mut v_a_8801_: *mut LeanObject,
    mut v_a_8802_: *mut LeanObject,
    mut v_a_8803_: *mut LeanObject,
    mut v_a_8804_: *mut LeanObject,
    mut v_a_8805_: *mut LeanObject,
    mut v_a_8806_: *mut LeanObject,
    mut v_a_8807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8808_: *mut LeanObject = core::ptr::null_mut();
    v_res_8808_ = l_Lean_Elab_Structural_structuralRecursion(
        v_docCtx_8798_,
        v_preDefs_8799_,
        v_termMeasure_x3fs_8800_,
        v_a_8801_,
        v_a_8802_,
        v_a_8803_,
        v_a_8804_,
        v_a_8805_,
        v_a_8806_,
    );
    lean_dec(v_a_8806_);
    lean_dec_ref(v_a_8805_);
    lean_dec(v_a_8804_);
    lean_dec_ref(v_a_8803_);
    lean_dec(v_a_8802_);
    lean_dec_ref(v_a_8801_);
    return v_res_8808_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(
    mut v_sz_8809_: usize,
    mut v_i_8810_: usize,
    mut v_bs_8811_: *mut LeanObject,
    mut v___y_8812_: *mut LeanObject,
    mut v___y_8813_: *mut LeanObject,
    mut v___y_8814_: *mut LeanObject,
    mut v___y_8815_: *mut LeanObject,
    mut v___y_8816_: *mut LeanObject,
    mut v___y_8817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8819_: *mut LeanObject = core::ptr::null_mut();
    v___x_8819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___redArg(v_sz_8809_, v_i_8810_, v_bs_8811_, v___y_8816_, v___y_8817_);
    return v___x_8819_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0___boxed(
    mut v_sz_8820_: *mut LeanObject,
    mut v_i_8821_: *mut LeanObject,
    mut v_bs_8822_: *mut LeanObject,
    mut v___y_8823_: *mut LeanObject,
    mut v___y_8824_: *mut LeanObject,
    mut v___y_8825_: *mut LeanObject,
    mut v___y_8826_: *mut LeanObject,
    mut v___y_8827_: *mut LeanObject,
    mut v___y_8828_: *mut LeanObject,
    mut v___y_8829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8830_: usize = 0;
    let mut v_i_boxed_8831_: usize = 0;
    let mut v_res_8832_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8830_ = lean_unbox_usize(v_sz_8820_);
    lean_dec(v_sz_8820_);
    v_i_boxed_8831_ = lean_unbox_usize(v_i_8821_);
    lean_dec(v_i_8821_);
    v_res_8832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_structuralRecursion_spec__0(v_sz_boxed_8830_, v_i_boxed_8831_, v_bs_8822_, v___y_8823_, v___y_8824_, v___y_8825_, v___y_8826_, v___y_8827_, v___y_8828_);
    lean_dec(v___y_8828_);
    lean_dec_ref(v___y_8827_);
    lean_dec(v___y_8826_);
    lean_dec_ref(v___y_8825_);
    lean_dec(v___y_8824_);
    lean_dec_ref(v___y_8823_);
    return v_res_8832_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(
    mut v_as_8833_: *mut LeanObject,
    mut v_sz_8834_: usize,
    mut v_i_8835_: usize,
    mut v_b_8836_: *mut LeanObject,
    mut v___y_8837_: *mut LeanObject,
    mut v___y_8838_: *mut LeanObject,
    mut v___y_8839_: *mut LeanObject,
    mut v___y_8840_: *mut LeanObject,
    mut v___y_8841_: *mut LeanObject,
    mut v___y_8842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8844_: *mut LeanObject = core::ptr::null_mut();
    v___x_8844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___redArg(v_as_8833_, v_sz_8834_, v_i_8835_, v_b_8836_, v___y_8839_, v___y_8840_, v___y_8841_, v___y_8842_);
    return v___x_8844_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2___boxed(
    mut v_as_8845_: *mut LeanObject,
    mut v_sz_8846_: *mut LeanObject,
    mut v_i_8847_: *mut LeanObject,
    mut v_b_8848_: *mut LeanObject,
    mut v___y_8849_: *mut LeanObject,
    mut v___y_8850_: *mut LeanObject,
    mut v___y_8851_: *mut LeanObject,
    mut v___y_8852_: *mut LeanObject,
    mut v___y_8853_: *mut LeanObject,
    mut v___y_8854_: *mut LeanObject,
    mut v___y_8855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8856_: usize = 0;
    let mut v_i_boxed_8857_: usize = 0;
    let mut v_res_8858_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8856_ = lean_unbox_usize(v_sz_8846_);
    lean_dec(v_sz_8846_);
    v_i_boxed_8857_ = lean_unbox_usize(v_i_8847_);
    lean_dec(v_i_8847_);
    v_res_8858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__2(v_as_8845_, v_sz_boxed_8856_, v_i_boxed_8857_, v_b_8848_, v___y_8849_, v___y_8850_, v___y_8851_, v___y_8852_, v___y_8853_, v___y_8854_);
    lean_dec(v___y_8854_);
    lean_dec_ref(v___y_8853_);
    lean_dec(v___y_8852_);
    lean_dec_ref(v___y_8851_);
    lean_dec(v___y_8850_);
    lean_dec_ref(v___y_8849_);
    lean_dec_ref(v_as_8845_);
    return v_res_8858_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(
    mut v_as_8859_: *mut LeanObject,
    mut v_sz_8860_: usize,
    mut v_i_8861_: usize,
    mut v_b_8862_: *mut LeanObject,
    mut v___y_8863_: *mut LeanObject,
    mut v___y_8864_: *mut LeanObject,
    mut v___y_8865_: *mut LeanObject,
    mut v___y_8866_: *mut LeanObject,
    mut v___y_8867_: *mut LeanObject,
    mut v___y_8868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8870_: *mut LeanObject = core::ptr::null_mut();
    v___x_8870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___redArg(v_as_8859_, v_sz_8860_, v_i_8861_, v_b_8862_, v___y_8867_, v___y_8868_);
    return v___x_8870_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3___boxed(
    mut v_as_8871_: *mut LeanObject,
    mut v_sz_8872_: *mut LeanObject,
    mut v_i_8873_: *mut LeanObject,
    mut v_b_8874_: *mut LeanObject,
    mut v___y_8875_: *mut LeanObject,
    mut v___y_8876_: *mut LeanObject,
    mut v___y_8877_: *mut LeanObject,
    mut v___y_8878_: *mut LeanObject,
    mut v___y_8879_: *mut LeanObject,
    mut v___y_8880_: *mut LeanObject,
    mut v___y_8881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8882_: usize = 0;
    let mut v_i_boxed_8883_: usize = 0;
    let mut v_res_8884_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8882_ = lean_unbox_usize(v_sz_8872_);
    lean_dec(v_sz_8872_);
    v_i_boxed_8883_ = lean_unbox_usize(v_i_8873_);
    lean_dec(v_i_8873_);
    v_res_8884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__3(v_as_8871_, v_sz_boxed_8882_, v_i_boxed_8883_, v_b_8874_, v___y_8875_, v___y_8876_, v___y_8877_, v___y_8878_, v___y_8879_, v___y_8880_);
    lean_dec(v___y_8880_);
    lean_dec_ref(v___y_8879_);
    lean_dec(v___y_8878_);
    lean_dec_ref(v___y_8877_);
    lean_dec(v___y_8876_);
    lean_dec_ref(v___y_8875_);
    lean_dec_ref(v_as_8871_);
    return v_res_8884_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(
    mut v_as_8885_: *mut LeanObject,
    mut v_sz_8886_: usize,
    mut v_i_8887_: usize,
    mut v_b_8888_: *mut LeanObject,
    mut v___y_8889_: *mut LeanObject,
    mut v___y_8890_: *mut LeanObject,
    mut v___y_8891_: *mut LeanObject,
    mut v___y_8892_: *mut LeanObject,
    mut v___y_8893_: *mut LeanObject,
    mut v___y_8894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8896_: *mut LeanObject = core::ptr::null_mut();
    v___x_8896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___redArg(v_as_8885_, v_sz_8886_, v_i_8887_, v_b_8888_, v___y_8891_, v___y_8892_, v___y_8893_, v___y_8894_);
    return v___x_8896_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4___boxed(
    mut v_as_8897_: *mut LeanObject,
    mut v_sz_8898_: *mut LeanObject,
    mut v_i_8899_: *mut LeanObject,
    mut v_b_8900_: *mut LeanObject,
    mut v___y_8901_: *mut LeanObject,
    mut v___y_8902_: *mut LeanObject,
    mut v___y_8903_: *mut LeanObject,
    mut v___y_8904_: *mut LeanObject,
    mut v___y_8905_: *mut LeanObject,
    mut v___y_8906_: *mut LeanObject,
    mut v___y_8907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8908_: usize = 0;
    let mut v_i_boxed_8909_: usize = 0;
    let mut v_res_8910_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8908_ = lean_unbox_usize(v_sz_8898_);
    lean_dec(v_sz_8898_);
    v_i_boxed_8909_ = lean_unbox_usize(v_i_8899_);
    lean_dec(v_i_8899_);
    v_res_8910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_structuralRecursion_spec__4(v_as_8897_, v_sz_boxed_8908_, v_i_boxed_8909_, v_b_8900_, v___y_8901_, v___y_8902_, v___y_8903_, v___y_8904_, v___y_8905_, v___y_8906_);
    lean_dec(v___y_8906_);
    lean_dec_ref(v___y_8905_);
    lean_dec(v___y_8904_);
    lean_dec_ref(v___y_8903_);
    lean_dec(v___y_8902_);
    lean_dec_ref(v___y_8901_);
    lean_dec_ref(v_as_8897_);
    return v_res_8910_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_Main(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_Mutual(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_BRecOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_Main(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_Mutual(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_BRecOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_Main(builtin);
}
