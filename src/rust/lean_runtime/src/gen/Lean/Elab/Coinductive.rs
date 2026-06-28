// Lean compiler output
// Module: Lean.Elab.Coinductive
// Imports: Lean.Elab.PreDefinition.PartialFixpoint Lean.Elab.Tactic.Rewrite Lean.Meta.Tactic.Simp Lean.Linter.UnusedVariables
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_MacroScopesView_review, l_Lean_Name_append,
    l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_extractMacroScopes, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::AuxRecursor::l_Lean_mkCasesOnName;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_levelParams, l_Lean_instInhabitedInductiveVal_default,
};
use crate::r#gen::Lean::Elab::DeclModifiers::l_Lean_Elab_instInhabitedModifiers_default;
use crate::r#gen::Lean::Elab::PreDefinition::PartialFixpoint::Main::l_Lean_Elab_partialFixpoint;
use crate::r#gen::Lean::Elab::PreDefinition::PartialFixpoint::{
    initialize_Lean_Elab_PreDefinition_PartialFixpoint,
    runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint,
};
use crate::r#gen::Lean::Elab::Tactic::Rewrite::{
    initialize_Lean_Elab_Tactic_Rewrite, runtime_initialize_Lean_Elab_Tactic_Rewrite,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_TermElabM_run___redArg, l_Lean_Elab_Term_addTermInfo_x27,
    l_Lean_Elab_Term_applyAttributes___boxed, l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed,
    l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_findConstVal_x3f, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_Environment_hasUnsafe, l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_constName, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar,
    l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_mvarId_x21, l_Lean_Expr_replaceFVars,
    l_Lean_Expr_sort___override, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Linter::UnusedVariables::{
    initialize_Lean_Linter_UnusedVariables, runtime_initialize_Lean_Linter_UnusedVariables,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalContext_get_x21, l_Lean_LocalDecl_type};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkCongrFun, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqMP,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::Eqns::l_Lean_Meta_getEqnsFor_x3f;
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_introNCore;
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    l_Lean_MVarId_replace, l_Lean_MVarId_replaceTargetEq,
};
use crate::r#gen::Lean::Meta::Tactic::Revert::l_Lean_MVarId_revert;
use crate::r#gen::Lean::Meta::Tactic::Rewrite::l_Lean_MVarId_rewrite;
use crate::r#gen::Lean::Meta::Tactic::Simp::{
    initialize_Lean_Meta_Tactic_Simp, runtime_initialize_Lean_Meta_Tactic_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_unfoldDefinition;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::Util::ReplaceExpr::lean_replace_expr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7,
    lean_apply_9, lean_box, lean_box_usize, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 105, 110, 100, 117, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,1608544935946222304 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 111, 105, 110, 100, 117, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,3502425036608280386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,2651562642360992291 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,12335972212032040814 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,14539449796098371388 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,17843507417996841225 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,427699689256578448 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,10442633407676750609 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,11307015034773232980 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,7247352532244850606 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,15297487843248306108 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,((( 793488904 as usize) << 1) | 1) as *mut LeanObject,11119998828780069236 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__24_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,9520679986626222715 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__24_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__24_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__25_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__25_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__25_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__26_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__24_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__25_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,15195699116450830683 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__26_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__26_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__27_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__26_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,17464980470838499246 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__27_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__27_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0_value:
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
static mut l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Command_instInhabitedCoinductiveElabData: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_addFunctorPostfix___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [95, 102, 117, 110, 99, 116, 111, 114, 0],
    };
static mut l_Lean_Elab_Command_addFunctorPostfix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_addFunctorPostfix___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_addFunctorPostfix___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_addFunctorPostfix___closed__0_value)
                as *mut LeanObject,
            9680752266908919265 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_addFunctorPostfix___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_addFunctorPostfix___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 111, 105, 110, 100, 117, 99, 116, 105,
            118, 101, 0,
        ],
    };
static mut l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1_value: LeanStringObject<45> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 45,
        m_capacity: 45,
        m_length: 44,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 111, 109, 109, 97, 110, 100, 46, 114,
            101, 109, 111, 118, 101, 70, 117, 110, 99, 116, 111, 114, 80, 111, 115, 116, 102, 105,
            120, 73, 110, 67, 116, 111, 114, 0,
        ],
    };
static mut l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 78, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,258 as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0_value
) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [100, 105, 100, 32, 110, 111, 116, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 116, 104, 101, 111, 114, 101, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 120, 105, 115, 116, 101, 110, 116, 105, 97, 108, 95, 101, 113, 117, 105, 118, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__2_value) as *mut LeanObject,7633731374219804931 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [102, 117, 110, 99, 116, 111, 114, 95, 117, 110, 102, 111, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0_value) as *mut LeanObject,8131757204198247059 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 101, 115, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [84, 104, 101, 32, 99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 32, 111, 102, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 105, 115, 32, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [84, 104, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 105, 115, 32, 111, 102, 32, 116, 104, 101, 32, 116, 121, 112, 101, 58, 32, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [71, 101, 110, 101, 114, 97, 116, 105, 110, 103, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 58, 32, 0]};
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(0 as *mut LeanObject)] };
pub static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1_value) as *mut LeanObject;
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6_value) as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 97, 115, 101, 115, 95, 101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__2_value) as *mut LeanObject,18063153688627580660 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__5_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 95, 97, 115, 95, 101, 108, 105, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__5_value) as *mut LeanObject,6393735541240574290 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8_value: LeanArrayObject<2> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__7_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 32, 98, 101, 32, 113, 117, 97, 110, 116, 105, 102, 105, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 105, 115, 116, 101, 110, 116, 105, 97, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__0_value) as *mut LeanObject,5617260025639121538 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCoinductive___closed__0_value: LeanStringObject<14> =
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
        m_data: [69, 108, 97, 98, 111, 114, 97, 116, 105, 110, 103, 58, 32, 0],
    };
static mut l_Lean_Elab_Command_elabCoinductive___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCoinductive___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Command_elabCoinductive___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCoinductive___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    v___x_4359_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_;
    v___x_4360_ = 0;
    v___x_4361_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__27_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_;
    v___x_4362_ = l_Lean_registerTraceClass(v___x_4359_, v___x_4360_, v___x_4361_);
    return v___x_4362_;
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2____boxed(
    mut v_a_4363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4364_: *mut LeanObject = core::ptr::null_mut();
    v_res_4364_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_();
    return v_res_4364_;
}
pub unsafe fn _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1()
-> *mut LeanObject {
    let mut v___x_4367_: u8 = 0;
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    v___x_4367_ = 0;
    v___x_4368_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0;
    v___x_4369_ = l_Lean_Elab_instInhabitedModifiers_default;
    v___x_4370_ = lean_box(0);
    v___x_4371_ = lean_box(0);
    v___x_4372_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_4372_, 0, v___x_4371_);
    lean_ctor_set(v___x_4372_, 1, v___x_4370_);
    lean_ctor_set(v___x_4372_, 2, v___x_4371_);
    lean_ctor_set(v___x_4372_, 3, v___x_4369_);
    lean_ctor_set(v___x_4372_, 4, v___x_4368_);
    lean_ctor_set_uint8(
        v___x_4372_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_4367_,
    );
    return v___x_4372_;
}
pub unsafe fn _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default() -> *mut LeanObject
{
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    v___x_4373_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1_once
        ),
        _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1,
    );
    return v___x_4373_;
}
pub unsafe fn _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData() -> *mut LeanObject {
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    v___x_4374_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
    return v___x_4374_;
}
pub unsafe fn l_Lean_Elab_Command_addFunctorPostfix(
    mut v_x_4378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    v___x_4379_ = l_Lean_Elab_Command_addFunctorPostfix___closed__1;
    v___x_4380_ = l_Lean_Name_append(v_x_4378_, v___x_4379_);
    return v___x_4380_;
}
pub unsafe fn l_Lean_Elab_Command_removeFunctorPostfix(
    mut v_x_4381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4382_: u8 = 0;
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_view_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4382_ = l_Lean_Name_hasMacroScopes(v_x_4381_);
                if v___x_4382_ == 0 {
                    v___x_4383_ = l_Lean_Name_getPrefix(v_x_4381_);
                    lean_dec(v_x_4381_);
                    return v___x_4383_;
                } else {
                    v_view_4384_ = l_Lean_extractMacroScopes(v_x_4381_);
                    v_name_4385_ = lean_ctor_get(v_view_4384_, 0);
                    v_imported_4386_ = lean_ctor_get(v_view_4384_, 1);
                    v_ctx_4387_ = lean_ctor_get(v_view_4384_, 2);
                    v_scopes_4388_ = lean_ctor_get(v_view_4384_, 3);
                    v_isSharedCheck_4397_ = (!lean_is_exclusive(v_view_4384_)) as u8;
                    if v_isSharedCheck_4397_ == 0 {
                        v___x_4390_ = v_view_4384_;
                        v_isShared_4391_ = v_isSharedCheck_4397_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_scopes_4388_);
                        lean_inc(v_ctx_4387_);
                        lean_inc(v_imported_4386_);
                        lean_inc(v_name_4385_);
                        lean_dec(v_view_4384_);
                        v___x_4390_ = lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4397_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4392_ = l_Lean_Name_getPrefix(v_name_4385_);
                lean_dec(v_name_4385_);
                if v_isShared_4391_ == 0 {
                    lean_ctor_set(v___x_4390_, 0, v___x_4392_);
                    v___x_4394_ = v___x_4390_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4392_);
                    lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_imported_4386_);
                    lean_ctor_set(v_reuseFailAlloc_4396_, 2, v_ctx_4387_);
                    lean_ctor_set(v_reuseFailAlloc_4396_, 3, v_scopes_4388_);
                    v___x_4394_ = v_reuseFailAlloc_4396_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4395_ = l_Lean_MacroScopesView_review(v___x_4394_);
                return v___x_4395_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Elab_Command_removeFunctorPostfixInCtor_spec__0(
    mut v_msg_4398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    v___x_4399_ = lean_box(0);
    v___x_4400_ = lean_panic_fn_borrowed(v___x_4399_, v_msg_4398_);
    return v___x_4400_;
}
pub unsafe fn _init_l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3() -> *mut LeanObject
{
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    v___x_4404_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2;
    v___x_4405_ = lean_unsigned_to_nat(13);
    v___x_4406_ = lean_unsigned_to_nat(124);
    v___x_4407_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1;
    v___x_4408_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0;
    v___x_4409_ = l_mkPanicMessageWithDecl(
        v___x_4408_,
        v___x_4407_,
        v___x_4406_,
        v___x_4405_,
        v___x_4404_,
    );
    return v___x_4409_;
}
pub unsafe fn l_Lean_Elab_Command_removeFunctorPostfixInCtor(
    mut v_x_4410_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4410_) == 1 {
        let mut v_pre_4411_: *mut LeanObject = core::ptr::null_mut();
        let mut v_str_4412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4411_ = lean_ctor_get(v_x_4410_, 0);
        lean_inc(v_pre_4411_);
        v_str_4412_ = lean_ctor_get(v_x_4410_, 1);
        lean_inc_ref(v_str_4412_);
        lean_dec_ref_known(v_x_4410_, 2);
        v___x_4413_ = l_Lean_Elab_Command_removeFunctorPostfix(v_pre_4411_);
        v___x_4414_ = l_Lean_Name_str___override(v___x_4413_, v_str_4412_);
        return v___x_4414_;
    } else {
        let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4410_);
        v___x_4415_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3_once
            ),
            _init_l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3,
        );
        v___x_4416_ =
            l_panic___at___00Lean_Elab_Command_removeFunctorPostfixInCtor_spec__0(v___x_4415_);
        return v___x_4416_;
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(
    mut v_goal_4422_: *mut LeanObject,
    mut v_eq_4423_: *mut LeanObject,
    mut v_symm_4424_: u8,
    mut v_a_4425_: *mut LeanObject,
    mut v_a_4426_: *mut LeanObject,
    mut v_a_4427_: *mut LeanObject,
    mut v_a_4428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eNew_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqProof_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4441_: u8 = 0;
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut v_a_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_goal_4422_);
                v___x_4430_ =
                    l_Lean_MVarId_getType(v_goal_4422_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_);
                if lean_obj_tag(v___x_4430_) == 0 {
                    v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
                    lean_inc(v_a_4431_);
                    lean_dec_ref_known(v___x_4430_, 1);
                    v___x_4432_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0;
                    lean_inc(v_goal_4422_);
                    v___x_4433_ = l_Lean_MVarId_rewrite(
                        v_goal_4422_,
                        v_a_4431_,
                        v_eq_4423_,
                        v_symm_4424_,
                        v___x_4432_,
                        v_a_4425_,
                        v_a_4426_,
                        v_a_4427_,
                        v_a_4428_,
                    );
                    if lean_obj_tag(v___x_4433_) == 0 {
                        v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
                        lean_inc(v_a_4434_);
                        lean_dec_ref_known(v___x_4433_, 1);
                        v_eNew_4435_ = lean_ctor_get(v_a_4434_, 0);
                        lean_inc_ref(v_eNew_4435_);
                        v_eqProof_4436_ = lean_ctor_get(v_a_4434_, 1);
                        lean_inc_ref(v_eqProof_4436_);
                        lean_dec(v_a_4434_);
                        v___x_4437_ = l_Lean_MVarId_replaceTargetEq(
                            v_goal_4422_,
                            v_eNew_4435_,
                            v_eqProof_4436_,
                            v_a_4425_,
                            v_a_4426_,
                            v_a_4427_,
                            v_a_4428_,
                        );
                        return v___x_4437_;
                    } else {
                        lean_dec(v_goal_4422_);
                        v_a_4438_ = lean_ctor_get(v___x_4433_, 0);
                        v_isSharedCheck_4445_ = (!lean_is_exclusive(v___x_4433_)) as u8;
                        if v_isSharedCheck_4445_ == 0 {
                            v___x_4440_ = v___x_4433_;
                            v_isShared_4441_ = v_isSharedCheck_4445_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4438_);
                            lean_dec(v___x_4433_);
                            v___x_4440_ = lean_box(0);
                            v_isShared_4441_ = v_isSharedCheck_4445_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_eq_4423_);
                    lean_dec(v_goal_4422_);
                    v_a_4446_ = lean_ctor_get(v___x_4430_, 0);
                    v_isSharedCheck_4453_ = (!lean_is_exclusive(v___x_4430_)) as u8;
                    if v_isSharedCheck_4453_ == 0 {
                        v___x_4448_ = v___x_4430_;
                        v_isShared_4449_ = v_isSharedCheck_4453_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4446_);
                        lean_dec(v___x_4430_);
                        v___x_4448_ = lean_box(0);
                        v_isShared_4449_ = v_isSharedCheck_4453_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4441_ == 0 {
                    v___x_4443_ = v___x_4440_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
                    v___x_4443_ = v_reuseFailAlloc_4444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4443_;
            }
            3 => {
                if v_isShared_4449_ == 0 {
                    v___x_4451_ = v___x_4448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
                    v___x_4451_ = v_reuseFailAlloc_4452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___boxed(
    mut v_goal_4454_: *mut LeanObject,
    mut v_eq_4455_: *mut LeanObject,
    mut v_symm_4456_: *mut LeanObject,
    mut v_a_4457_: *mut LeanObject,
    mut v_a_4458_: *mut LeanObject,
    mut v_a_4459_: *mut LeanObject,
    mut v_a_4460_: *mut LeanObject,
    mut v_a_4461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_4462_: u8 = 0;
    let mut v_res_4463_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_4462_ = (lean_unbox(v_symm_4456_) as u8);
    v_res_4463_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(
        v_goal_4454_,
        v_eq_4455_,
        v_symm_boxed_4462_,
        v_a_4457_,
        v_a_4458_,
        v_a_4459_,
        v_a_4460_,
    );
    lean_dec(v_a_4460_);
    lean_dec_ref(v_a_4459_);
    lean_dec(v_a_4458_);
    lean_dec_ref(v_a_4457_);
    return v_res_4463_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(
    mut v_e_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4467_: u8 = 0;
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4487_: u8 = 0;
    let mut v_unused_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4467_ = l_Lean_Expr_hasMVar(v_e_4464_);
                if v___x_4467_ == 0 {
                    v___x_4468_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4468_, 0, v_e_4464_);
                    return v___x_4468_;
                } else {
                    v___x_4469_ = lean_st_ref_get(v___y_4465_);
                    v_mctx_4470_ = lean_ctor_get(v___x_4469_, 0);
                    lean_inc_ref(v_mctx_4470_);
                    lean_dec(v___x_4469_);
                    v___x_4471_ = l_Lean_instantiateMVarsCore(v_mctx_4470_, v_e_4464_);
                    v_fst_4472_ = lean_ctor_get(v___x_4471_, 0);
                    lean_inc(v_fst_4472_);
                    v_snd_4473_ = lean_ctor_get(v___x_4471_, 1);
                    lean_inc(v_snd_4473_);
                    lean_dec_ref(v___x_4471_);
                    v___x_4474_ = lean_st_ref_take(v___y_4465_);
                    v_cache_4475_ = lean_ctor_get(v___x_4474_, 1);
                    v_zetaDeltaFVarIds_4476_ = lean_ctor_get(v___x_4474_, 2);
                    v_postponed_4477_ = lean_ctor_get(v___x_4474_, 3);
                    v_diag_4478_ = lean_ctor_get(v___x_4474_, 4);
                    v_isSharedCheck_4487_ = (!lean_is_exclusive(v___x_4474_)) as u8;
                    if v_isSharedCheck_4487_ == 0 {
                        v_unused_4488_ = lean_ctor_get(v___x_4474_, 0);
                        lean_dec(v_unused_4488_);
                        v___x_4480_ = v___x_4474_;
                        v_isShared_4481_ = v_isSharedCheck_4487_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4478_);
                        lean_inc(v_postponed_4477_);
                        lean_inc(v_zetaDeltaFVarIds_4476_);
                        lean_inc(v_cache_4475_);
                        lean_dec(v___x_4474_);
                        v___x_4480_ = lean_box(0);
                        v_isShared_4481_ = v_isSharedCheck_4487_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4481_ == 0 {
                    lean_ctor_set(v___x_4480_, 0, v_snd_4473_);
                    v___x_4483_ = v___x_4480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_snd_4473_);
                    lean_ctor_set(v_reuseFailAlloc_4486_, 1, v_cache_4475_);
                    lean_ctor_set(v_reuseFailAlloc_4486_, 2, v_zetaDeltaFVarIds_4476_);
                    lean_ctor_set(v_reuseFailAlloc_4486_, 3, v_postponed_4477_);
                    lean_ctor_set(v_reuseFailAlloc_4486_, 4, v_diag_4478_);
                    v___x_4483_ = v_reuseFailAlloc_4486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4484_ = lean_st_ref_set(v___y_4465_, v___x_4483_);
                v___x_4485_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4485_, 0, v_fst_4472_);
                return v___x_4485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg___boxed(
    mut v_e_4489_: *mut LeanObject,
    mut v___y_4490_: *mut LeanObject,
    mut v___y_4491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4492_: *mut LeanObject = core::ptr::null_mut();
    v_res_4492_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_e_4489_, v___y_4490_);
    lean_dec(v___y_4490_);
    return v_res_4492_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(
    mut v_e_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    v___x_4499_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_e_4493_, v___y_4495_);
    return v___x_4499_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___boxed(
    mut v_e_4500_: *mut LeanObject,
    mut v___y_4501_: *mut LeanObject,
    mut v___y_4502_: *mut LeanObject,
    mut v___y_4503_: *mut LeanObject,
    mut v___y_4504_: *mut LeanObject,
    mut v___y_4505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4506_: *mut LeanObject = core::ptr::null_mut();
    v_res_4506_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(v_e_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
    lean_dec(v___y_4504_);
    lean_dec_ref(v___y_4503_);
    lean_dec(v___y_4502_);
    lean_dec_ref(v___y_4501_);
    return v_res_4506_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(
    mut v_k_4507_: *mut LeanObject,
    mut v_b_4508_: *mut LeanObject,
    mut v_c_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
    mut v___y_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4513_);
    lean_inc_ref(v___y_4512_);
    lean_inc(v___y_4511_);
    lean_inc_ref(v___y_4510_);
    v___x_4515_ = lean_apply_7(
        v_k_4507_,
        v_b_4508_,
        v_c_4509_,
        v___y_4510_,
        v___y_4511_,
        v___y_4512_,
        v___y_4513_,
        lean_box(0),
    );
    return v___x_4515_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed(
    mut v_k_4516_: *mut LeanObject,
    mut v_b_4517_: *mut LeanObject,
    mut v_c_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
    mut v___y_4520_: *mut LeanObject,
    mut v___y_4521_: *mut LeanObject,
    mut v___y_4522_: *mut LeanObject,
    mut v___y_4523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4524_: *mut LeanObject = core::ptr::null_mut();
    v_res_4524_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(v_k_4516_, v_b_4517_, v_c_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
    lean_dec(v___y_4522_);
    lean_dec_ref(v___y_4521_);
    lean_dec(v___y_4520_);
    lean_dec_ref(v___y_4519_);
    return v_res_4524_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(
    mut v_type_4525_: *mut LeanObject,
    mut v_k_4526_: *mut LeanObject,
    mut v_cleanupAnnotations_4527_: u8,
    mut v_whnfType_4528_: u8,
    mut v___y_4529_: *mut LeanObject,
    mut v___y_4530_: *mut LeanObject,
    mut v___y_4531_: *mut LeanObject,
    mut v___y_4532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4539_: u8 = 0;
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4543_: u8 = 0;
    let mut v_a_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4547_: u8 = 0;
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4534_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_4534_, 0, v_k_4526_);
                v___x_4535_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_4525_,
                    v___f_4534_,
                    v_cleanupAnnotations_4527_,
                    v_whnfType_4528_,
                    v___y_4529_,
                    v___y_4530_,
                    v___y_4531_,
                    v___y_4532_,
                );
                if lean_obj_tag(v___x_4535_) == 0 {
                    v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
                    v_isSharedCheck_4543_ = (!lean_is_exclusive(v___x_4535_)) as u8;
                    if v_isSharedCheck_4543_ == 0 {
                        v___x_4538_ = v___x_4535_;
                        v_isShared_4539_ = v_isSharedCheck_4543_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4536_);
                        lean_dec(v___x_4535_);
                        v___x_4538_ = lean_box(0);
                        v_isShared_4539_ = v_isSharedCheck_4543_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4544_ = lean_ctor_get(v___x_4535_, 0);
                    v_isSharedCheck_4551_ = (!lean_is_exclusive(v___x_4535_)) as u8;
                    if v_isSharedCheck_4551_ == 0 {
                        v___x_4546_ = v___x_4535_;
                        v_isShared_4547_ = v_isSharedCheck_4551_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4544_);
                        lean_dec(v___x_4535_);
                        v___x_4546_ = lean_box(0);
                        v_isShared_4547_ = v_isSharedCheck_4551_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4539_ == 0 {
                    v___x_4541_ = v___x_4538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
                    v___x_4541_ = v_reuseFailAlloc_4542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4541_;
            }
            3 => {
                if v_isShared_4547_ == 0 {
                    v___x_4549_ = v___x_4546_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
                    v___x_4549_ = v_reuseFailAlloc_4550_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___boxed(
    mut v_type_4552_: *mut LeanObject,
    mut v_k_4553_: *mut LeanObject,
    mut v_cleanupAnnotations_4554_: *mut LeanObject,
    mut v_whnfType_4555_: *mut LeanObject,
    mut v___y_4556_: *mut LeanObject,
    mut v___y_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4561_: u8 = 0;
    let mut v_whnfType_boxed_4562_: u8 = 0;
    let mut v_res_4563_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4561_ = (lean_unbox(v_cleanupAnnotations_4554_) as u8);
    v_whnfType_boxed_4562_ = (lean_unbox(v_whnfType_4555_) as u8);
    v_res_4563_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_4552_, v_k_4553_, v_cleanupAnnotations_boxed_4561_, v_whnfType_boxed_4562_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
    lean_dec(v___y_4559_);
    lean_dec_ref(v___y_4558_);
    lean_dec(v___y_4557_);
    lean_dec_ref(v___y_4556_);
    return v_res_4563_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(
    mut v_00_u03b1_4564_: *mut LeanObject,
    mut v_type_4565_: *mut LeanObject,
    mut v_k_4566_: *mut LeanObject,
    mut v_cleanupAnnotations_4567_: u8,
    mut v_whnfType_4568_: u8,
    mut v___y_4569_: *mut LeanObject,
    mut v___y_4570_: *mut LeanObject,
    mut v___y_4571_: *mut LeanObject,
    mut v___y_4572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    v___x_4574_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_4565_, v_k_4566_, v_cleanupAnnotations_4567_, v_whnfType_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
    return v___x_4574_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___boxed(
    mut v_00_u03b1_4575_: *mut LeanObject,
    mut v_type_4576_: *mut LeanObject,
    mut v_k_4577_: *mut LeanObject,
    mut v_cleanupAnnotations_4578_: *mut LeanObject,
    mut v_whnfType_4579_: *mut LeanObject,
    mut v___y_4580_: *mut LeanObject,
    mut v___y_4581_: *mut LeanObject,
    mut v___y_4582_: *mut LeanObject,
    mut v___y_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4585_: u8 = 0;
    let mut v_whnfType_boxed_4586_: u8 = 0;
    let mut v_res_4587_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4585_ = (lean_unbox(v_cleanupAnnotations_4578_) as u8);
    v_whnfType_boxed_4586_ = (lean_unbox(v_whnfType_4579_) as u8);
    v_res_4587_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(v_00_u03b1_4575_, v_type_4576_, v_k_4577_, v_cleanupAnnotations_boxed_4585_, v_whnfType_boxed_4586_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
    lean_dec(v___y_4583_);
    lean_dec_ref(v___y_4582_);
    lean_dec(v___y_4581_);
    lean_dec_ref(v___y_4580_);
    return v_res_4587_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(
    mut v_name_4588_: *mut LeanObject,
    mut v_levelParams_4589_: *mut LeanObject,
    mut v_type_4590_: *mut LeanObject,
    mut v_value_4591_: *mut LeanObject,
    mut v_hints_4592_: *mut LeanObject,
    mut v___y_4593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4597_: u8 = 0;
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4604_: u8 = 0;
    let mut v___x_4605_: u8 = 0;
    let mut v___x_4606_: u8 = 0;
    let mut v_env_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: u8 = 0;
    let mut v___x_4609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4595_ = lean_st_ref_get(v___y_4593_);
                v_env_4607_ = lean_ctor_get(v___x_4595_, 0);
                lean_inc_ref_n(v_env_4607_, 2);
                lean_dec(v___x_4595_);
                v___x_4608_ = l_Lean_Environment_hasUnsafe(v_env_4607_, v_type_4590_);
                if v___x_4608_ == 0 {
                    v___x_4609_ = l_Lean_Environment_hasUnsafe(v_env_4607_, v_value_4591_);
                    v___y_4604_ = v___x_4609_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_env_4607_);
                    v___y_4604_ = v___x_4608_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc(v_name_4588_);
                v___x_4598_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4598_, 0, v_name_4588_);
                lean_ctor_set(v___x_4598_, 1, v_levelParams_4589_);
                lean_ctor_set(v___x_4598_, 2, v_type_4590_);
                v___x_4599_ = lean_box(0);
                v___x_4600_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4600_, 0, v_name_4588_);
                lean_ctor_set(v___x_4600_, 1, v___x_4599_);
                v___x_4601_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_4601_, 0, v___x_4598_);
                lean_ctor_set(v___x_4601_, 1, v_value_4591_);
                lean_ctor_set(v___x_4601_, 2, v_hints_4592_);
                lean_ctor_set(v___x_4601_, 3, v___x_4600_);
                lean_ctor_set_uint8(
                    v___x_4601_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___y_4597_,
                );
                v___x_4602_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4602_, 0, v___x_4601_);
                return v___x_4602_;
            }
            2 => {
                if v___y_4604_ == 0 {
                    v___x_4605_ = 1;
                    v___y_4597_ = v___x_4605_;
                    state = 1;
                    continue;
                } else {
                    v___x_4606_ = 0;
                    v___y_4597_ = v___x_4606_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg___boxed(
    mut v_name_4610_: *mut LeanObject,
    mut v_levelParams_4611_: *mut LeanObject,
    mut v_type_4612_: *mut LeanObject,
    mut v_value_4613_: *mut LeanObject,
    mut v_hints_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4617_: *mut LeanObject = core::ptr::null_mut();
    v_res_4617_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v_name_4610_, v_levelParams_4611_, v_type_4612_, v_value_4613_, v_hints_4614_, v___y_4615_);
    lean_dec(v___y_4615_);
    return v_res_4617_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(
    mut v_name_4618_: *mut LeanObject,
    mut v_levelParams_4619_: *mut LeanObject,
    mut v_type_4620_: *mut LeanObject,
    mut v_value_4621_: *mut LeanObject,
    mut v_hints_4622_: *mut LeanObject,
    mut v___y_4623_: *mut LeanObject,
    mut v___y_4624_: *mut LeanObject,
    mut v___y_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    v___x_4628_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v_name_4618_, v_levelParams_4619_, v_type_4620_, v_value_4621_, v_hints_4622_, v___y_4626_);
    return v___x_4628_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___boxed(
    mut v_name_4629_: *mut LeanObject,
    mut v_levelParams_4630_: *mut LeanObject,
    mut v_type_4631_: *mut LeanObject,
    mut v_value_4632_: *mut LeanObject,
    mut v_hints_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
    mut v___y_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4639_: *mut LeanObject = core::ptr::null_mut();
    v_res_4639_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(v_name_4629_, v_levelParams_4630_, v_type_4631_, v_value_4632_, v_hints_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
    lean_dec(v___y_4637_);
    lean_dec_ref(v___y_4636_);
    lean_dec(v___y_4635_);
    lean_dec_ref(v___y_4634_);
    return v_res_4639_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(
    mut v_a_4640_: *mut LeanObject,
    mut v_a_4641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4640_) == 0 {
                    v___x_4642_ = l_List_reverse___redArg(v_a_4641_);
                    return v___x_4642_;
                } else {
                    v_head_4643_ = lean_ctor_get(v_a_4640_, 0);
                    v_tail_4644_ = lean_ctor_get(v_a_4640_, 1);
                    v_isSharedCheck_4653_ = (!lean_is_exclusive(v_a_4640_)) as u8;
                    if v_isSharedCheck_4653_ == 0 {
                        v___x_4646_ = v_a_4640_;
                        v_isShared_4647_ = v_isSharedCheck_4653_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4644_);
                        lean_inc(v_head_4643_);
                        lean_dec(v_a_4640_);
                        v___x_4646_ = lean_box(0);
                        v_isShared_4647_ = v_isSharedCheck_4653_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4648_ = l_Lean_mkLevelParam(v_head_4643_);
                if v_isShared_4647_ == 0 {
                    lean_ctor_set(v___x_4646_, 1, v_a_4641_);
                    lean_ctor_set(v___x_4646_, 0, v___x_4648_);
                    v___x_4650_ = v___x_4646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4648_);
                    lean_ctor_set(v_reuseFailAlloc_4652_, 1, v_a_4641_);
                    v___x_4650_ = v_reuseFailAlloc_4652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4640_ = v_tail_4644_;
                v_a_4641_ = v___x_4650_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(
    mut v_x_4654_: *mut LeanObject,
    mut v_x_4655_: *mut LeanObject,
    mut v_x_4656_: *mut LeanObject,
    mut v_x_4657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4662_: u8 = 0;
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: u8 = 0;
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4658_ = lean_ctor_get(v_x_4654_, 0);
                v_vs_4659_ = lean_ctor_get(v_x_4654_, 1);
                v_isSharedCheck_4683_ = (!lean_is_exclusive(v_x_4654_)) as u8;
                if v_isSharedCheck_4683_ == 0 {
                    v___x_4661_ = v_x_4654_;
                    v_isShared_4662_ = v_isSharedCheck_4683_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_4659_);
                    lean_inc(v_ks_4658_);
                    lean_dec(v_x_4654_);
                    v___x_4661_ = lean_box(0);
                    v_isShared_4662_ = v_isSharedCheck_4683_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4663_ = lean_array_get_size(v_ks_4658_);
                v___x_4664_ = lean_nat_dec_lt(v_x_4655_, v___x_4663_);
                if v___x_4664_ == 0 {
                    lean_dec(v_x_4655_);
                    v___x_4665_ = lean_array_push(v_ks_4658_, v_x_4656_);
                    v___x_4666_ = lean_array_push(v_vs_4659_, v_x_4657_);
                    if v_isShared_4662_ == 0 {
                        lean_ctor_set(v___x_4661_, 1, v___x_4666_);
                        lean_ctor_set(v___x_4661_, 0, v___x_4665_);
                        v___x_4668_ = v___x_4661_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4669_, 0, v___x_4665_);
                        lean_ctor_set(v_reuseFailAlloc_4669_, 1, v___x_4666_);
                        v___x_4668_ = v_reuseFailAlloc_4669_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4670_ = lean_array_fget_borrowed(v_ks_4658_, v_x_4655_);
                    v___x_4671_ = l_Lean_instBEqMVarId_beq(v_x_4656_, v_k_x27_4670_);
                    if v___x_4671_ == 0 {
                        if v_isShared_4662_ == 0 {
                            v___x_4673_ = v___x_4661_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_ks_4658_);
                            lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_vs_4659_);
                            v___x_4673_ = v_reuseFailAlloc_4677_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4678_ = lean_array_fset(v_ks_4658_, v_x_4655_, v_x_4656_);
                        v___x_4679_ = lean_array_fset(v_vs_4659_, v_x_4655_, v_x_4657_);
                        lean_dec(v_x_4655_);
                        if v_isShared_4662_ == 0 {
                            lean_ctor_set(v___x_4661_, 1, v___x_4679_);
                            lean_ctor_set(v___x_4661_, 0, v___x_4678_);
                            v___x_4681_ = v___x_4661_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4678_);
                            lean_ctor_set(v_reuseFailAlloc_4682_, 1, v___x_4679_);
                            v___x_4681_ = v_reuseFailAlloc_4682_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4668_;
            }
            3 => {
                v___x_4674_ = lean_unsigned_to_nat(1);
                v___x_4675_ = lean_nat_add(v_x_4655_, v___x_4674_);
                lean_dec(v_x_4655_);
                v_x_4654_ = v___x_4673_;
                v_x_4655_ = v___x_4675_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(
    mut v_n_4684_: *mut LeanObject,
    mut v_k_4685_: *mut LeanObject,
    mut v_v_4686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    v___x_4687_ = lean_unsigned_to_nat(0);
    v___x_4688_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_n_4684_, v___x_4687_, v_k_4685_, v_v_4686_);
    return v___x_4688_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0()
-> usize {
    let mut v___x_4689_: usize = 0;
    let mut v___x_4690_: usize = 0;
    let mut v___x_4691_: usize = 0;
    v___x_4689_ = 5usize;
    v___x_4690_ = 1usize;
    v___x_4691_ = lean_usize_shift_left(v___x_4690_, v___x_4689_);
    return v___x_4691_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1()
-> usize {
    let mut v___x_4692_: usize = 0;
    let mut v___x_4693_: usize = 0;
    let mut v___x_4694_: usize = 0;
    v___x_4692_ = 1usize;
    v___x_4693_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0);
    v___x_4694_ = lean_usize_sub(v___x_4693_, v___x_4692_);
    return v___x_4694_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    v___x_4695_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_4695_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(
    mut v_x_4696_: *mut LeanObject,
    mut v_x_4697_: usize,
    mut v_x_4698_: usize,
    mut v_x_4699_: *mut LeanObject,
    mut v_x_4700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: usize = 0;
    let mut v___x_4703_: usize = 0;
    let mut v___x_4704_: usize = 0;
    let mut v___x_4705_: usize = 0;
    let mut v_j_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: u8 = 0;
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4711_: u8 = 0;
    let mut v_v_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4726_: u8 = 0;
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4732_: u8 = 0;
    let mut v_node_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4736_: u8 = 0;
    let mut v___x_4737_: usize = 0;
    let mut v___x_4738_: usize = 0;
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4743_: u8 = 0;
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4745_: u8 = 0;
    let mut v_unused_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4751_: u8 = 0;
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4756_: u8 = 0;
    let mut v_ks_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: usize = 0;
    let mut v___x_4763_: u8 = 0;
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: u8 = 0;
    let mut v_reuseFailAlloc_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4696_) == 0 {
                    v_es_4701_ = lean_ctor_get(v_x_4696_, 0);
                    v___x_4702_ = 5usize;
                    v___x_4703_ = 1usize;
                    v___x_4704_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1);
                    v___x_4705_ = lean_usize_land(v_x_4697_, v___x_4704_);
                    v_j_4706_ = lean_usize_to_nat(v___x_4705_);
                    v___x_4707_ = lean_array_get_size(v_es_4701_);
                    v___x_4708_ = lean_nat_dec_lt(v_j_4706_, v___x_4707_);
                    if v___x_4708_ == 0 {
                        lean_dec(v_j_4706_);
                        lean_dec(v_x_4700_);
                        lean_dec(v_x_4699_);
                        return v_x_4696_;
                    } else {
                        lean_inc_ref(v_es_4701_);
                        v_isSharedCheck_4745_ = (!lean_is_exclusive(v_x_4696_)) as u8;
                        if v_isSharedCheck_4745_ == 0 {
                            v_unused_4746_ = lean_ctor_get(v_x_4696_, 0);
                            lean_dec(v_unused_4746_);
                            v___x_4710_ = v_x_4696_;
                            v_isShared_4711_ = v_isSharedCheck_4745_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4696_);
                            v___x_4710_ = lean_box(0);
                            v_isShared_4711_ = v_isSharedCheck_4745_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4747_ = lean_ctor_get(v_x_4696_, 0);
                    v_vs_4748_ = lean_ctor_get(v_x_4696_, 1);
                    v_isSharedCheck_4768_ = (!lean_is_exclusive(v_x_4696_)) as u8;
                    if v_isSharedCheck_4768_ == 0 {
                        v___x_4750_ = v_x_4696_;
                        v_isShared_4751_ = v_isSharedCheck_4768_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_4748_);
                        lean_inc(v_ks_4747_);
                        lean_dec(v_x_4696_);
                        v___x_4750_ = lean_box(0);
                        v_isShared_4751_ = v_isSharedCheck_4768_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4712_ = lean_array_fget(v_es_4701_, v_j_4706_);
                v___x_4713_ = lean_box(0);
                v_xs_x27_4714_ = lean_array_fset(v_es_4701_, v_j_4706_, v___x_4713_);
                match lean_obj_tag(v_v_4712_) {
                    0 => {
                        v_key_4721_ = lean_ctor_get(v_v_4712_, 0);
                        v_val_4722_ = lean_ctor_get(v_v_4712_, 1);
                        v_isSharedCheck_4732_ = (!lean_is_exclusive(v_v_4712_)) as u8;
                        if v_isSharedCheck_4732_ == 0 {
                            v___x_4724_ = v_v_4712_;
                            v_isShared_4725_ = v_isSharedCheck_4732_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4722_);
                            lean_inc(v_key_4721_);
                            lean_dec(v_v_4712_);
                            v___x_4724_ = lean_box(0);
                            v_isShared_4725_ = v_isSharedCheck_4732_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4733_ = lean_ctor_get(v_v_4712_, 0);
                        v_isSharedCheck_4743_ = (!lean_is_exclusive(v_v_4712_)) as u8;
                        if v_isSharedCheck_4743_ == 0 {
                            v___x_4735_ = v_v_4712_;
                            v_isShared_4736_ = v_isSharedCheck_4743_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_4733_);
                            lean_dec(v_v_4712_);
                            v___x_4735_ = lean_box(0);
                            v_isShared_4736_ = v_isSharedCheck_4743_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4744_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4744_, 0, v_x_4699_);
                        lean_ctor_set(v___x_4744_, 1, v_x_4700_);
                        v___y_4716_ = v___x_4744_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4717_ = lean_array_fset(v_xs_x27_4714_, v_j_4706_, v___y_4716_);
                lean_dec(v_j_4706_);
                if v_isShared_4711_ == 0 {
                    lean_ctor_set(v___x_4710_, 0, v___x_4717_);
                    v___x_4719_ = v___x_4710_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4717_);
                    v___x_4719_ = v_reuseFailAlloc_4720_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4719_;
            }
            4 => {
                v___x_4726_ = l_Lean_instBEqMVarId_beq(v_x_4699_, v_key_4721_);
                if v___x_4726_ == 0 {
                    lean_del_object(v___x_4724_);
                    v___x_4727_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4721_,
                        v_val_4722_,
                        v_x_4699_,
                        v_x_4700_,
                    );
                    v___x_4728_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4728_, 0, v___x_4727_);
                    v___y_4716_ = v___x_4728_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4722_);
                    lean_dec(v_key_4721_);
                    if v_isShared_4725_ == 0 {
                        lean_ctor_set(v___x_4724_, 1, v_x_4700_);
                        lean_ctor_set(v___x_4724_, 0, v_x_4699_);
                        v___x_4730_ = v___x_4724_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_x_4699_);
                        lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_x_4700_);
                        v___x_4730_ = v_reuseFailAlloc_4731_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4716_ = v___x_4730_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4737_ = lean_usize_shift_right(v_x_4697_, v___x_4702_);
                v___x_4738_ = lean_usize_add(v_x_4698_, v___x_4703_);
                v___x_4739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_node_4733_, v___x_4737_, v___x_4738_, v_x_4699_, v_x_4700_);
                if v_isShared_4736_ == 0 {
                    lean_ctor_set(v___x_4735_, 0, v___x_4739_);
                    v___x_4741_ = v___x_4735_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4739_);
                    v___x_4741_ = v_reuseFailAlloc_4742_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4716_ = v___x_4741_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4751_ == 0 {
                    v___x_4753_ = v___x_4750_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_ks_4747_);
                    lean_ctor_set(v_reuseFailAlloc_4767_, 1, v_vs_4748_);
                    v___x_4753_ = v_reuseFailAlloc_4767_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4754_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v___x_4753_, v_x_4699_, v_x_4700_);
                v___x_4762_ = 7usize;
                v___x_4763_ = lean_usize_dec_le(v___x_4762_, v_x_4698_);
                if v___x_4763_ == 0 {
                    v___x_4764_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4754_);
                    v___x_4765_ = lean_unsigned_to_nat(4);
                    v___x_4766_ = lean_nat_dec_lt(v___x_4764_, v___x_4765_);
                    lean_dec(v___x_4764_);
                    v___y_4756_ = v___x_4766_;
                    state = 10;
                    continue;
                } else {
                    v___y_4756_ = v___x_4763_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4756_ == 0 {
                    v_ks_4757_ = lean_ctor_get(v_newNode_4754_, 0);
                    lean_inc_ref(v_ks_4757_);
                    v_vs_4758_ = lean_ctor_get(v_newNode_4754_, 1);
                    lean_inc_ref(v_vs_4758_);
                    lean_dec_ref(v_newNode_4754_);
                    v___x_4759_ = lean_unsigned_to_nat(0);
                    v___x_4760_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2);
                    v___x_4761_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_x_4698_, v_ks_4757_, v_vs_4758_, v___x_4759_, v___x_4760_);
                    lean_dec_ref(v_vs_4758_);
                    lean_dec_ref(v_ks_4757_);
                    return v___x_4761_;
                } else {
                    return v_newNode_4754_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(
    mut v_depth_4769_: usize,
    mut v_keys_4770_: *mut LeanObject,
    mut v_vals_4771_: *mut LeanObject,
    mut v_i_4772_: *mut LeanObject,
    mut v_entries_4773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: u8 = 0;
    let mut v_k_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: u64 = 0;
    let mut v_h_4779_: usize = 0;
    let mut v___x_4780_: usize = 0;
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: usize = 0;
    let mut v___x_4783_: usize = 0;
    let mut v___x_4784_: usize = 0;
    let mut v_h_4785_: usize = 0;
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4774_ = lean_array_get_size(v_keys_4770_);
                v___x_4775_ = lean_nat_dec_lt(v_i_4772_, v___x_4774_);
                if v___x_4775_ == 0 {
                    lean_dec(v_i_4772_);
                    return v_entries_4773_;
                } else {
                    v_k_4776_ = lean_array_fget_borrowed(v_keys_4770_, v_i_4772_);
                    v_v_4777_ = lean_array_fget_borrowed(v_vals_4771_, v_i_4772_);
                    v___x_4778_ = l_Lean_instHashableMVarId_hash(v_k_4776_);
                    v_h_4779_ = lean_uint64_to_usize(v___x_4778_);
                    v___x_4780_ = 5usize;
                    v___x_4781_ = lean_unsigned_to_nat(1);
                    v___x_4782_ = 1usize;
                    v___x_4783_ = lean_usize_sub(v_depth_4769_, v___x_4782_);
                    v___x_4784_ = lean_usize_mul(v___x_4780_, v___x_4783_);
                    v_h_4785_ = lean_usize_shift_right(v_h_4779_, v___x_4784_);
                    v___x_4786_ = lean_nat_add(v_i_4772_, v___x_4781_);
                    lean_dec(v_i_4772_);
                    lean_inc(v_v_4777_);
                    lean_inc(v_k_4776_);
                    v___x_4787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_entries_4773_, v_h_4785_, v_depth_4769_, v_k_4776_, v_v_4777_);
                    v_i_4772_ = v___x_4786_;
                    v_entries_4773_ = v___x_4787_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg___boxed(
    mut v_depth_4789_: *mut LeanObject,
    mut v_keys_4790_: *mut LeanObject,
    mut v_vals_4791_: *mut LeanObject,
    mut v_i_4792_: *mut LeanObject,
    mut v_entries_4793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4794_: usize = 0;
    let mut v_res_4795_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4794_ = lean_unbox_usize(v_depth_4789_);
    lean_dec(v_depth_4789_);
    v_res_4795_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_boxed_4794_, v_keys_4790_, v_vals_4791_, v_i_4792_, v_entries_4793_);
    lean_dec_ref(v_vals_4791_);
    lean_dec_ref(v_keys_4790_);
    return v_res_4795_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___boxed(
    mut v_x_4796_: *mut LeanObject,
    mut v_x_4797_: *mut LeanObject,
    mut v_x_4798_: *mut LeanObject,
    mut v_x_4799_: *mut LeanObject,
    mut v_x_4800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_8781__boxed_4801_: usize = 0;
    let mut v_x_8782__boxed_4802_: usize = 0;
    let mut v_res_4803_: *mut LeanObject = core::ptr::null_mut();
    v_x_8781__boxed_4801_ = lean_unbox_usize(v_x_4797_);
    lean_dec(v_x_4797_);
    v_x_8782__boxed_4802_ = lean_unbox_usize(v_x_4798_);
    lean_dec(v_x_4798_);
    v_res_4803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_4796_, v_x_8781__boxed_4801_, v_x_8782__boxed_4802_, v_x_4799_, v_x_4800_);
    return v_res_4803_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(
    mut v_x_4804_: *mut LeanObject,
    mut v_x_4805_: *mut LeanObject,
    mut v_x_4806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4807_: u64 = 0;
    let mut v___x_4808_: usize = 0;
    let mut v___x_4809_: usize = 0;
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    v___x_4807_ = l_Lean_instHashableMVarId_hash(v_x_4805_);
    v___x_4808_ = lean_uint64_to_usize(v___x_4807_);
    v___x_4809_ = 1usize;
    v___x_4810_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_4804_, v___x_4808_, v___x_4809_, v_x_4805_, v_x_4806_);
    return v___x_4810_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(
    mut v_mvarId_4811_: *mut LeanObject,
    mut v_val_4812_: *mut LeanObject,
    mut v___y_4813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4823_: u8 = 0;
    let mut v_depth_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4847_: u8 = 0;
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4815_ = lean_st_ref_take(v___y_4813_);
                v_mctx_4816_ = lean_ctor_get(v___x_4815_, 0);
                v_cache_4817_ = lean_ctor_get(v___x_4815_, 1);
                v_zetaDeltaFVarIds_4818_ = lean_ctor_get(v___x_4815_, 2);
                v_postponed_4819_ = lean_ctor_get(v___x_4815_, 3);
                v_diag_4820_ = lean_ctor_get(v___x_4815_, 4);
                v_isSharedCheck_4848_ = (!lean_is_exclusive(v___x_4815_)) as u8;
                if v_isSharedCheck_4848_ == 0 {
                    v___x_4822_ = v___x_4815_;
                    v_isShared_4823_ = v_isSharedCheck_4848_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_4820_);
                    lean_inc(v_postponed_4819_);
                    lean_inc(v_zetaDeltaFVarIds_4818_);
                    lean_inc(v_cache_4817_);
                    lean_inc(v_mctx_4816_);
                    lean_dec(v___x_4815_);
                    v___x_4822_ = lean_box(0);
                    v_isShared_4823_ = v_isSharedCheck_4848_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4824_ = lean_ctor_get(v_mctx_4816_, 0);
                v_levelAssignDepth_4825_ = lean_ctor_get(v_mctx_4816_, 1);
                v_lmvarCounter_4826_ = lean_ctor_get(v_mctx_4816_, 2);
                v_mvarCounter_4827_ = lean_ctor_get(v_mctx_4816_, 3);
                v_lDecls_4828_ = lean_ctor_get(v_mctx_4816_, 4);
                v_decls_4829_ = lean_ctor_get(v_mctx_4816_, 5);
                v_userNames_4830_ = lean_ctor_get(v_mctx_4816_, 6);
                v_lAssignment_4831_ = lean_ctor_get(v_mctx_4816_, 7);
                v_eAssignment_4832_ = lean_ctor_get(v_mctx_4816_, 8);
                v_dAssignment_4833_ = lean_ctor_get(v_mctx_4816_, 9);
                v_isSharedCheck_4847_ = (!lean_is_exclusive(v_mctx_4816_)) as u8;
                if v_isSharedCheck_4847_ == 0 {
                    v___x_4835_ = v_mctx_4816_;
                    v_isShared_4836_ = v_isSharedCheck_4847_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_4833_);
                    lean_inc(v_eAssignment_4832_);
                    lean_inc(v_lAssignment_4831_);
                    lean_inc(v_userNames_4830_);
                    lean_inc(v_decls_4829_);
                    lean_inc(v_lDecls_4828_);
                    lean_inc(v_mvarCounter_4827_);
                    lean_inc(v_lmvarCounter_4826_);
                    lean_inc(v_levelAssignDepth_4825_);
                    lean_inc(v_depth_4824_);
                    lean_dec(v_mctx_4816_);
                    v___x_4835_ = lean_box(0);
                    v_isShared_4836_ = v_isSharedCheck_4847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4837_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_4832_, v_mvarId_4811_, v_val_4812_);
                if v_isShared_4836_ == 0 {
                    lean_ctor_set(v___x_4835_, 8, v___x_4837_);
                    v___x_4839_ = v___x_4835_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_depth_4824_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 1, v_levelAssignDepth_4825_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 2, v_lmvarCounter_4826_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 3, v_mvarCounter_4827_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 4, v_lDecls_4828_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 5, v_decls_4829_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 6, v_userNames_4830_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 7, v_lAssignment_4831_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 8, v___x_4837_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 9, v_dAssignment_4833_);
                    v___x_4839_ = v_reuseFailAlloc_4846_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4823_ == 0 {
                    lean_ctor_set(v___x_4822_, 0, v___x_4839_);
                    v___x_4841_ = v___x_4822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4839_);
                    lean_ctor_set(v_reuseFailAlloc_4845_, 1, v_cache_4817_);
                    lean_ctor_set(v_reuseFailAlloc_4845_, 2, v_zetaDeltaFVarIds_4818_);
                    lean_ctor_set(v_reuseFailAlloc_4845_, 3, v_postponed_4819_);
                    lean_ctor_set(v_reuseFailAlloc_4845_, 4, v_diag_4820_);
                    v___x_4841_ = v_reuseFailAlloc_4845_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4842_ = lean_st_ref_set(v___y_4813_, v___x_4841_);
                v___x_4843_ = lean_box(0);
                v___x_4844_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4844_, 0, v___x_4843_);
                return v___x_4844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg___boxed(
    mut v_mvarId_4849_: *mut LeanObject,
    mut v_val_4850_: *mut LeanObject,
    mut v___y_4851_: *mut LeanObject,
    mut v___y_4852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4853_: *mut LeanObject = core::ptr::null_mut();
    v_res_4853_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_4849_, v_val_4850_, v___y_4851_);
    lean_dec(v___y_4851_);
    return v_res_4853_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(
    mut v_msgData_4854_: *mut LeanObject,
    mut v___y_4855_: *mut LeanObject,
    mut v___y_4856_: *mut LeanObject,
    mut v___y_4857_: *mut LeanObject,
    mut v___y_4858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    v___x_4860_ = lean_st_ref_get(v___y_4858_);
    v_env_4861_ = lean_ctor_get(v___x_4860_, 0);
    lean_inc_ref(v_env_4861_);
    lean_dec(v___x_4860_);
    v___x_4862_ = lean_st_ref_get(v___y_4856_);
    v_mctx_4863_ = lean_ctor_get(v___x_4862_, 0);
    lean_inc_ref(v_mctx_4863_);
    lean_dec(v___x_4862_);
    v_lctx_4864_ = lean_ctor_get(v___y_4855_, 2);
    v_options_4865_ = lean_ctor_get(v___y_4857_, 2);
    lean_inc_ref(v_options_4865_);
    lean_inc_ref(v_lctx_4864_);
    v___x_4866_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4866_, 0, v_env_4861_);
    lean_ctor_set(v___x_4866_, 1, v_mctx_4863_);
    lean_ctor_set(v___x_4866_, 2, v_lctx_4864_);
    lean_ctor_set(v___x_4866_, 3, v_options_4865_);
    v___x_4867_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4867_, 0, v___x_4866_);
    lean_ctor_set(v___x_4867_, 1, v_msgData_4854_);
    v___x_4868_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4868_, 0, v___x_4867_);
    return v___x_4868_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(
    mut v_msgData_4869_: *mut LeanObject,
    mut v___y_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4875_: *mut LeanObject = core::ptr::null_mut();
    v_res_4875_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
    lean_dec(v___y_4873_);
    lean_dec_ref(v___y_4872_);
    lean_dec(v___y_4871_);
    lean_dec_ref(v___y_4870_);
    return v_res_4875_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(
    mut v_msg_4876_: *mut LeanObject,
    mut v___y_4877_: *mut LeanObject,
    mut v___y_4878_: *mut LeanObject,
    mut v___y_4879_: *mut LeanObject,
    mut v___y_4880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4887_: u8 = 0;
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4882_ = lean_ctor_get(v___y_4879_, 5);
                v___x_4883_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
                v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
                v_isSharedCheck_4892_ = (!lean_is_exclusive(v___x_4883_)) as u8;
                if v_isSharedCheck_4892_ == 0 {
                    v___x_4886_ = v___x_4883_;
                    v_isShared_4887_ = v_isSharedCheck_4892_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4884_);
                    lean_dec(v___x_4883_);
                    v___x_4886_ = lean_box(0);
                    v_isShared_4887_ = v_isSharedCheck_4892_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4882_);
                v___x_4888_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4888_, 0, v_ref_4882_);
                lean_ctor_set(v___x_4888_, 1, v_a_4884_);
                if v_isShared_4887_ == 0 {
                    lean_ctor_set_tag(v___x_4886_, 1);
                    lean_ctor_set(v___x_4886_, 0, v___x_4888_);
                    v___x_4890_ = v___x_4886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4888_);
                    v___x_4890_ = v_reuseFailAlloc_4891_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(
    mut v_msg_4893_: *mut LeanObject,
    mut v___y_4894_: *mut LeanObject,
    mut v___y_4895_: *mut LeanObject,
    mut v___y_4896_: *mut LeanObject,
    mut v___y_4897_: *mut LeanObject,
    mut v___y_4898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4899_: *mut LeanObject = core::ptr::null_mut();
    v_res_4899_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_);
    lean_dec(v___y_4897_);
    lean_dec_ref(v___y_4896_);
    lean_dec(v___y_4895_);
    lean_dec_ref(v___y_4894_);
    return v_res_4899_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(
    mut v_a_4900_: *mut LeanObject,
    mut v_b_4901_: *mut LeanObject,
    mut v___y_4902_: *mut LeanObject,
    mut v___y_4903_: *mut LeanObject,
    mut v___y_4904_: *mut LeanObject,
    mut v___y_4905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4912_: u8 = 0;
    let mut v___x_4913_: u8 = 0;
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4907_ = lean_ctor_get(v_a_4900_, 0);
                v_start_4908_ = lean_ctor_get(v_a_4900_, 1);
                v_stop_4909_ = lean_ctor_get(v_a_4900_, 2);
                v_isSharedCheck_4924_ = (!lean_is_exclusive(v_a_4900_)) as u8;
                if v_isSharedCheck_4924_ == 0 {
                    v___x_4911_ = v_a_4900_;
                    v_isShared_4912_ = v_isSharedCheck_4924_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_4909_);
                    lean_inc(v_start_4908_);
                    lean_inc(v_array_4907_);
                    lean_dec(v_a_4900_);
                    v___x_4911_ = lean_box(0);
                    v_isShared_4912_ = v_isSharedCheck_4924_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4913_ = lean_nat_dec_lt(v_start_4908_, v_stop_4909_);
                if v___x_4913_ == 0 {
                    lean_del_object(v___x_4911_);
                    lean_dec(v_stop_4909_);
                    lean_dec(v_start_4908_);
                    lean_dec_ref(v_array_4907_);
                    v___x_4914_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4914_, 0, v_b_4901_);
                    return v___x_4914_;
                } else {
                    v___x_4915_ = lean_array_fget_borrowed(v_array_4907_, v_start_4908_);
                    lean_inc(v___x_4915_);
                    v___x_4916_ = l_Lean_Meta_mkCongrFun(
                        v_b_4901_,
                        v___x_4915_,
                        v___y_4902_,
                        v___y_4903_,
                        v___y_4904_,
                        v___y_4905_,
                    );
                    if lean_obj_tag(v___x_4916_) == 0 {
                        v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
                        lean_inc(v_a_4917_);
                        lean_dec_ref_known(v___x_4916_, 1);
                        v___x_4918_ = lean_unsigned_to_nat(1);
                        v___x_4919_ = lean_nat_add(v_start_4908_, v___x_4918_);
                        lean_dec(v_start_4908_);
                        if v_isShared_4912_ == 0 {
                            lean_ctor_set(v___x_4911_, 1, v___x_4919_);
                            v___x_4921_ = v___x_4911_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4923_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_array_4907_);
                            lean_ctor_set(v_reuseFailAlloc_4923_, 1, v___x_4919_);
                            lean_ctor_set(v_reuseFailAlloc_4923_, 2, v_stop_4909_);
                            v___x_4921_ = v_reuseFailAlloc_4923_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4911_);
                        lean_dec(v_stop_4909_);
                        lean_dec(v_start_4908_);
                        lean_dec_ref(v_array_4907_);
                        return v___x_4916_;
                    }
                }
            }
            2 => {
                v_a_4900_ = v___x_4921_;
                v_b_4901_ = v_a_4917_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(
    mut v_a_4925_: *mut LeanObject,
    mut v_b_4926_: *mut LeanObject,
    mut v___y_4927_: *mut LeanObject,
    mut v___y_4928_: *mut LeanObject,
    mut v___y_4929_: *mut LeanObject,
    mut v___y_4930_: *mut LeanObject,
    mut v___y_4931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4932_: *mut LeanObject = core::ptr::null_mut();
    v_res_4932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_4925_, v_b_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
    lean_dec(v___y_4930_);
    lean_dec_ref(v___y_4929_);
    lean_dec(v___y_4928_);
    lean_dec_ref(v___y_4927_);
    return v_res_4932_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(
    mut v_levels_4933_: *mut LeanObject,
    mut v___x_4934_: *mut LeanObject,
    mut v_sz_4935_: usize,
    mut v_i_4936_: usize,
    mut v_bs_4937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4938_: u8 = 0;
    let mut v_v_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: usize = 0;
    let mut v___x_4948_: usize = 0;
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4938_ = lean_usize_dec_lt(v_i_4936_, v_sz_4935_);
                if v___x_4938_ == 0 {
                    lean_dec(v_levels_4933_);
                    return v_bs_4937_;
                } else {
                    v_v_4939_ = lean_array_uget_borrowed(v_bs_4937_, v_i_4936_);
                    v_toConstantVal_4940_ = lean_ctor_get(v_v_4939_, 0);
                    v_name_4941_ = lean_ctor_get(v_toConstantVal_4940_, 0);
                    lean_inc(v_name_4941_);
                    v___x_4942_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4943_ = lean_array_uset(v_bs_4937_, v_i_4936_, v___x_4942_);
                    v___x_4944_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4941_);
                    lean_inc(v_levels_4933_);
                    v___x_4945_ = l_Lean_mkConst(v___x_4944_, v_levels_4933_);
                    v___x_4946_ = l_Lean_mkAppN(v___x_4945_, v___x_4934_);
                    v___x_4947_ = 1usize;
                    v___x_4948_ = lean_usize_add(v_i_4936_, v___x_4947_);
                    v___x_4949_ = lean_array_uset(v_bs_x27_4943_, v_i_4936_, v___x_4946_);
                    v_i_4936_ = v___x_4948_;
                    v_bs_4937_ = v___x_4949_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(
    mut v_levels_4951_: *mut LeanObject,
    mut v___x_4952_: *mut LeanObject,
    mut v_sz_4953_: *mut LeanObject,
    mut v_i_4954_: *mut LeanObject,
    mut v_bs_4955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4956_: usize = 0;
    let mut v_i_boxed_4957_: usize = 0;
    let mut v_res_4958_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4956_ = lean_unbox_usize(v_sz_4953_);
    lean_dec(v_sz_4953_);
    v_i_boxed_4957_ = lean_unbox_usize(v_i_4954_);
    lean_dec(v_i_4954_);
    v_res_4958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_4951_, v___x_4952_, v_sz_boxed_4956_, v_i_boxed_4957_, v_bs_4955_);
    lean_dec_ref(v___x_4952_);
    return v_res_4958_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    v___x_4960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0;
    v___x_4961_ = l_Lean_stringToMessageData(v___x_4960_);
    return v___x_4961_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(
    mut v_infos_4965_: *mut LeanObject,
    mut v_numParams_4966_: *mut LeanObject,
    mut v___x_4967_: *mut LeanObject,
    mut v_name_4968_: *mut LeanObject,
    mut v_levels_4969_: *mut LeanObject,
    mut v_args_4970_: *mut LeanObject,
    mut v_x_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
    mut v___y_4973_: *mut LeanObject,
    mut v___y_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4988_: usize = 0;
    let mut v___x_4989_: usize = 0;
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4999_: u8 = 0;
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: u8 = 0;
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: u8 = 0;
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: u8 = 0;
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: u8 = 0;
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5044_: u8 = 0;
    let mut v_a_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5048_: u8 = 0;
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5052_: u8 = 0;
    let mut v_a_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5056_: u8 = 0;
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5060_: u8 = 0;
    let mut v_reuseFailAlloc_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5062_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4977_ = lean_array_get_size(v_infos_4965_);
                v___x_4978_ = lean_nat_sub(v_numParams_4966_, v___x_4977_);
                lean_inc(v___x_4967_);
                lean_inc_ref(v_args_4970_);
                v___x_4979_ = l_Array_toSubarray___redArg(v_args_4970_, v___x_4967_, v___x_4978_);
                v___x_4980_ = lean_array_get_size(v_args_4970_);
                v___x_4981_ =
                    l_Array_toSubarray___redArg(v_args_4970_, v_numParams_4966_, v___x_4980_);
                lean_inc_n(v_name_4968_, 2);
                v___x_4982_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4968_);
                lean_inc_n(v_levels_4969_, 3);
                lean_inc(v___x_4982_);
                v___x_4983_ = l_Lean_mkConst(v___x_4982_, v_levels_4969_);
                v___x_4984_ = l_Subarray_copy___redArg(v___x_4979_);
                v___x_4985_ = l_Lean_mkAppN(v___x_4983_, v___x_4984_);
                lean_inc_ref(v___x_4981_);
                v___x_4986_ = l_Subarray_copy___redArg(v___x_4981_);
                v___x_4987_ = l_Lean_mkAppN(v___x_4985_, v___x_4986_);
                v_sz_4988_ = lean_array_size(v_infos_4965_);
                v___x_4989_ = 0usize;
                v___x_4990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_4969_, v___x_4984_, v_sz_4988_, v___x_4989_, v_infos_4965_);
                v___x_4991_ = l_Lean_mkConst(v_name_4968_, v_levels_4969_);
                lean_inc_ref(v___x_4984_);
                v___x_4992_ = l_Array_append___redArg(v___x_4984_, v___x_4990_);
                lean_dec_ref(v___x_4990_);
                v___x_4993_ = l_Array_append___redArg(v___x_4992_, v___x_4986_);
                v___x_4994_ = l_Lean_mkAppN(v___x_4991_, v___x_4993_);
                lean_dec_ref(v___x_4993_);
                v___x_4995_ = l_Lean_Meta_mkEq(
                    v___x_4987_,
                    v___x_4994_,
                    v___y_4972_,
                    v___y_4973_,
                    v___y_4974_,
                    v___y_4975_,
                );
                if lean_obj_tag(v___x_4995_) == 0 {
                    v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
                    v_isSharedCheck_5062_ = (!lean_is_exclusive(v___x_4995_)) as u8;
                    if v_isSharedCheck_5062_ == 0 {
                        v___x_4998_ = v___x_4995_;
                        v_isShared_4999_ = v_isSharedCheck_5062_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4996_);
                        lean_dec(v___x_4995_);
                        v___x_4998_ = lean_box(0);
                        v_isShared_4999_ = v_isSharedCheck_5062_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4986_);
                    lean_dec_ref(v___x_4984_);
                    lean_dec(v___x_4982_);
                    lean_dec_ref(v___x_4981_);
                    lean_dec(v_levels_4969_);
                    lean_dec(v_name_4968_);
                    lean_dec(v___x_4967_);
                    return v___x_4995_;
                }
            }
            1 => {
                if v_isShared_4999_ == 0 {
                    lean_ctor_set_tag(v___x_4998_, 1);
                    v___x_5001_ = v___x_4998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5061_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_4996_);
                    v___x_5001_ = v_reuseFailAlloc_5061_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5002_ = 0;
                v___x_5003_ = lean_box(0);
                v___x_5004_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_5001_,
                    v___x_5002_,
                    v___x_5003_,
                    v___y_4972_,
                    v___y_4973_,
                    v___y_4974_,
                    v___y_4975_,
                );
                if lean_obj_tag(v___x_5004_) == 0 {
                    v_a_5005_ = lean_ctor_get(v___x_5004_, 0);
                    lean_inc(v_a_5005_);
                    lean_dec_ref_known(v___x_5004_, 1);
                    v___x_5006_ = l_Lean_Meta_getEqnsFor_x3f(
                        v___x_4982_,
                        v___y_4972_,
                        v___y_4973_,
                        v___y_4974_,
                        v___y_4975_,
                    );
                    if lean_obj_tag(v___x_5006_) == 0 {
                        v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
                        lean_inc(v_a_5007_);
                        lean_dec_ref_known(v___x_5006_, 1);
                        if lean_obj_tag(v_a_5007_) == 1 {
                            v_val_5015_ = lean_ctor_get(v_a_5007_, 0);
                            lean_inc(v_val_5015_);
                            lean_dec_ref_known(v_a_5007_, 1);
                            v___x_5016_ = lean_array_get_size(v_val_5015_);
                            v___x_5017_ = lean_unsigned_to_nat(1);
                            v___x_5018_ = lean_nat_dec_eq(v___x_5016_, v___x_5017_);
                            if v___x_5018_ == 0 {
                                lean_dec(v_val_5015_);
                                lean_dec(v_a_5005_);
                                lean_dec_ref(v___x_4986_);
                                lean_dec_ref(v___x_4984_);
                                lean_dec_ref(v___x_4981_);
                                lean_dec(v_levels_4969_);
                                lean_dec(v_name_4968_);
                                lean_dec(v___x_4967_);
                                v___y_5009_ = v___y_4972_;
                                v___y_5010_ = v___y_4973_;
                                v___y_5011_ = v___y_4974_;
                                v___y_5012_ = v___y_4975_;
                                state = 3;
                                continue;
                            } else {
                                v___x_5019_ = lean_array_fget(v_val_5015_, v___x_4967_);
                                lean_dec(v___x_4967_);
                                lean_dec(v_val_5015_);
                                v___x_5020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3;
                                v___x_5021_ = l_Lean_Name_append(v_name_4968_, v___x_5020_);
                                lean_inc(v_levels_4969_);
                                v___x_5022_ = l_Lean_mkConst(v___x_5021_, v_levels_4969_);
                                v___x_5023_ = l_Lean_mkConst(v___x_5019_, v_levels_4969_);
                                v___x_5024_ = l_Lean_mkAppN(v___x_5023_, v___x_4984_);
                                v___x_5025_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v___x_4981_, v___x_5024_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
                                if lean_obj_tag(v___x_5025_) == 0 {
                                    v_a_5026_ = lean_ctor_get(v___x_5025_, 0);
                                    lean_inc(v_a_5026_);
                                    lean_dec_ref_known(v___x_5025_, 1);
                                    v___x_5027_ = l_Lean_Expr_mvarId_x21(v_a_5005_);
                                    v___x_5028_ = 0;
                                    v___x_5029_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_5027_, v___x_5022_, v___x_5028_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
                                    if lean_obj_tag(v___x_5029_) == 0 {
                                        v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
                                        lean_inc(v_a_5030_);
                                        lean_dec_ref_known(v___x_5029_, 1);
                                        v___x_5031_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_5030_, v_a_5026_, v___y_4973_);
                                        if lean_obj_tag(v___x_5031_) == 0 {
                                            lean_dec_ref_known(v___x_5031_, 1);
                                            v___x_5032_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_5005_, v___y_4973_);
                                            if lean_obj_tag(v___x_5032_) == 0 {
                                                v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
                                                lean_inc(v_a_5033_);
                                                lean_dec_ref_known(v___x_5032_, 1);
                                                v___x_5034_ = l_Array_append___redArg(
                                                    v___x_4984_,
                                                    v___x_4986_,
                                                );
                                                lean_dec_ref(v___x_4986_);
                                                v___x_5035_ = 1;
                                                v___x_5036_ = l_Lean_Meta_mkLambdaFVars(
                                                    v___x_5034_,
                                                    v_a_5033_,
                                                    v___x_5028_,
                                                    v___x_5018_,
                                                    v___x_5028_,
                                                    v___x_5018_,
                                                    v___x_5035_,
                                                    v___y_4972_,
                                                    v___y_4973_,
                                                    v___y_4974_,
                                                    v___y_4975_,
                                                );
                                                lean_dec_ref(v___x_5034_);
                                                return v___x_5036_;
                                            } else {
                                                lean_dec_ref(v___x_4986_);
                                                lean_dec_ref(v___x_4984_);
                                                return v___x_5032_;
                                            }
                                        } else {
                                            lean_dec(v_a_5005_);
                                            lean_dec_ref(v___x_4986_);
                                            lean_dec_ref(v___x_4984_);
                                            v_a_5037_ = lean_ctor_get(v___x_5031_, 0);
                                            v_isSharedCheck_5044_ =
                                                (!lean_is_exclusive(v___x_5031_)) as u8;
                                            if v_isSharedCheck_5044_ == 0 {
                                                v___x_5039_ = v___x_5031_;
                                                v_isShared_5040_ = v_isSharedCheck_5044_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5037_);
                                                lean_dec(v___x_5031_);
                                                v___x_5039_ = lean_box(0);
                                                v_isShared_5040_ = v_isSharedCheck_5044_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_5026_);
                                        lean_dec(v_a_5005_);
                                        lean_dec_ref(v___x_4986_);
                                        lean_dec_ref(v___x_4984_);
                                        v_a_5045_ = lean_ctor_get(v___x_5029_, 0);
                                        v_isSharedCheck_5052_ =
                                            (!lean_is_exclusive(v___x_5029_)) as u8;
                                        if v_isSharedCheck_5052_ == 0 {
                                            v___x_5047_ = v___x_5029_;
                                            v_isShared_5048_ = v_isSharedCheck_5052_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5045_);
                                            lean_dec(v___x_5029_);
                                            v___x_5047_ = lean_box(0);
                                            v_isShared_5048_ = v_isSharedCheck_5052_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_5022_);
                                    lean_dec(v_a_5005_);
                                    lean_dec_ref(v___x_4986_);
                                    lean_dec_ref(v___x_4984_);
                                    return v___x_5025_;
                                }
                            }
                        } else {
                            lean_dec(v_a_5007_);
                            lean_dec(v_a_5005_);
                            lean_dec_ref(v___x_4986_);
                            lean_dec_ref(v___x_4984_);
                            lean_dec_ref(v___x_4981_);
                            lean_dec(v_levels_4969_);
                            lean_dec(v_name_4968_);
                            lean_dec(v___x_4967_);
                            v___y_5009_ = v___y_4972_;
                            v___y_5010_ = v___y_4973_;
                            v___y_5011_ = v___y_4974_;
                            v___y_5012_ = v___y_4975_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5005_);
                        lean_dec_ref(v___x_4986_);
                        lean_dec_ref(v___x_4984_);
                        lean_dec_ref(v___x_4981_);
                        lean_dec(v_levels_4969_);
                        lean_dec(v_name_4968_);
                        lean_dec(v___x_4967_);
                        v_a_5053_ = lean_ctor_get(v___x_5006_, 0);
                        v_isSharedCheck_5060_ = (!lean_is_exclusive(v___x_5006_)) as u8;
                        if v_isSharedCheck_5060_ == 0 {
                            v___x_5055_ = v___x_5006_;
                            v_isShared_5056_ = v_isSharedCheck_5060_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5053_);
                            lean_dec(v___x_5006_);
                            v___x_5055_ = lean_box(0);
                            v_isShared_5056_ = v_isSharedCheck_5060_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_4986_);
                    lean_dec_ref(v___x_4984_);
                    lean_dec(v___x_4982_);
                    lean_dec_ref(v___x_4981_);
                    lean_dec(v_levels_4969_);
                    lean_dec(v_name_4968_);
                    lean_dec(v___x_4967_);
                    return v___x_5004_;
                }
            }
            3 => {
                v___x_5013_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1);
                v___x_5014_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_5013_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_);
                return v___x_5014_;
            }
            4 => {
                if v_isShared_5040_ == 0 {
                    v___x_5042_ = v___x_5039_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
                    v___x_5042_ = v_reuseFailAlloc_5043_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5042_;
            }
            6 => {
                if v_isShared_5048_ == 0 {
                    v___x_5050_ = v___x_5047_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
                    v___x_5050_ = v_reuseFailAlloc_5051_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5050_;
            }
            8 => {
                if v_isShared_5056_ == 0 {
                    v___x_5058_ = v___x_5055_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5059_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5053_);
                    v___x_5058_ = v_reuseFailAlloc_5059_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed(
    mut v_infos_5063_: *mut LeanObject,
    mut v_numParams_5064_: *mut LeanObject,
    mut v___x_5065_: *mut LeanObject,
    mut v_name_5066_: *mut LeanObject,
    mut v_levels_5067_: *mut LeanObject,
    mut v_args_5068_: *mut LeanObject,
    mut v_x_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
    mut v___y_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
    mut v___y_5074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5075_: *mut LeanObject = core::ptr::null_mut();
    v_res_5075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(v_infos_5063_, v_numParams_5064_, v___x_5065_, v_name_5066_, v_levels_5067_, v_args_5068_, v_x_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
    lean_dec(v___y_5073_);
    lean_dec_ref(v___y_5072_);
    lean_dec(v___y_5071_);
    lean_dec_ref(v___y_5070_);
    lean_dec_ref(v_x_5069_);
    return v_res_5075_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0()
-> f64 {
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: f64 = 0.0;
    v___x_5076_ = lean_unsigned_to_nat(0);
    v___x_5077_ = lean_float_of_nat(v___x_5076_);
    return v___x_5077_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(
    mut v_cls_5081_: *mut LeanObject,
    mut v_msg_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
    mut v___y_5084_: *mut LeanObject,
    mut v___y_5085_: *mut LeanObject,
    mut v___y_5086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5106_: u8 = 0;
    let mut v_tid_5107_: u64 = 0;
    let mut v_traces_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5111_: u8 = 0;
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: f64 = 0.0;
    let mut v___x_5114_: u8 = 0;
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5132_: u8 = 0;
    let mut v_isSharedCheck_5133_: u8 = 0;
    let mut v_isSharedCheck_5134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5088_ = lean_ctor_get(v___y_5085_, 5);
                v___x_5089_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_);
                v_a_5090_ = lean_ctor_get(v___x_5089_, 0);
                v_isSharedCheck_5134_ = (!lean_is_exclusive(v___x_5089_)) as u8;
                if v_isSharedCheck_5134_ == 0 {
                    v___x_5092_ = v___x_5089_;
                    v_isShared_5093_ = v_isSharedCheck_5134_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5090_);
                    lean_dec(v___x_5089_);
                    v___x_5092_ = lean_box(0);
                    v_isShared_5093_ = v_isSharedCheck_5134_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5094_ = lean_st_ref_take(v___y_5086_);
                v_traceState_5095_ = lean_ctor_get(v___x_5094_, 4);
                v_env_5096_ = lean_ctor_get(v___x_5094_, 0);
                v_nextMacroScope_5097_ = lean_ctor_get(v___x_5094_, 1);
                v_ngen_5098_ = lean_ctor_get(v___x_5094_, 2);
                v_auxDeclNGen_5099_ = lean_ctor_get(v___x_5094_, 3);
                v_cache_5100_ = lean_ctor_get(v___x_5094_, 5);
                v_messages_5101_ = lean_ctor_get(v___x_5094_, 6);
                v_infoState_5102_ = lean_ctor_get(v___x_5094_, 7);
                v_snapshotTasks_5103_ = lean_ctor_get(v___x_5094_, 8);
                v_isSharedCheck_5133_ = (!lean_is_exclusive(v___x_5094_)) as u8;
                if v_isSharedCheck_5133_ == 0 {
                    v___x_5105_ = v___x_5094_;
                    v_isShared_5106_ = v_isSharedCheck_5133_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5103_);
                    lean_inc(v_infoState_5102_);
                    lean_inc(v_messages_5101_);
                    lean_inc(v_cache_5100_);
                    lean_inc(v_traceState_5095_);
                    lean_inc(v_auxDeclNGen_5099_);
                    lean_inc(v_ngen_5098_);
                    lean_inc(v_nextMacroScope_5097_);
                    lean_inc(v_env_5096_);
                    lean_dec(v___x_5094_);
                    v___x_5105_ = lean_box(0);
                    v_isShared_5106_ = v_isSharedCheck_5133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5107_ = lean_ctor_get_uint64(
                    v_traceState_5095_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5108_ = lean_ctor_get(v_traceState_5095_, 0);
                v_isSharedCheck_5132_ = (!lean_is_exclusive(v_traceState_5095_)) as u8;
                if v_isSharedCheck_5132_ == 0 {
                    v___x_5110_ = v_traceState_5095_;
                    v_isShared_5111_ = v_isSharedCheck_5132_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_5108_);
                    lean_dec(v_traceState_5095_);
                    v___x_5110_ = lean_box(0);
                    v_isShared_5111_ = v_isSharedCheck_5132_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5112_ = lean_box(0);
                v___x_5113_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
                v___x_5114_ = 0;
                v___x_5115_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1;
                v___x_5116_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_5116_, 0, v_cls_5081_);
                lean_ctor_set(v___x_5116_, 1, v___x_5112_);
                lean_ctor_set(v___x_5116_, 2, v___x_5115_);
                lean_ctor_set_float(
                    v___x_5116_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5113_,
                );
                lean_ctor_set_float(
                    v___x_5116_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5113_,
                );
                lean_ctor_set_uint8(
                    v___x_5116_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_5114_,
                );
                v___x_5117_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2;
                v___x_5118_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_5118_, 0, v___x_5116_);
                lean_ctor_set(v___x_5118_, 1, v_a_5090_);
                lean_ctor_set(v___x_5118_, 2, v___x_5117_);
                lean_inc(v_ref_5088_);
                v___x_5119_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5119_, 0, v_ref_5088_);
                lean_ctor_set(v___x_5119_, 1, v___x_5118_);
                v___x_5120_ = l_Lean_PersistentArray_push___redArg(v_traces_5108_, v___x_5119_);
                if v_isShared_5111_ == 0 {
                    lean_ctor_set(v___x_5110_, 0, v___x_5120_);
                    v___x_5122_ = v___x_5110_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5120_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5131_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5107_,
                    );
                    v___x_5122_ = v_reuseFailAlloc_5131_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5106_ == 0 {
                    lean_ctor_set(v___x_5105_, 4, v___x_5122_);
                    v___x_5124_ = v___x_5105_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_env_5096_);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 1, v_nextMacroScope_5097_);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 2, v_ngen_5098_);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 3, v_auxDeclNGen_5099_);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 4, v___x_5122_);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 5, v_cache_5100_);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 6, v_messages_5101_);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 7, v_infoState_5102_);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 8, v_snapshotTasks_5103_);
                    v___x_5124_ = v_reuseFailAlloc_5130_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5125_ = lean_st_ref_set(v___y_5086_, v___x_5124_);
                v___x_5126_ = lean_box(0);
                if v_isShared_5093_ == 0 {
                    lean_ctor_set(v___x_5092_, 0, v___x_5126_);
                    v___x_5128_ = v___x_5092_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5126_);
                    v___x_5128_ = v_reuseFailAlloc_5129_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(
    mut v_cls_5135_: *mut LeanObject,
    mut v_msg_5136_: *mut LeanObject,
    mut v___y_5137_: *mut LeanObject,
    mut v___y_5138_: *mut LeanObject,
    mut v___y_5139_: *mut LeanObject,
    mut v___y_5140_: *mut LeanObject,
    mut v___y_5141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5142_: *mut LeanObject = core::ptr::null_mut();
    v_res_5142_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v_cls_5135_, v_msg_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
    lean_dec(v___y_5140_);
    lean_dec_ref(v___y_5139_);
    lean_dec(v___y_5138_);
    lean_dec_ref(v___y_5137_);
    return v_res_5142_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4()
-> *mut LeanObject {
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    v___x_5149_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_;
    v___x_5150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3;
    v___x_5151_ = l_Lean_Name_append(v___x_5150_, v___x_5149_);
    return v___x_5151_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6()
-> *mut LeanObject {
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    v___x_5153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5;
    v___x_5154_ = l_Lean_stringToMessageData(v___x_5153_);
    return v___x_5154_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(
    mut v_infos_5155_: *mut LeanObject,
    mut v_levels_5156_: *mut LeanObject,
    mut v_as_5157_: *mut LeanObject,
    mut v_sz_5158_: usize,
    mut v_i_5159_: usize,
    mut v_b_5160_: *mut LeanObject,
    mut v___y_5161_: *mut LeanObject,
    mut v___y_5162_: *mut LeanObject,
    mut v___y_5163_: *mut LeanObject,
    mut v___y_5164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5166_: u8 = 0;
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: u8 = 0;
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5181_: u8 = 0;
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: usize = 0;
    let mut v___x_5199_: usize = 0;
    let mut v_a_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5204_: u8 = 0;
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5208_: u8 = 0;
    let mut v_a_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5212_: u8 = 0;
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5216_: u8 = 0;
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: u8 = 0;
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5227_: u8 = 0;
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5166_ = lean_usize_dec_lt(v_i_5159_, v_sz_5158_);
                if v___x_5166_ == 0 {
                    lean_dec(v_levels_5156_);
                    lean_dec_ref(v_infos_5155_);
                    v___x_5167_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5167_, 0, v_b_5160_);
                    return v___x_5167_;
                } else {
                    v_a_5168_ = lean_array_uget_borrowed(v_as_5157_, v_i_5159_);
                    v_toConstantVal_5169_ = lean_ctor_get(v_a_5168_, 0);
                    v_numParams_5170_ = lean_ctor_get(v_a_5168_, 1);
                    v_name_5171_ = lean_ctor_get(v_toConstantVal_5169_, 0);
                    v_levelParams_5172_ = lean_ctor_get(v_toConstantVal_5169_, 1);
                    v_type_5173_ = lean_ctor_get(v_toConstantVal_5169_, 2);
                    v___x_5174_ = lean_unsigned_to_nat(0);
                    lean_inc(v_levels_5156_);
                    lean_inc(v_name_5171_);
                    lean_inc(v_numParams_5170_);
                    lean_inc_ref(v_infos_5155_);
                    v___f_5175_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed as *mut core::ffi::c_void, 12, 5);
                    lean_closure_set(v___f_5175_, 0, v_infos_5155_);
                    lean_closure_set(v___f_5175_, 1, v_numParams_5170_);
                    lean_closure_set(v___f_5175_, 2, v___x_5174_);
                    lean_closure_set(v___f_5175_, 3, v_name_5171_);
                    lean_closure_set(v___f_5175_, 4, v_levels_5156_);
                    v___x_5176_ = 0;
                    lean_inc_ref(v_type_5173_);
                    v___x_5177_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_5173_, v___f_5175_, v___x_5176_, v___x_5176_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
                    if lean_obj_tag(v___x_5177_) == 0 {
                        v_options_5178_ = lean_ctor_get(v___y_5163_, 2);
                        v_a_5179_ = lean_ctor_get(v___x_5177_, 0);
                        lean_inc(v_a_5179_);
                        lean_dec_ref_known(v___x_5177_, 1);
                        v_inheritedTraceOptions_5180_ = lean_ctor_get(v___y_5163_, 13);
                        v_hasTrace_5181_ = lean_ctor_get_uint8(
                            v_options_5178_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        v___x_5182_ = lean_box(0);
                        if v_hasTrace_5181_ == 0 {
                            v___y_5184_ = v___y_5161_;
                            v___y_5185_ = v___y_5162_;
                            v___y_5186_ = v___y_5163_;
                            v___y_5187_ = v___y_5164_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5217_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_;
                            v___x_5218_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
                            v___x_5219_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_5180_,
                                v_options_5178_,
                                v___x_5218_,
                            );
                            if v___x_5219_ == 0 {
                                v___y_5184_ = v___y_5161_;
                                v___y_5185_ = v___y_5162_;
                                v___y_5186_ = v___y_5163_;
                                v___y_5187_ = v___y_5164_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5220_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6);
                                lean_inc(v_a_5179_);
                                v___x_5221_ = l_Lean_MessageData_ofExpr(v_a_5179_);
                                v___x_5222_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5222_, 0, v___x_5220_);
                                lean_ctor_set(v___x_5222_, 1, v___x_5221_);
                                v___x_5223_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v___x_5217_, v___x_5222_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
                                if lean_obj_tag(v___x_5223_) == 0 {
                                    lean_dec_ref_known(v___x_5223_, 1);
                                    v___y_5184_ = v___y_5161_;
                                    v___y_5185_ = v___y_5162_;
                                    v___y_5186_ = v___y_5163_;
                                    v___y_5187_ = v___y_5164_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_a_5179_);
                                    lean_dec(v_levels_5156_);
                                    lean_dec_ref(v_infos_5155_);
                                    return v___x_5223_;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_levels_5156_);
                        lean_dec_ref(v_infos_5155_);
                        v_a_5224_ = lean_ctor_get(v___x_5177_, 0);
                        v_isSharedCheck_5231_ = (!lean_is_exclusive(v___x_5177_)) as u8;
                        if v_isSharedCheck_5231_ == 0 {
                            v___x_5226_ = v___x_5177_;
                            v_isShared_5227_ = v_isSharedCheck_5231_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5224_);
                            lean_dec(v___x_5177_);
                            v___x_5226_ = lean_box(0);
                            v_isShared_5227_ = v_isSharedCheck_5231_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v___y_5187_);
                lean_inc_ref(v___y_5186_);
                lean_inc(v___y_5185_);
                lean_inc_ref(v___y_5184_);
                lean_inc(v_a_5179_);
                v___x_5188_ = lean_infer_type(
                    v_a_5179_,
                    v___y_5184_,
                    v___y_5185_,
                    v___y_5186_,
                    v___y_5187_,
                );
                if lean_obj_tag(v___x_5188_) == 0 {
                    v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
                    lean_inc(v_a_5189_);
                    lean_dec_ref_known(v___x_5188_, 1);
                    lean_inc(v_name_5171_);
                    v___x_5190_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_5171_);
                    v___x_5191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1;
                    v___x_5192_ = l_Lean_Name_append(v___x_5190_, v___x_5191_);
                    v___x_5193_ = lean_box(0);
                    lean_inc(v_levelParams_5172_);
                    v___x_5194_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_5192_, v_levelParams_5172_, v_a_5189_, v_a_5179_, v___x_5193_, v___y_5187_);
                    if lean_obj_tag(v___x_5194_) == 0 {
                        v_a_5195_ = lean_ctor_get(v___x_5194_, 0);
                        lean_inc(v_a_5195_);
                        lean_dec_ref_known(v___x_5194_, 1);
                        v___x_5196_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5196_, 0, v_a_5195_);
                        v___x_5197_ =
                            l_Lean_addDecl(v___x_5196_, v___x_5176_, v___y_5186_, v___y_5187_);
                        if lean_obj_tag(v___x_5197_) == 0 {
                            lean_dec_ref_known(v___x_5197_, 1);
                            v___x_5198_ = 1usize;
                            v___x_5199_ = lean_usize_add(v_i_5159_, v___x_5198_);
                            v_i_5159_ = v___x_5199_;
                            v_b_5160_ = v___x_5182_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_levels_5156_);
                            lean_dec_ref(v_infos_5155_);
                            return v___x_5197_;
                        }
                    } else {
                        lean_dec(v_levels_5156_);
                        lean_dec_ref(v_infos_5155_);
                        v_a_5201_ = lean_ctor_get(v___x_5194_, 0);
                        v_isSharedCheck_5208_ = (!lean_is_exclusive(v___x_5194_)) as u8;
                        if v_isSharedCheck_5208_ == 0 {
                            v___x_5203_ = v___x_5194_;
                            v_isShared_5204_ = v_isSharedCheck_5208_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5201_);
                            lean_dec(v___x_5194_);
                            v___x_5203_ = lean_box(0);
                            v_isShared_5204_ = v_isSharedCheck_5208_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5179_);
                    lean_dec(v_levels_5156_);
                    lean_dec_ref(v_infos_5155_);
                    v_a_5209_ = lean_ctor_get(v___x_5188_, 0);
                    v_isSharedCheck_5216_ = (!lean_is_exclusive(v___x_5188_)) as u8;
                    if v_isSharedCheck_5216_ == 0 {
                        v___x_5211_ = v___x_5188_;
                        v_isShared_5212_ = v_isSharedCheck_5216_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5209_);
                        lean_dec(v___x_5188_);
                        v___x_5211_ = lean_box(0);
                        v_isShared_5212_ = v_isSharedCheck_5216_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5204_ == 0 {
                    v___x_5206_ = v___x_5203_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5207_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5207_, 0, v_a_5201_);
                    v___x_5206_ = v_reuseFailAlloc_5207_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5206_;
            }
            4 => {
                if v_isShared_5212_ == 0 {
                    v___x_5214_ = v___x_5211_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5215_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5209_);
                    v___x_5214_ = v_reuseFailAlloc_5215_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5214_;
            }
            6 => {
                if v_isShared_5227_ == 0 {
                    v___x_5229_ = v___x_5226_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_a_5224_);
                    v___x_5229_ = v_reuseFailAlloc_5230_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(
    mut v_infos_5232_: *mut LeanObject,
    mut v_levels_5233_: *mut LeanObject,
    mut v_as_5234_: *mut LeanObject,
    mut v_sz_5235_: *mut LeanObject,
    mut v_i_5236_: *mut LeanObject,
    mut v_b_5237_: *mut LeanObject,
    mut v___y_5238_: *mut LeanObject,
    mut v___y_5239_: *mut LeanObject,
    mut v___y_5240_: *mut LeanObject,
    mut v___y_5241_: *mut LeanObject,
    mut v___y_5242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5243_: usize = 0;
    let mut v_i_boxed_5244_: usize = 0;
    let mut v_res_5245_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5243_ = lean_unbox_usize(v_sz_5235_);
    lean_dec(v_sz_5235_);
    v_i_boxed_5244_ = lean_unbox_usize(v_i_5236_);
    lean_dec(v_i_5236_);
    v_res_5245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_5232_, v_levels_5233_, v_as_5234_, v_sz_boxed_5243_, v_i_boxed_5244_, v_b_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_);
    lean_dec(v___y_5241_);
    lean_dec_ref(v___y_5240_);
    lean_dec(v___y_5239_);
    lean_dec_ref(v___y_5238_);
    lean_dec_ref(v_as_5234_);
    return v_res_5245_;
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(
    mut v_infos_5246_: *mut LeanObject,
    mut v_a_5247_: *mut LeanObject,
    mut v_a_5248_: *mut LeanObject,
    mut v_a_5249_: *mut LeanObject,
    mut v_a_5250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levels_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5260_: usize = 0;
    let mut v___x_5261_: usize = 0;
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5265_: u8 = 0;
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5269_: u8 = 0;
    let mut v_unused_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5252_ = l_Lean_instInhabitedInductiveVal_default;
                v___x_5253_ = lean_unsigned_to_nat(0);
                v___x_5254_ = lean_array_get_borrowed(v___x_5252_, v_infos_5246_, v___x_5253_);
                v_toConstantVal_5255_ = lean_ctor_get(v___x_5254_, 0);
                v_levelParams_5256_ = lean_ctor_get(v_toConstantVal_5255_, 1);
                v___x_5257_ = lean_box(0);
                lean_inc(v_levelParams_5256_);
                v_levels_5258_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_5256_, v___x_5257_);
                v___x_5259_ = lean_box(0);
                v_sz_5260_ = lean_array_size(v_infos_5246_);
                v___x_5261_ = 0usize;
                lean_inc_ref(v_infos_5246_);
                v___x_5262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_5246_, v_levels_5258_, v_infos_5246_, v_sz_5260_, v___x_5261_, v___x_5259_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_);
                lean_dec_ref(v_infos_5246_);
                if lean_obj_tag(v___x_5262_) == 0 {
                    v_isSharedCheck_5269_ = (!lean_is_exclusive(v___x_5262_)) as u8;
                    if v_isSharedCheck_5269_ == 0 {
                        v_unused_5270_ = lean_ctor_get(v___x_5262_, 0);
                        lean_dec(v_unused_5270_);
                        v___x_5264_ = v___x_5262_;
                        v_isShared_5265_ = v_isSharedCheck_5269_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5262_);
                        v___x_5264_ = lean_box(0);
                        v_isShared_5265_ = v_isSharedCheck_5269_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_5262_;
                }
            }
            1 => {
                if v_isShared_5265_ == 0 {
                    lean_ctor_set(v___x_5264_, 0, v___x_5259_);
                    v___x_5267_ = v___x_5264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5268_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5268_, 0, v___x_5259_);
                    v___x_5267_ = v_reuseFailAlloc_5268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(
    mut v_infos_5271_: *mut LeanObject,
    mut v_a_5272_: *mut LeanObject,
    mut v_a_5273_: *mut LeanObject,
    mut v_a_5274_: *mut LeanObject,
    mut v_a_5275_: *mut LeanObject,
    mut v_a_5276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5277_: *mut LeanObject = core::ptr::null_mut();
    v_res_5277_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(
        v_infos_5271_,
        v_a_5272_,
        v_a_5273_,
        v_a_5274_,
        v_a_5275_,
    );
    lean_dec(v_a_5275_);
    lean_dec_ref(v_a_5274_);
    lean_dec(v_a_5273_);
    lean_dec_ref(v_a_5272_);
    return v_res_5277_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(
    mut v_00_u03b1_5278_: *mut LeanObject,
    mut v_msg_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    v___x_5285_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
    return v___x_5285_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(
    mut v_00_u03b1_5286_: *mut LeanObject,
    mut v_msg_5287_: *mut LeanObject,
    mut v___y_5288_: *mut LeanObject,
    mut v___y_5289_: *mut LeanObject,
    mut v___y_5290_: *mut LeanObject,
    mut v___y_5291_: *mut LeanObject,
    mut v___y_5292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5293_: *mut LeanObject = core::ptr::null_mut();
    v_res_5293_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(v_00_u03b1_5286_, v_msg_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_);
    lean_dec(v___y_5291_);
    lean_dec_ref(v___y_5290_);
    lean_dec(v___y_5289_);
    lean_dec_ref(v___y_5288_);
    return v_res_5293_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(
    mut v_inst_5294_: *mut LeanObject,
    mut v_R_5295_: *mut LeanObject,
    mut v_a_5296_: *mut LeanObject,
    mut v_b_5297_: *mut LeanObject,
    mut v_c_5298_: *mut LeanObject,
    mut v___y_5299_: *mut LeanObject,
    mut v___y_5300_: *mut LeanObject,
    mut v___y_5301_: *mut LeanObject,
    mut v___y_5302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    v___x_5304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_5296_, v_b_5297_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
    return v___x_5304_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(
    mut v_inst_5305_: *mut LeanObject,
    mut v_R_5306_: *mut LeanObject,
    mut v_a_5307_: *mut LeanObject,
    mut v_b_5308_: *mut LeanObject,
    mut v_c_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5315_: *mut LeanObject = core::ptr::null_mut();
    v_res_5315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(v_inst_5305_, v_R_5306_, v_a_5307_, v_b_5308_, v_c_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_);
    lean_dec(v___y_5313_);
    lean_dec_ref(v___y_5312_);
    lean_dec(v___y_5311_);
    lean_dec_ref(v___y_5310_);
    return v_res_5315_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(
    mut v_mvarId_5316_: *mut LeanObject,
    mut v_val_5317_: *mut LeanObject,
    mut v___y_5318_: *mut LeanObject,
    mut v___y_5319_: *mut LeanObject,
    mut v___y_5320_: *mut LeanObject,
    mut v___y_5321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    v___x_5323_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_5316_, v_val_5317_, v___y_5319_);
    return v___x_5323_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(
    mut v_mvarId_5324_: *mut LeanObject,
    mut v_val_5325_: *mut LeanObject,
    mut v___y_5326_: *mut LeanObject,
    mut v___y_5327_: *mut LeanObject,
    mut v___y_5328_: *mut LeanObject,
    mut v___y_5329_: *mut LeanObject,
    mut v___y_5330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5331_: *mut LeanObject = core::ptr::null_mut();
    v_res_5331_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(v_mvarId_5324_, v_val_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
    lean_dec(v___y_5329_);
    lean_dec_ref(v___y_5328_);
    lean_dec(v___y_5327_);
    lean_dec_ref(v___y_5326_);
    return v_res_5331_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(
    mut v_00_u03b2_5332_: *mut LeanObject,
    mut v_x_5333_: *mut LeanObject,
    mut v_x_5334_: *mut LeanObject,
    mut v_x_5335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    v___x_5336_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_x_5333_, v_x_5334_, v_x_5335_);
    return v___x_5336_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(
    mut v_00_u03b2_5337_: *mut LeanObject,
    mut v_x_5338_: *mut LeanObject,
    mut v_x_5339_: usize,
    mut v_x_5340_: usize,
    mut v_x_5341_: *mut LeanObject,
    mut v_x_5342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    v___x_5343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_5338_, v_x_5339_, v_x_5340_, v_x_5341_, v_x_5342_);
    return v___x_5343_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___boxed(
    mut v_00_u03b2_5344_: *mut LeanObject,
    mut v_x_5345_: *mut LeanObject,
    mut v_x_5346_: *mut LeanObject,
    mut v_x_5347_: *mut LeanObject,
    mut v_x_5348_: *mut LeanObject,
    mut v_x_5349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9715__boxed_5350_: usize = 0;
    let mut v_x_9716__boxed_5351_: usize = 0;
    let mut v_res_5352_: *mut LeanObject = core::ptr::null_mut();
    v_x_9715__boxed_5350_ = lean_unbox_usize(v_x_5346_);
    lean_dec(v_x_5346_);
    v_x_9716__boxed_5351_ = lean_unbox_usize(v_x_5347_);
    lean_dec(v_x_5347_);
    v_res_5352_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(v_00_u03b2_5344_, v_x_5345_, v_x_9715__boxed_5350_, v_x_9716__boxed_5351_, v_x_5348_, v_x_5349_);
    return v_res_5352_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12(
    mut v_00_u03b2_5353_: *mut LeanObject,
    mut v_n_5354_: *mut LeanObject,
    mut v_k_5355_: *mut LeanObject,
    mut v_v_5356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    v___x_5357_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v_n_5354_, v_k_5355_, v_v_5356_);
    return v___x_5357_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(
    mut v_00_u03b2_5358_: *mut LeanObject,
    mut v_depth_5359_: usize,
    mut v_keys_5360_: *mut LeanObject,
    mut v_vals_5361_: *mut LeanObject,
    mut v_heq_5362_: *mut LeanObject,
    mut v_i_5363_: *mut LeanObject,
    mut v_entries_5364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    v___x_5365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_5359_, v_keys_5360_, v_vals_5361_, v_i_5363_, v_entries_5364_);
    return v___x_5365_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___boxed(
    mut v_00_u03b2_5366_: *mut LeanObject,
    mut v_depth_5367_: *mut LeanObject,
    mut v_keys_5368_: *mut LeanObject,
    mut v_vals_5369_: *mut LeanObject,
    mut v_heq_5370_: *mut LeanObject,
    mut v_i_5371_: *mut LeanObject,
    mut v_entries_5372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5373_: usize = 0;
    let mut v_res_5374_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5373_ = lean_unbox_usize(v_depth_5367_);
    lean_dec(v_depth_5367_);
    v_res_5374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(v_00_u03b2_5366_, v_depth_boxed_5373_, v_keys_5368_, v_vals_5369_, v_heq_5370_, v_i_5371_, v_entries_5372_);
    lean_dec_ref(v_vals_5369_);
    lean_dec_ref(v_keys_5368_);
    return v_res_5374_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13(
    mut v_00_u03b2_5375_: *mut LeanObject,
    mut v_x_5376_: *mut LeanObject,
    mut v_x_5377_: *mut LeanObject,
    mut v_x_5378_: *mut LeanObject,
    mut v_x_5379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    v___x_5380_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_x_5376_, v_x_5377_, v_x_5378_, v_x_5379_);
    return v___x_5380_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(
    mut v_e_5381_: *mut LeanObject,
    mut v___y_5382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5384_: u8 = 0;
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5398_: u8 = 0;
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5404_: u8 = 0;
    let mut v_unused_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5384_ = l_Lean_Expr_hasMVar(v_e_5381_);
                if v___x_5384_ == 0 {
                    v___x_5385_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5385_, 0, v_e_5381_);
                    return v___x_5385_;
                } else {
                    v___x_5386_ = lean_st_ref_get(v___y_5382_);
                    v_mctx_5387_ = lean_ctor_get(v___x_5386_, 0);
                    lean_inc_ref(v_mctx_5387_);
                    lean_dec(v___x_5386_);
                    v___x_5388_ = l_Lean_instantiateMVarsCore(v_mctx_5387_, v_e_5381_);
                    v_fst_5389_ = lean_ctor_get(v___x_5388_, 0);
                    lean_inc(v_fst_5389_);
                    v_snd_5390_ = lean_ctor_get(v___x_5388_, 1);
                    lean_inc(v_snd_5390_);
                    lean_dec_ref(v___x_5388_);
                    v___x_5391_ = lean_st_ref_take(v___y_5382_);
                    v_cache_5392_ = lean_ctor_get(v___x_5391_, 1);
                    v_zetaDeltaFVarIds_5393_ = lean_ctor_get(v___x_5391_, 2);
                    v_postponed_5394_ = lean_ctor_get(v___x_5391_, 3);
                    v_diag_5395_ = lean_ctor_get(v___x_5391_, 4);
                    v_isSharedCheck_5404_ = (!lean_is_exclusive(v___x_5391_)) as u8;
                    if v_isSharedCheck_5404_ == 0 {
                        v_unused_5405_ = lean_ctor_get(v___x_5391_, 0);
                        lean_dec(v_unused_5405_);
                        v___x_5397_ = v___x_5391_;
                        v_isShared_5398_ = v_isSharedCheck_5404_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_5395_);
                        lean_inc(v_postponed_5394_);
                        lean_inc(v_zetaDeltaFVarIds_5393_);
                        lean_inc(v_cache_5392_);
                        lean_dec(v___x_5391_);
                        v___x_5397_ = lean_box(0);
                        v_isShared_5398_ = v_isSharedCheck_5404_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5398_ == 0 {
                    lean_ctor_set(v___x_5397_, 0, v_snd_5390_);
                    v___x_5400_ = v___x_5397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_snd_5390_);
                    lean_ctor_set(v_reuseFailAlloc_5403_, 1, v_cache_5392_);
                    lean_ctor_set(v_reuseFailAlloc_5403_, 2, v_zetaDeltaFVarIds_5393_);
                    lean_ctor_set(v_reuseFailAlloc_5403_, 3, v_postponed_5394_);
                    lean_ctor_set(v_reuseFailAlloc_5403_, 4, v_diag_5395_);
                    v___x_5400_ = v_reuseFailAlloc_5403_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5401_ = lean_st_ref_set(v___y_5382_, v___x_5400_);
                v___x_5402_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5402_, 0, v_fst_5389_);
                return v___x_5402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(
    mut v_e_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5409_: *mut LeanObject = core::ptr::null_mut();
    v_res_5409_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_5406_, v___y_5407_);
    lean_dec(v___y_5407_);
    return v_res_5409_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(
    mut v_e_5410_: *mut LeanObject,
    mut v___y_5411_: *mut LeanObject,
    mut v___y_5412_: *mut LeanObject,
    mut v___y_5413_: *mut LeanObject,
    mut v___y_5414_: *mut LeanObject,
    mut v___y_5415_: *mut LeanObject,
    mut v___y_5416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    v___x_5418_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_5410_, v___y_5414_);
    return v___x_5418_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(
    mut v_e_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
    mut v___y_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
    mut v___y_5423_: *mut LeanObject,
    mut v___y_5424_: *mut LeanObject,
    mut v___y_5425_: *mut LeanObject,
    mut v___y_5426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5427_: *mut LeanObject = core::ptr::null_mut();
    v_res_5427_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_e_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
    lean_dec(v___y_5425_);
    lean_dec_ref(v___y_5424_);
    lean_dec(v___y_5423_);
    lean_dec_ref(v___y_5422_);
    lean_dec(v___y_5421_);
    lean_dec_ref(v___y_5420_);
    return v_res_5427_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(
    mut v_k_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
    mut v_b_5431_: *mut LeanObject,
    mut v_c_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5438_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5436_);
    lean_inc_ref(v___y_5435_);
    lean_inc(v___y_5434_);
    lean_inc_ref(v___y_5433_);
    lean_inc(v___y_5430_);
    lean_inc_ref(v___y_5429_);
    v___x_5438_ = lean_apply_9(
        v_k_5428_,
        v_b_5431_,
        v_c_5432_,
        v___y_5429_,
        v___y_5430_,
        v___y_5433_,
        v___y_5434_,
        v___y_5435_,
        v___y_5436_,
        lean_box(0),
    );
    return v___x_5438_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed(
    mut v_k_5439_: *mut LeanObject,
    mut v___y_5440_: *mut LeanObject,
    mut v___y_5441_: *mut LeanObject,
    mut v_b_5442_: *mut LeanObject,
    mut v_c_5443_: *mut LeanObject,
    mut v___y_5444_: *mut LeanObject,
    mut v___y_5445_: *mut LeanObject,
    mut v___y_5446_: *mut LeanObject,
    mut v___y_5447_: *mut LeanObject,
    mut v___y_5448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5449_: *mut LeanObject = core::ptr::null_mut();
    v_res_5449_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(v_k_5439_, v___y_5440_, v___y_5441_, v_b_5442_, v_c_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
    lean_dec(v___y_5447_);
    lean_dec_ref(v___y_5446_);
    lean_dec(v___y_5445_);
    lean_dec_ref(v___y_5444_);
    lean_dec(v___y_5441_);
    lean_dec_ref(v___y_5440_);
    return v_res_5449_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(
    mut v_type_5450_: *mut LeanObject,
    mut v_k_5451_: *mut LeanObject,
    mut v_cleanupAnnotations_5452_: u8,
    mut v___y_5453_: *mut LeanObject,
    mut v___y_5454_: *mut LeanObject,
    mut v___y_5455_: *mut LeanObject,
    mut v___y_5456_: *mut LeanObject,
    mut v___y_5457_: *mut LeanObject,
    mut v___y_5458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: u8 = 0;
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5454_);
                lean_inc_ref(v___y_5453_);
                v___f_5460_ = lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_5460_, 0, v_k_5451_);
                lean_closure_set(v___f_5460_, 1, v___y_5453_);
                lean_closure_set(v___f_5460_, 2, v___y_5454_);
                v___x_5461_ = 0;
                v___x_5462_ = lean_box(0);
                v___x_5463_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        lean_box(0),
                        v___x_5461_,
                        v___x_5462_,
                        v_type_5450_,
                        v___f_5460_,
                        v_cleanupAnnotations_5452_,
                        v___x_5461_,
                        v___y_5455_,
                        v___y_5456_,
                        v___y_5457_,
                        v___y_5458_,
                    );
                if lean_obj_tag(v___x_5463_) == 0 {
                    return v___x_5463_;
                } else {
                    v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
                    v_isSharedCheck_5471_ = (!lean_is_exclusive(v___x_5463_)) as u8;
                    if v_isSharedCheck_5471_ == 0 {
                        v___x_5466_ = v___x_5463_;
                        v_isShared_5467_ = v_isSharedCheck_5471_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5464_);
                        lean_dec(v___x_5463_);
                        v___x_5466_ = lean_box(0);
                        v_isShared_5467_ = v_isSharedCheck_5471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5467_ == 0 {
                    v___x_5469_ = v___x_5466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
                    v___x_5469_ = v_reuseFailAlloc_5470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(
    mut v_type_5472_: *mut LeanObject,
    mut v_k_5473_: *mut LeanObject,
    mut v_cleanupAnnotations_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5482_: u8 = 0;
    let mut v_res_5483_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5482_ = (lean_unbox(v_cleanupAnnotations_5474_) as u8);
    v_res_5483_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_5472_, v_k_5473_, v_cleanupAnnotations_boxed_5482_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
    lean_dec(v___y_5480_);
    lean_dec_ref(v___y_5479_);
    lean_dec(v___y_5478_);
    lean_dec_ref(v___y_5477_);
    lean_dec(v___y_5476_);
    lean_dec_ref(v___y_5475_);
    return v_res_5483_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(
    mut v_00_u03b1_5484_: *mut LeanObject,
    mut v_type_5485_: *mut LeanObject,
    mut v_k_5486_: *mut LeanObject,
    mut v_cleanupAnnotations_5487_: u8,
    mut v___y_5488_: *mut LeanObject,
    mut v___y_5489_: *mut LeanObject,
    mut v___y_5490_: *mut LeanObject,
    mut v___y_5491_: *mut LeanObject,
    mut v___y_5492_: *mut LeanObject,
    mut v___y_5493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    v___x_5495_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_5485_, v_k_5486_, v_cleanupAnnotations_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
    return v___x_5495_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(
    mut v_00_u03b1_5496_: *mut LeanObject,
    mut v_type_5497_: *mut LeanObject,
    mut v_k_5498_: *mut LeanObject,
    mut v_cleanupAnnotations_5499_: *mut LeanObject,
    mut v___y_5500_: *mut LeanObject,
    mut v___y_5501_: *mut LeanObject,
    mut v___y_5502_: *mut LeanObject,
    mut v___y_5503_: *mut LeanObject,
    mut v___y_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5507_: u8 = 0;
    let mut v_res_5508_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5507_ = (lean_unbox(v_cleanupAnnotations_5499_) as u8);
    v_res_5508_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(v_00_u03b1_5496_, v_type_5497_, v_k_5498_, v_cleanupAnnotations_boxed_5507_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_);
    lean_dec(v___y_5505_);
    lean_dec_ref(v___y_5504_);
    lean_dec(v___y_5503_);
    lean_dec_ref(v___y_5502_);
    lean_dec(v___y_5501_);
    lean_dec_ref(v___y_5500_);
    return v_res_5508_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(
    mut v_name_5509_: *mut LeanObject,
    mut v_levelParams_5510_: *mut LeanObject,
    mut v_type_5511_: *mut LeanObject,
    mut v_value_5512_: *mut LeanObject,
    mut v_hints_5513_: *mut LeanObject,
    mut v___y_5514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5518_: u8 = 0;
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5525_: u8 = 0;
    let mut v___x_5526_: u8 = 0;
    let mut v___x_5527_: u8 = 0;
    let mut v_env_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: u8 = 0;
    let mut v___x_5530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5516_ = lean_st_ref_get(v___y_5514_);
                v_env_5528_ = lean_ctor_get(v___x_5516_, 0);
                lean_inc_ref_n(v_env_5528_, 2);
                lean_dec(v___x_5516_);
                v___x_5529_ = l_Lean_Environment_hasUnsafe(v_env_5528_, v_type_5511_);
                if v___x_5529_ == 0 {
                    v___x_5530_ = l_Lean_Environment_hasUnsafe(v_env_5528_, v_value_5512_);
                    v___y_5525_ = v___x_5530_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_env_5528_);
                    v___y_5525_ = v___x_5529_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc(v_name_5509_);
                v___x_5519_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_5519_, 0, v_name_5509_);
                lean_ctor_set(v___x_5519_, 1, v_levelParams_5510_);
                lean_ctor_set(v___x_5519_, 2, v_type_5511_);
                v___x_5520_ = lean_box(0);
                v___x_5521_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5521_, 0, v_name_5509_);
                lean_ctor_set(v___x_5521_, 1, v___x_5520_);
                v___x_5522_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_5522_, 0, v___x_5519_);
                lean_ctor_set(v___x_5522_, 1, v_value_5512_);
                lean_ctor_set(v___x_5522_, 2, v_hints_5513_);
                lean_ctor_set(v___x_5522_, 3, v___x_5521_);
                lean_ctor_set_uint8(
                    v___x_5522_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___y_5518_,
                );
                v___x_5523_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5523_, 0, v___x_5522_);
                return v___x_5523_;
            }
            2 => {
                if v___y_5525_ == 0 {
                    v___x_5526_ = 1;
                    v___y_5518_ = v___x_5526_;
                    state = 1;
                    continue;
                } else {
                    v___x_5527_ = 0;
                    v___y_5518_ = v___x_5527_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(
    mut v_name_5531_: *mut LeanObject,
    mut v_levelParams_5532_: *mut LeanObject,
    mut v_type_5533_: *mut LeanObject,
    mut v_value_5534_: *mut LeanObject,
    mut v_hints_5535_: *mut LeanObject,
    mut v___y_5536_: *mut LeanObject,
    mut v___y_5537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5538_: *mut LeanObject = core::ptr::null_mut();
    v_res_5538_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_5531_, v_levelParams_5532_, v_type_5533_, v_value_5534_, v_hints_5535_, v___y_5536_);
    lean_dec(v___y_5536_);
    return v_res_5538_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(
    mut v_name_5539_: *mut LeanObject,
    mut v_levelParams_5540_: *mut LeanObject,
    mut v_type_5541_: *mut LeanObject,
    mut v_value_5542_: *mut LeanObject,
    mut v_hints_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    v___x_5551_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_5539_, v_levelParams_5540_, v_type_5541_, v_value_5542_, v_hints_5543_, v___y_5549_);
    return v___x_5551_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(
    mut v_name_5552_: *mut LeanObject,
    mut v_levelParams_5553_: *mut LeanObject,
    mut v_type_5554_: *mut LeanObject,
    mut v_value_5555_: *mut LeanObject,
    mut v_hints_5556_: *mut LeanObject,
    mut v___y_5557_: *mut LeanObject,
    mut v___y_5558_: *mut LeanObject,
    mut v___y_5559_: *mut LeanObject,
    mut v___y_5560_: *mut LeanObject,
    mut v___y_5561_: *mut LeanObject,
    mut v___y_5562_: *mut LeanObject,
    mut v___y_5563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5564_: *mut LeanObject = core::ptr::null_mut();
    v_res_5564_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_5552_, v_levelParams_5553_, v_type_5554_, v_value_5555_, v_hints_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_);
    lean_dec(v___y_5562_);
    lean_dec_ref(v___y_5561_);
    lean_dec(v___y_5560_);
    lean_dec_ref(v___y_5559_);
    lean_dec(v___y_5558_);
    lean_dec_ref(v___y_5557_);
    return v_res_5564_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(
    mut v_type_5565_: *mut LeanObject,
    mut v_maxFVars_x3f_5566_: *mut LeanObject,
    mut v_k_5567_: *mut LeanObject,
    mut v_cleanupAnnotations_5568_: u8,
    mut v_whnfType_5569_: u8,
    mut v___y_5570_: *mut LeanObject,
    mut v___y_5571_: *mut LeanObject,
    mut v___y_5572_: *mut LeanObject,
    mut v___y_5573_: *mut LeanObject,
    mut v___y_5574_: *mut LeanObject,
    mut v___y_5575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5571_);
                lean_inc_ref(v___y_5570_);
                v___f_5577_ = lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_5577_, 0, v_k_5567_);
                lean_closure_set(v___f_5577_, 1, v___y_5570_);
                lean_closure_set(v___f_5577_, 2, v___y_5571_);
                v___x_5578_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_5565_,
                    v_maxFVars_x3f_5566_,
                    v___f_5577_,
                    v_cleanupAnnotations_5568_,
                    v_whnfType_5569_,
                    v___y_5572_,
                    v___y_5573_,
                    v___y_5574_,
                    v___y_5575_,
                );
                if lean_obj_tag(v___x_5578_) == 0 {
                    return v___x_5578_;
                } else {
                    v_a_5579_ = lean_ctor_get(v___x_5578_, 0);
                    v_isSharedCheck_5586_ = (!lean_is_exclusive(v___x_5578_)) as u8;
                    if v_isSharedCheck_5586_ == 0 {
                        v___x_5581_ = v___x_5578_;
                        v_isShared_5582_ = v_isSharedCheck_5586_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5579_);
                        lean_dec(v___x_5578_);
                        v___x_5581_ = lean_box(0);
                        v_isShared_5582_ = v_isSharedCheck_5586_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5582_ == 0 {
                    v___x_5584_ = v___x_5581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5579_);
                    v___x_5584_ = v_reuseFailAlloc_5585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(
    mut v_type_5587_: *mut LeanObject,
    mut v_maxFVars_x3f_5588_: *mut LeanObject,
    mut v_k_5589_: *mut LeanObject,
    mut v_cleanupAnnotations_5590_: *mut LeanObject,
    mut v_whnfType_5591_: *mut LeanObject,
    mut v___y_5592_: *mut LeanObject,
    mut v___y_5593_: *mut LeanObject,
    mut v___y_5594_: *mut LeanObject,
    mut v___y_5595_: *mut LeanObject,
    mut v___y_5596_: *mut LeanObject,
    mut v___y_5597_: *mut LeanObject,
    mut v___y_5598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5599_: u8 = 0;
    let mut v_whnfType_boxed_5600_: u8 = 0;
    let mut v_res_5601_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5599_ = (lean_unbox(v_cleanupAnnotations_5590_) as u8);
    v_whnfType_boxed_5600_ = (lean_unbox(v_whnfType_5591_) as u8);
    v_res_5601_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_5587_, v_maxFVars_x3f_5588_, v_k_5589_, v_cleanupAnnotations_boxed_5599_, v_whnfType_boxed_5600_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_);
    lean_dec(v___y_5597_);
    lean_dec_ref(v___y_5596_);
    lean_dec(v___y_5595_);
    lean_dec_ref(v___y_5594_);
    lean_dec(v___y_5593_);
    lean_dec_ref(v___y_5592_);
    return v_res_5601_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(
    mut v_00_u03b1_5602_: *mut LeanObject,
    mut v_type_5603_: *mut LeanObject,
    mut v_maxFVars_x3f_5604_: *mut LeanObject,
    mut v_k_5605_: *mut LeanObject,
    mut v_cleanupAnnotations_5606_: u8,
    mut v_whnfType_5607_: u8,
    mut v___y_5608_: *mut LeanObject,
    mut v___y_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
    mut v___y_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    v___x_5615_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_5603_, v_maxFVars_x3f_5604_, v_k_5605_, v_cleanupAnnotations_5606_, v_whnfType_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
    return v___x_5615_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(
    mut v_00_u03b1_5616_: *mut LeanObject,
    mut v_type_5617_: *mut LeanObject,
    mut v_maxFVars_x3f_5618_: *mut LeanObject,
    mut v_k_5619_: *mut LeanObject,
    mut v_cleanupAnnotations_5620_: *mut LeanObject,
    mut v_whnfType_5621_: *mut LeanObject,
    mut v___y_5622_: *mut LeanObject,
    mut v___y_5623_: *mut LeanObject,
    mut v___y_5624_: *mut LeanObject,
    mut v___y_5625_: *mut LeanObject,
    mut v___y_5626_: *mut LeanObject,
    mut v___y_5627_: *mut LeanObject,
    mut v___y_5628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5629_: u8 = 0;
    let mut v_whnfType_boxed_5630_: u8 = 0;
    let mut v_res_5631_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5629_ = (lean_unbox(v_cleanupAnnotations_5620_) as u8);
    v_whnfType_boxed_5630_ = (lean_unbox(v_whnfType_5621_) as u8);
    v_res_5631_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_00_u03b1_5616_, v_type_5617_, v_maxFVars_x3f_5618_, v_k_5619_, v_cleanupAnnotations_boxed_5629_, v_whnfType_boxed_5630_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_);
    lean_dec(v___y_5627_);
    lean_dec_ref(v___y_5626_);
    lean_dec(v___y_5625_);
    lean_dec_ref(v___y_5624_);
    lean_dec(v___y_5623_);
    lean_dec_ref(v___y_5622_);
    return v_res_5631_;
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(
    mut v_cls_5632_: *mut LeanObject,
    mut v___y_5633_: *mut LeanObject,
    mut v___y_5634_: *mut LeanObject,
    mut v___y_5635_: *mut LeanObject,
    mut v___y_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5641_: u8 = 0;
    v_options_5640_ = lean_ctor_get(v___y_5637_, 2);
    v_hasTrace_5641_ = lean_ctor_get_uint8(
        v_options_5640_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_5641_ == 0 {
        let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_cls_5632_);
        v___x_5642_ = lean_box((v_hasTrace_5641_) as usize);
        v___x_5643_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5643_, 0, v___x_5642_);
        return v___x_5643_;
    } else {
        let mut v_inheritedTraceOptions_5644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5647_: u8 = 0;
        let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_5644_ = lean_ctor_get(v___y_5637_, 13);
        v___x_5645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3;
        v___x_5646_ = l_Lean_Name_append(v___x_5645_, v_cls_5632_);
        v___x_5647_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_5644_,
            v_options_5640_,
            v___x_5646_,
        );
        lean_dec(v___x_5646_);
        v___x_5648_ = lean_box((v___x_5647_) as usize);
        v___x_5649_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5649_, 0, v___x_5648_);
        return v___x_5649_;
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(
    mut v_cls_5650_: *mut LeanObject,
    mut v___y_5651_: *mut LeanObject,
    mut v___y_5652_: *mut LeanObject,
    mut v___y_5653_: *mut LeanObject,
    mut v___y_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
    mut v___y_5657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5658_: *mut LeanObject = core::ptr::null_mut();
    v_res_5658_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_);
    lean_dec(v___y_5656_);
    lean_dec_ref(v___y_5655_);
    lean_dec(v___y_5654_);
    lean_dec_ref(v___y_5653_);
    lean_dec(v___y_5652_);
    lean_dec_ref(v___y_5651_);
    return v_res_5658_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(
    mut v_mvarId_5659_: *mut LeanObject,
    mut v_val_5660_: *mut LeanObject,
    mut v___y_5661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v_depth_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5684_: u8 = 0;
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5695_: u8 = 0;
    let mut v_isSharedCheck_5696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5663_ = lean_st_ref_take(v___y_5661_);
                v_mctx_5664_ = lean_ctor_get(v___x_5663_, 0);
                v_cache_5665_ = lean_ctor_get(v___x_5663_, 1);
                v_zetaDeltaFVarIds_5666_ = lean_ctor_get(v___x_5663_, 2);
                v_postponed_5667_ = lean_ctor_get(v___x_5663_, 3);
                v_diag_5668_ = lean_ctor_get(v___x_5663_, 4);
                v_isSharedCheck_5696_ = (!lean_is_exclusive(v___x_5663_)) as u8;
                if v_isSharedCheck_5696_ == 0 {
                    v___x_5670_ = v___x_5663_;
                    v_isShared_5671_ = v_isSharedCheck_5696_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_5668_);
                    lean_inc(v_postponed_5667_);
                    lean_inc(v_zetaDeltaFVarIds_5666_);
                    lean_inc(v_cache_5665_);
                    lean_inc(v_mctx_5664_);
                    lean_dec(v___x_5663_);
                    v___x_5670_ = lean_box(0);
                    v_isShared_5671_ = v_isSharedCheck_5696_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5672_ = lean_ctor_get(v_mctx_5664_, 0);
                v_levelAssignDepth_5673_ = lean_ctor_get(v_mctx_5664_, 1);
                v_lmvarCounter_5674_ = lean_ctor_get(v_mctx_5664_, 2);
                v_mvarCounter_5675_ = lean_ctor_get(v_mctx_5664_, 3);
                v_lDecls_5676_ = lean_ctor_get(v_mctx_5664_, 4);
                v_decls_5677_ = lean_ctor_get(v_mctx_5664_, 5);
                v_userNames_5678_ = lean_ctor_get(v_mctx_5664_, 6);
                v_lAssignment_5679_ = lean_ctor_get(v_mctx_5664_, 7);
                v_eAssignment_5680_ = lean_ctor_get(v_mctx_5664_, 8);
                v_dAssignment_5681_ = lean_ctor_get(v_mctx_5664_, 9);
                v_isSharedCheck_5695_ = (!lean_is_exclusive(v_mctx_5664_)) as u8;
                if v_isSharedCheck_5695_ == 0 {
                    v___x_5683_ = v_mctx_5664_;
                    v_isShared_5684_ = v_isSharedCheck_5695_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_5681_);
                    lean_inc(v_eAssignment_5680_);
                    lean_inc(v_lAssignment_5679_);
                    lean_inc(v_userNames_5678_);
                    lean_inc(v_decls_5677_);
                    lean_inc(v_lDecls_5676_);
                    lean_inc(v_mvarCounter_5675_);
                    lean_inc(v_lmvarCounter_5674_);
                    lean_inc(v_levelAssignDepth_5673_);
                    lean_inc(v_depth_5672_);
                    lean_dec(v_mctx_5664_);
                    v___x_5683_ = lean_box(0);
                    v_isShared_5684_ = v_isSharedCheck_5695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5685_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_5680_, v_mvarId_5659_, v_val_5660_);
                if v_isShared_5684_ == 0 {
                    lean_ctor_set(v___x_5683_, 8, v___x_5685_);
                    v___x_5687_ = v___x_5683_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_depth_5672_);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 1, v_levelAssignDepth_5673_);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 2, v_lmvarCounter_5674_);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 3, v_mvarCounter_5675_);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 4, v_lDecls_5676_);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 5, v_decls_5677_);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 6, v_userNames_5678_);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 7, v_lAssignment_5679_);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 8, v___x_5685_);
                    lean_ctor_set(v_reuseFailAlloc_5694_, 9, v_dAssignment_5681_);
                    v___x_5687_ = v_reuseFailAlloc_5694_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5671_ == 0 {
                    lean_ctor_set(v___x_5670_, 0, v___x_5687_);
                    v___x_5689_ = v___x_5670_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5693_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5693_, 0, v___x_5687_);
                    lean_ctor_set(v_reuseFailAlloc_5693_, 1, v_cache_5665_);
                    lean_ctor_set(v_reuseFailAlloc_5693_, 2, v_zetaDeltaFVarIds_5666_);
                    lean_ctor_set(v_reuseFailAlloc_5693_, 3, v_postponed_5667_);
                    lean_ctor_set(v_reuseFailAlloc_5693_, 4, v_diag_5668_);
                    v___x_5689_ = v_reuseFailAlloc_5693_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5690_ = lean_st_ref_set(v___y_5661_, v___x_5689_);
                v___x_5691_ = lean_box(0);
                v___x_5692_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5692_, 0, v___x_5691_);
                return v___x_5692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(
    mut v_mvarId_5697_: *mut LeanObject,
    mut v_val_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5701_: *mut LeanObject = core::ptr::null_mut();
    v_res_5701_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_5697_, v_val_5698_, v___y_5699_);
    lean_dec(v___y_5699_);
    return v_res_5701_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(
    mut v_cls_5702_: *mut LeanObject,
    mut v_msg_5703_: *mut LeanObject,
    mut v___y_5704_: *mut LeanObject,
    mut v___y_5705_: *mut LeanObject,
    mut v___y_5706_: *mut LeanObject,
    mut v___y_5707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5714_: u8 = 0;
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5727_: u8 = 0;
    let mut v_tid_5728_: u64 = 0;
    let mut v_traces_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: f64 = 0.0;
    let mut v___x_5735_: u8 = 0;
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5753_: u8 = 0;
    let mut v_isSharedCheck_5754_: u8 = 0;
    let mut v_isSharedCheck_5755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5709_ = lean_ctor_get(v___y_5706_, 5);
                v___x_5710_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_);
                v_a_5711_ = lean_ctor_get(v___x_5710_, 0);
                v_isSharedCheck_5755_ = (!lean_is_exclusive(v___x_5710_)) as u8;
                if v_isSharedCheck_5755_ == 0 {
                    v___x_5713_ = v___x_5710_;
                    v_isShared_5714_ = v_isSharedCheck_5755_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5711_);
                    lean_dec(v___x_5710_);
                    v___x_5713_ = lean_box(0);
                    v_isShared_5714_ = v_isSharedCheck_5755_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5715_ = lean_st_ref_take(v___y_5707_);
                v_traceState_5716_ = lean_ctor_get(v___x_5715_, 4);
                v_env_5717_ = lean_ctor_get(v___x_5715_, 0);
                v_nextMacroScope_5718_ = lean_ctor_get(v___x_5715_, 1);
                v_ngen_5719_ = lean_ctor_get(v___x_5715_, 2);
                v_auxDeclNGen_5720_ = lean_ctor_get(v___x_5715_, 3);
                v_cache_5721_ = lean_ctor_get(v___x_5715_, 5);
                v_messages_5722_ = lean_ctor_get(v___x_5715_, 6);
                v_infoState_5723_ = lean_ctor_get(v___x_5715_, 7);
                v_snapshotTasks_5724_ = lean_ctor_get(v___x_5715_, 8);
                v_isSharedCheck_5754_ = (!lean_is_exclusive(v___x_5715_)) as u8;
                if v_isSharedCheck_5754_ == 0 {
                    v___x_5726_ = v___x_5715_;
                    v_isShared_5727_ = v_isSharedCheck_5754_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5724_);
                    lean_inc(v_infoState_5723_);
                    lean_inc(v_messages_5722_);
                    lean_inc(v_cache_5721_);
                    lean_inc(v_traceState_5716_);
                    lean_inc(v_auxDeclNGen_5720_);
                    lean_inc(v_ngen_5719_);
                    lean_inc(v_nextMacroScope_5718_);
                    lean_inc(v_env_5717_);
                    lean_dec(v___x_5715_);
                    v___x_5726_ = lean_box(0);
                    v_isShared_5727_ = v_isSharedCheck_5754_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5728_ = lean_ctor_get_uint64(
                    v_traceState_5716_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5729_ = lean_ctor_get(v_traceState_5716_, 0);
                v_isSharedCheck_5753_ = (!lean_is_exclusive(v_traceState_5716_)) as u8;
                if v_isSharedCheck_5753_ == 0 {
                    v___x_5731_ = v_traceState_5716_;
                    v_isShared_5732_ = v_isSharedCheck_5753_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_5729_);
                    lean_dec(v_traceState_5716_);
                    v___x_5731_ = lean_box(0);
                    v_isShared_5732_ = v_isSharedCheck_5753_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5733_ = lean_box(0);
                v___x_5734_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
                v___x_5735_ = 0;
                v___x_5736_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1;
                v___x_5737_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_5737_, 0, v_cls_5702_);
                lean_ctor_set(v___x_5737_, 1, v___x_5733_);
                lean_ctor_set(v___x_5737_, 2, v___x_5736_);
                lean_ctor_set_float(
                    v___x_5737_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5734_,
                );
                lean_ctor_set_float(
                    v___x_5737_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5734_,
                );
                lean_ctor_set_uint8(
                    v___x_5737_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_5735_,
                );
                v___x_5738_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2;
                v___x_5739_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_5739_, 0, v___x_5737_);
                lean_ctor_set(v___x_5739_, 1, v_a_5711_);
                lean_ctor_set(v___x_5739_, 2, v___x_5738_);
                lean_inc(v_ref_5709_);
                v___x_5740_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5740_, 0, v_ref_5709_);
                lean_ctor_set(v___x_5740_, 1, v___x_5739_);
                v___x_5741_ = l_Lean_PersistentArray_push___redArg(v_traces_5729_, v___x_5740_);
                if v_isShared_5732_ == 0 {
                    lean_ctor_set(v___x_5731_, 0, v___x_5741_);
                    v___x_5743_ = v___x_5731_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 0, v___x_5741_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5752_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5728_,
                    );
                    v___x_5743_ = v_reuseFailAlloc_5752_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5727_ == 0 {
                    lean_ctor_set(v___x_5726_, 4, v___x_5743_);
                    v___x_5745_ = v___x_5726_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_env_5717_);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 1, v_nextMacroScope_5718_);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 2, v_ngen_5719_);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 3, v_auxDeclNGen_5720_);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 4, v___x_5743_);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 5, v_cache_5721_);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 6, v_messages_5722_);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 7, v_infoState_5723_);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 8, v_snapshotTasks_5724_);
                    v___x_5745_ = v_reuseFailAlloc_5751_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5746_ = lean_st_ref_set(v___y_5707_, v___x_5745_);
                v___x_5747_ = lean_box(0);
                if v_isShared_5714_ == 0 {
                    lean_ctor_set(v___x_5713_, 0, v___x_5747_);
                    v___x_5749_ = v___x_5713_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5750_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5750_, 0, v___x_5747_);
                    v___x_5749_ = v_reuseFailAlloc_5750_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(
    mut v_cls_5756_: *mut LeanObject,
    mut v_msg_5757_: *mut LeanObject,
    mut v___y_5758_: *mut LeanObject,
    mut v___y_5759_: *mut LeanObject,
    mut v___y_5760_: *mut LeanObject,
    mut v___y_5761_: *mut LeanObject,
    mut v___y_5762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5763_: *mut LeanObject = core::ptr::null_mut();
    v_res_5763_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_5756_, v_msg_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_);
    lean_dec(v___y_5761_);
    lean_dec_ref(v___y_5760_);
    lean_dec(v___y_5759_);
    lean_dec_ref(v___y_5758_);
    return v_res_5763_;
}
pub unsafe fn _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0()
-> *mut LeanObject {
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5765_: *mut LeanObject = core::ptr::null_mut();
    v___x_5764_ = lean_box(0);
    v_dummy_5765_ = l_Lean_Expr_sort___override(v___x_5764_);
    return v_dummy_5765_;
}
pub unsafe fn _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2()
-> *mut LeanObject {
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    v___x_5767_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1;
    v___x_5768_ = l_Lean_stringToMessageData(v___x_5767_);
    return v___x_5768_;
}
pub unsafe fn _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4()
-> *mut LeanObject {
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    v___x_5770_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3;
    v___x_5771_ = l_Lean_stringToMessageData(v___x_5770_);
    return v___x_5771_;
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(
    mut v_numParams_5772_: *mut LeanObject,
    mut v___x_5773_: *mut LeanObject,
    mut v_name_5774_: *mut LeanObject,
    mut v___x_5775_: *mut LeanObject,
    mut v___x_5776_: *mut LeanObject,
    mut v_name_5777_: *mut LeanObject,
    mut v___x_5778_: *mut LeanObject,
    mut v_cls_5779_: *mut LeanObject,
    mut v_fields_5780_: *mut LeanObject,
    mut v_bodyExpr_5781_: *mut LeanObject,
    mut v___y_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
    mut v___y_5784_: *mut LeanObject,
    mut v___y_5785_: *mut LeanObject,
    mut v___y_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5791_: u8 = 0;
    let mut v_nargs_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: u8 = 0;
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: u8 = 0;
    let mut v___x_5826_: u8 = 0;
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eNew_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqProof_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: u8 = 0;
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5843_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: u8 = 0;
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5875_: u8 = 0;
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5789_ = lean_ctor_get(v___y_5786_, 2);
                v_inheritedTraceOptions_5790_ = lean_ctor_get(v___y_5786_, 13);
                v_hasTrace_5791_ = lean_ctor_get_uint8(
                    v_options_5789_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_nargs_5792_ = l_Lean_Expr_getAppNumArgs(v_bodyExpr_5781_);
                v_dummy_5793_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once), _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
                lean_inc(v_nargs_5792_);
                v___x_5794_ = lean_mk_array(v_nargs_5792_, v_dummy_5793_);
                v___x_5795_ = lean_unsigned_to_nat(1);
                v___x_5796_ = lean_nat_sub(v_nargs_5792_, v___x_5795_);
                lean_dec(v_nargs_5792_);
                v___x_5797_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_bodyExpr_5781_,
                    v___x_5794_,
                    v___x_5796_,
                );
                v___x_5798_ = lean_array_get_size(v___x_5797_);
                v___x_5799_ = lean_nat_add(v_numParams_5772_, v___x_5773_);
                v___x_5800_ = l_Array_toSubarray___redArg(v___x_5797_, v___x_5799_, v___x_5798_);
                v___x_5801_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_5774_);
                lean_inc(v___x_5775_);
                lean_inc(v___x_5801_);
                v___x_5802_ = l_Lean_mkConst(v___x_5801_, v___x_5775_);
                v___x_5803_ = l_Lean_mkAppN(v___x_5802_, v___x_5776_);
                v___x_5804_ = l_Subarray_copy___redArg(v___x_5800_);
                v___x_5805_ = l_Lean_mkAppN(v___x_5803_, v___x_5804_);
                lean_dec_ref(v___x_5804_);
                if v_hasTrace_5791_ == 0 {
                    lean_dec(v_cls_5779_);
                    v___y_5807_ = v___y_5782_;
                    v___y_5808_ = v___y_5783_;
                    v___y_5809_ = v___y_5784_;
                    v___y_5810_ = v___y_5785_;
                    v___y_5811_ = v___y_5786_;
                    v___y_5812_ = v___y_5787_;
                    state = 1;
                    continue;
                } else {
                    v___x_5861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3;
                    lean_inc(v_cls_5779_);
                    v___x_5862_ = l_Lean_Name_append(v___x_5861_, v_cls_5779_);
                    v___x_5863_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5790_,
                        v_options_5789_,
                        v___x_5862_,
                    );
                    lean_dec(v___x_5862_);
                    if v___x_5863_ == 0 {
                        lean_dec(v_cls_5779_);
                        v___y_5807_ = v___y_5782_;
                        v___y_5808_ = v___y_5783_;
                        v___y_5809_ = v___y_5784_;
                        v___y_5810_ = v___y_5785_;
                        v___y_5811_ = v___y_5786_;
                        v___y_5812_ = v___y_5787_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5864_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once), _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2);
                        lean_inc(v_name_5777_);
                        v___x_5865_ = l_Lean_MessageData_ofName(v_name_5777_);
                        v___x_5866_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5866_, 0, v___x_5864_);
                        lean_ctor_set(v___x_5866_, 1, v___x_5865_);
                        v___x_5867_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once), _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4);
                        v___x_5868_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5868_, 0, v___x_5866_);
                        lean_ctor_set(v___x_5868_, 1, v___x_5867_);
                        lean_inc_ref(v___x_5805_);
                        v___x_5869_ = l_Lean_MessageData_ofExpr(v___x_5805_);
                        v___x_5870_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5870_, 0, v___x_5868_);
                        lean_ctor_set(v___x_5870_, 1, v___x_5869_);
                        v___x_5871_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_5779_, v___x_5870_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_);
                        if lean_obj_tag(v___x_5871_) == 0 {
                            lean_dec_ref_known(v___x_5871_, 1);
                            v___y_5807_ = v___y_5782_;
                            v___y_5808_ = v___y_5783_;
                            v___y_5809_ = v___y_5784_;
                            v___y_5810_ = v___y_5785_;
                            v___y_5811_ = v___y_5786_;
                            v___y_5812_ = v___y_5787_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v___x_5805_);
                            lean_dec(v___x_5801_);
                            lean_dec(v_name_5777_);
                            lean_dec(v___x_5775_);
                            v_a_5872_ = lean_ctor_get(v___x_5871_, 0);
                            v_isSharedCheck_5879_ = (!lean_is_exclusive(v___x_5871_)) as u8;
                            if v_isSharedCheck_5879_ == 0 {
                                v___x_5874_ = v___x_5871_;
                                v_isShared_5875_ = v_isSharedCheck_5879_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_5872_);
                                lean_dec(v___x_5871_);
                                v___x_5874_ = lean_box(0);
                                v_isShared_5875_ = v_isSharedCheck_5879_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5813_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5813_, 0, v___x_5805_);
                v___x_5814_ = 0;
                v___x_5815_ = lean_box(0);
                v___x_5816_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_5813_,
                    v___x_5814_,
                    v___x_5815_,
                    v___y_5809_,
                    v___y_5810_,
                    v___y_5811_,
                    v___y_5812_,
                );
                if lean_obj_tag(v___x_5816_) == 0 {
                    v_a_5817_ = lean_ctor_get(v___x_5816_, 0);
                    lean_inc(v_a_5817_);
                    lean_dec_ref_known(v___x_5816_, 1);
                    v___x_5818_ = l_Lean_Expr_mvarId_x21(v_a_5817_);
                    lean_inc(v___x_5818_);
                    v___x_5819_ = l_Lean_MVarId_getType(
                        v___x_5818_,
                        v___y_5809_,
                        v___y_5810_,
                        v___y_5811_,
                        v___y_5812_,
                    );
                    if lean_obj_tag(v___x_5819_) == 0 {
                        v_a_5820_ = lean_ctor_get(v___x_5819_, 0);
                        lean_inc(v_a_5820_);
                        lean_dec_ref_known(v___x_5819_, 1);
                        v___x_5821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1;
                        v___x_5822_ = l_Lean_Name_append(v___x_5801_, v___x_5821_);
                        lean_inc(v___x_5775_);
                        v___x_5823_ = l_Lean_mkConst(v___x_5822_, v___x_5775_);
                        v___x_5824_ = l_Lean_mkAppN(v___x_5823_, v___x_5776_);
                        v___x_5825_ = 0;
                        v___x_5826_ = 1;
                        v___x_5827_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0;
                        lean_inc(v___x_5818_);
                        v___x_5828_ = l_Lean_MVarId_rewrite(
                            v___x_5818_,
                            v_a_5820_,
                            v___x_5824_,
                            v___x_5825_,
                            v___x_5827_,
                            v___y_5809_,
                            v___y_5810_,
                            v___y_5811_,
                            v___y_5812_,
                        );
                        if lean_obj_tag(v___x_5828_) == 0 {
                            v_a_5829_ = lean_ctor_get(v___x_5828_, 0);
                            lean_inc(v_a_5829_);
                            lean_dec_ref_known(v___x_5828_, 1);
                            v_eNew_5830_ = lean_ctor_get(v_a_5829_, 0);
                            lean_inc_ref(v_eNew_5830_);
                            v_eqProof_5831_ = lean_ctor_get(v_a_5829_, 1);
                            lean_inc_ref(v_eqProof_5831_);
                            lean_dec(v_a_5829_);
                            v___x_5832_ = l_Lean_MVarId_replaceTargetEq(
                                v___x_5818_,
                                v_eNew_5830_,
                                v_eqProof_5831_,
                                v___y_5809_,
                                v___y_5810_,
                                v___y_5811_,
                                v___y_5812_,
                            );
                            if lean_obj_tag(v___x_5832_) == 0 {
                                v_a_5833_ = lean_ctor_get(v___x_5832_, 0);
                                lean_inc(v_a_5833_);
                                lean_dec_ref_known(v___x_5832_, 1);
                                v___x_5834_ = l_Lean_mkConst(v_name_5777_, v___x_5775_);
                                v___x_5835_ = l_Lean_mkAppN(v___x_5834_, v___x_5776_);
                                v___x_5836_ = l_Lean_mkAppN(v___x_5835_, v___x_5778_);
                                v___x_5837_ = l_Lean_mkAppN(v___x_5836_, v_fields_5780_);
                                v___x_5838_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_a_5833_, v___x_5837_, v___y_5810_);
                                lean_dec_ref(v___x_5838_);
                                v___x_5839_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_a_5817_, v___y_5810_);
                                v_a_5840_ = lean_ctor_get(v___x_5839_, 0);
                                lean_inc(v_a_5840_);
                                lean_dec_ref(v___x_5839_);
                                v___x_5841_ = 1;
                                v___x_5842_ = l_Lean_Meta_mkLambdaFVars(
                                    v_fields_5780_,
                                    v_a_5840_,
                                    v___x_5825_,
                                    v___x_5826_,
                                    v___x_5825_,
                                    v___x_5826_,
                                    v___x_5841_,
                                    v___y_5809_,
                                    v___y_5810_,
                                    v___y_5811_,
                                    v___y_5812_,
                                );
                                if lean_obj_tag(v___x_5842_) == 0 {
                                    v_a_5843_ = lean_ctor_get(v___x_5842_, 0);
                                    lean_inc(v_a_5843_);
                                    lean_dec_ref_known(v___x_5842_, 1);
                                    v___x_5844_ = l_Lean_Meta_mkLambdaFVars(
                                        v___x_5776_,
                                        v_a_5843_,
                                        v___x_5825_,
                                        v___x_5826_,
                                        v___x_5825_,
                                        v___x_5826_,
                                        v___x_5841_,
                                        v___y_5809_,
                                        v___y_5810_,
                                        v___y_5811_,
                                        v___y_5812_,
                                    );
                                    return v___x_5844_;
                                } else {
                                    return v___x_5842_;
                                }
                            } else {
                                lean_dec(v_a_5817_);
                                lean_dec(v_name_5777_);
                                lean_dec(v___x_5775_);
                                v_a_5845_ = lean_ctor_get(v___x_5832_, 0);
                                v_isSharedCheck_5852_ = (!lean_is_exclusive(v___x_5832_)) as u8;
                                if v_isSharedCheck_5852_ == 0 {
                                    v___x_5847_ = v___x_5832_;
                                    v_isShared_5848_ = v_isSharedCheck_5852_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_5845_);
                                    lean_dec(v___x_5832_);
                                    v___x_5847_ = lean_box(0);
                                    v_isShared_5848_ = v_isSharedCheck_5852_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_5818_);
                            lean_dec(v_a_5817_);
                            lean_dec(v_name_5777_);
                            lean_dec(v___x_5775_);
                            v_a_5853_ = lean_ctor_get(v___x_5828_, 0);
                            v_isSharedCheck_5860_ = (!lean_is_exclusive(v___x_5828_)) as u8;
                            if v_isSharedCheck_5860_ == 0 {
                                v___x_5855_ = v___x_5828_;
                                v_isShared_5856_ = v_isSharedCheck_5860_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5853_);
                                lean_dec(v___x_5828_);
                                v___x_5855_ = lean_box(0);
                                v_isShared_5856_ = v_isSharedCheck_5860_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_5818_);
                        lean_dec(v_a_5817_);
                        lean_dec(v___x_5801_);
                        lean_dec(v_name_5777_);
                        lean_dec(v___x_5775_);
                        return v___x_5819_;
                    }
                } else {
                    lean_dec(v___x_5801_);
                    lean_dec(v_name_5777_);
                    lean_dec(v___x_5775_);
                    return v___x_5816_;
                }
            }
            2 => {
                if v_isShared_5848_ == 0 {
                    v___x_5850_ = v___x_5847_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_a_5845_);
                    v___x_5850_ = v_reuseFailAlloc_5851_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5850_;
            }
            4 => {
                if v_isShared_5856_ == 0 {
                    v___x_5858_ = v___x_5855_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
                    v___x_5858_ = v_reuseFailAlloc_5859_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5858_;
            }
            6 => {
                if v_isShared_5875_ == 0 {
                    v___x_5877_ = v___x_5874_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5878_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5878_, 0, v_a_5872_);
                    v___x_5877_ = v_reuseFailAlloc_5878_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_5880_: *mut LeanObject = *_args.add(0);
    let mut v___x_5881_: *mut LeanObject = *_args.add(1);
    let mut v_name_5882_: *mut LeanObject = *_args.add(2);
    let mut v___x_5883_: *mut LeanObject = *_args.add(3);
    let mut v___x_5884_: *mut LeanObject = *_args.add(4);
    let mut v_name_5885_: *mut LeanObject = *_args.add(5);
    let mut v___x_5886_: *mut LeanObject = *_args.add(6);
    let mut v_cls_5887_: *mut LeanObject = *_args.add(7);
    let mut v_fields_5888_: *mut LeanObject = *_args.add(8);
    let mut v_bodyExpr_5889_: *mut LeanObject = *_args.add(9);
    let mut v___y_5890_: *mut LeanObject = *_args.add(10);
    let mut v___y_5891_: *mut LeanObject = *_args.add(11);
    let mut v___y_5892_: *mut LeanObject = *_args.add(12);
    let mut v___y_5893_: *mut LeanObject = *_args.add(13);
    let mut v___y_5894_: *mut LeanObject = *_args.add(14);
    let mut v___y_5895_: *mut LeanObject = *_args.add(15);
    let mut v___y_5896_: *mut LeanObject = *_args.add(16);
    let mut v_res_5897_: *mut LeanObject = core::ptr::null_mut();
    v_res_5897_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v_numParams_5880_, v___x_5881_, v_name_5882_, v___x_5883_, v___x_5884_, v_name_5885_, v___x_5886_, v_cls_5887_, v_fields_5888_, v_bodyExpr_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
    lean_dec(v___y_5895_);
    lean_dec_ref(v___y_5894_);
    lean_dec(v___y_5893_);
    lean_dec_ref(v___y_5892_);
    lean_dec(v___y_5891_);
    lean_dec_ref(v___y_5890_);
    lean_dec_ref(v_fields_5888_);
    lean_dec_ref(v___x_5886_);
    lean_dec_ref(v___x_5884_);
    lean_dec(v___x_5881_);
    lean_dec(v_numParams_5880_);
    return v_res_5897_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(
    mut v___x_5898_: *mut LeanObject,
    mut v_sz_5899_: usize,
    mut v_i_5900_: usize,
    mut v_bs_5901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5902_: u8 = 0;
    let mut v_v_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: usize = 0;
    let mut v___x_5908_: usize = 0;
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5902_ = lean_usize_dec_lt(v_i_5900_, v_sz_5899_);
                if v___x_5902_ == 0 {
                    return v_bs_5901_;
                } else {
                    v_v_5903_ = lean_array_uget(v_bs_5901_, v_i_5900_);
                    v___x_5904_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5905_ = lean_array_uset(v_bs_5901_, v_i_5900_, v___x_5904_);
                    v___x_5906_ = l_Lean_mkAppN(v_v_5903_, v___x_5898_);
                    v___x_5907_ = 1usize;
                    v___x_5908_ = lean_usize_add(v_i_5900_, v___x_5907_);
                    v___x_5909_ = lean_array_uset(v_bs_x27_5905_, v_i_5900_, v___x_5906_);
                    v_i_5900_ = v___x_5908_;
                    v_bs_5901_ = v___x_5909_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(
    mut v___x_5911_: *mut LeanObject,
    mut v_sz_5912_: *mut LeanObject,
    mut v_i_5913_: *mut LeanObject,
    mut v_bs_5914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5915_: usize = 0;
    let mut v_i_boxed_5916_: usize = 0;
    let mut v_res_5917_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5915_ = lean_unbox_usize(v_sz_5912_);
    lean_dec(v_sz_5912_);
    v_i_boxed_5916_ = lean_unbox_usize(v_i_5913_);
    lean_dec(v_i_5913_);
    v_res_5917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_5911_, v_sz_boxed_5915_, v_i_boxed_5916_, v_bs_5914_);
    lean_dec_ref(v___x_5911_);
    return v_res_5917_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(
    mut v___x_5918_: *mut LeanObject,
    mut v_sz_5919_: usize,
    mut v_i_5920_: usize,
    mut v_bs_5921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5922_: u8 = 0;
    let mut v_v_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: usize = 0;
    let mut v___x_5928_: usize = 0;
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5922_ = lean_usize_dec_lt(v_i_5920_, v_sz_5919_);
                if v___x_5922_ == 0 {
                    lean_dec(v___x_5918_);
                    return v_bs_5921_;
                } else {
                    v_v_5923_ = lean_array_uget(v_bs_5921_, v_i_5920_);
                    v___x_5924_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5925_ = lean_array_uset(v_bs_5921_, v_i_5920_, v___x_5924_);
                    lean_inc(v___x_5918_);
                    v___x_5926_ = l_Lean_mkConst(v_v_5923_, v___x_5918_);
                    v___x_5927_ = 1usize;
                    v___x_5928_ = lean_usize_add(v_i_5920_, v___x_5927_);
                    v___x_5929_ = lean_array_uset(v_bs_x27_5925_, v_i_5920_, v___x_5926_);
                    v_i_5920_ = v___x_5928_;
                    v_bs_5921_ = v___x_5929_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(
    mut v___x_5931_: *mut LeanObject,
    mut v_sz_5932_: *mut LeanObject,
    mut v_i_5933_: *mut LeanObject,
    mut v_bs_5934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5935_: usize = 0;
    let mut v_i_boxed_5936_: usize = 0;
    let mut v_res_5937_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5935_ = lean_unbox_usize(v_sz_5932_);
    lean_dec(v_sz_5932_);
    v_i_boxed_5936_ = lean_unbox_usize(v_i_5933_);
    lean_dec(v_i_5933_);
    v_res_5937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_5931_, v_sz_boxed_5935_, v_i_boxed_5936_, v_bs_5934_);
    return v_res_5937_;
}
pub unsafe fn _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1()
-> *mut LeanObject {
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    v___x_5939_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0;
    v___x_5940_ = l_Lean_stringToMessageData(v___x_5939_);
    return v___x_5940_;
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(
    mut v___x_5941_: *mut LeanObject,
    mut v_numParams_5942_: *mut LeanObject,
    mut v___x_5943_: *mut LeanObject,
    mut v___x_5944_: *mut LeanObject,
    mut v___x_5945_: usize,
    mut v___x_5946_: *mut LeanObject,
    mut v_name_5947_: *mut LeanObject,
    mut v_name_5948_: *mut LeanObject,
    mut v_cls_5949_: *mut LeanObject,
    mut v___f_5950_: *mut LeanObject,
    mut v_levelParams_5951_: *mut LeanObject,
    mut v_ctorSyntax_5952_: *mut LeanObject,
    mut v_args_5953_: *mut LeanObject,
    mut v_body_5954_: *mut LeanObject,
    mut v___y_5955_: *mut LeanObject,
    mut v___y_5956_: *mut LeanObject,
    mut v___y_5957_: *mut LeanObject,
    mut v___y_5958_: *mut LeanObject,
    mut v___y_5959_: *mut LeanObject,
    mut v___y_5960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5965_: usize = 0;
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5967_: usize = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: u8 = 0;
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5990_: u8 = 0;
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: u8 = 0;
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5999_: u8 = 0;
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: u8 = 0;
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6010_: u8 = 0;
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6014_: u8 = 0;
    let mut v_a_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6018_: u8 = 0;
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6022_: u8 = 0;
    let mut v_a_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6026_: u8 = 0;
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_n(v_numParams_5942_, 2);
                v___x_5962_ =
                    l_Array_extract___redArg(v_args_5953_, v___x_5941_, v_numParams_5942_);
                v___x_5963_ = lean_array_get_size(v_args_5953_);
                v___x_5964_ =
                    l_Array_toSubarray___redArg(v_args_5953_, v_numParams_5942_, v___x_5963_);
                v_sz_5965_ = lean_array_size(v___x_5943_);
                lean_inc(v___x_5944_);
                v___x_5966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_5944_, v_sz_5965_, v___x_5945_, v___x_5943_);
                v_sz_5967_ = lean_array_size(v___x_5966_);
                v___x_5968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_5962_, v_sz_5967_, v___x_5945_, v___x_5966_);
                lean_inc(v_cls_5949_);
                lean_inc_ref(v___x_5968_);
                lean_inc(v_name_5948_);
                v___f_5969_ = lean_alloc_closure(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed as *mut core::ffi::c_void, 17, 8);
                lean_closure_set(v___f_5969_, 0, v_numParams_5942_);
                lean_closure_set(v___f_5969_, 1, v___x_5946_);
                lean_closure_set(v___f_5969_, 2, v_name_5947_);
                lean_closure_set(v___f_5969_, 3, v___x_5944_);
                lean_closure_set(v___f_5969_, 4, v___x_5962_);
                lean_closure_set(v___f_5969_, 5, v_name_5948_);
                lean_closure_set(v___f_5969_, 6, v___x_5968_);
                lean_closure_set(v___f_5969_, 7, v_cls_5949_);
                v___x_5970_ = l_Subarray_copy___redArg(v___x_5964_);
                v___x_5971_ = l_Lean_Expr_replaceFVars(v_body_5954_, v___x_5970_, v___x_5968_);
                lean_dec_ref(v___x_5968_);
                lean_dec_ref(v___x_5970_);
                v___x_5972_ = 0;
                v___x_5973_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v___x_5971_, v___f_5969_, v___x_5972_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_, v___y_5959_, v___y_5960_);
                if lean_obj_tag(v___x_5973_) == 0 {
                    v_a_5974_ = lean_ctor_get(v___x_5973_, 0);
                    lean_inc_n(v_a_5974_, 2);
                    lean_dec_ref_known(v___x_5973_, 1);
                    lean_inc(v___y_5960_);
                    lean_inc_ref(v___y_5959_);
                    lean_inc(v___y_5958_);
                    lean_inc_ref(v___y_5957_);
                    v___x_5975_ = lean_infer_type(
                        v_a_5974_,
                        v___y_5957_,
                        v___y_5958_,
                        v___y_5959_,
                        v___y_5960_,
                    );
                    if lean_obj_tag(v___x_5975_) == 0 {
                        v_a_5976_ = lean_ctor_get(v___x_5975_, 0);
                        lean_inc(v_a_5976_);
                        lean_dec_ref_known(v___x_5975_, 1);
                        lean_inc(v___y_5960_);
                        lean_inc_ref(v___y_5959_);
                        lean_inc(v___y_5958_);
                        lean_inc_ref(v___y_5957_);
                        lean_inc(v___y_5956_);
                        lean_inc_ref(v___y_5955_);
                        v___x_6000_ = lean_apply_7(
                            v___f_5950_,
                            v___y_5955_,
                            v___y_5956_,
                            v___y_5957_,
                            v___y_5958_,
                            v___y_5959_,
                            v___y_5960_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_6000_) == 0 {
                            v_a_6001_ = lean_ctor_get(v___x_6000_, 0);
                            lean_inc(v_a_6001_);
                            lean_dec_ref_known(v___x_6000_, 1);
                            v___x_6002_ = (lean_unbox(v_a_6001_) as u8);
                            lean_dec(v_a_6001_);
                            if v___x_6002_ == 0 {
                                lean_dec(v_cls_5949_);
                                v___y_5978_ = v___y_5955_;
                                v___y_5979_ = v___y_5956_;
                                v___y_5980_ = v___y_5957_;
                                v___y_5981_ = v___y_5958_;
                                v___y_5982_ = v___y_5959_;
                                v___y_5983_ = v___y_5960_;
                                state = 1;
                                continue;
                            } else {
                                v___x_6003_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once), _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1);
                                lean_inc(v_a_5976_);
                                v___x_6004_ = l_Lean_MessageData_ofExpr(v_a_5976_);
                                v___x_6005_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6005_, 0, v___x_6003_);
                                lean_ctor_set(v___x_6005_, 1, v___x_6004_);
                                v___x_6006_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_5949_, v___x_6005_, v___y_5957_, v___y_5958_, v___y_5959_, v___y_5960_);
                                if lean_obj_tag(v___x_6006_) == 0 {
                                    lean_dec_ref_known(v___x_6006_, 1);
                                    v___y_5978_ = v___y_5955_;
                                    v___y_5979_ = v___y_5956_;
                                    v___y_5980_ = v___y_5957_;
                                    v___y_5981_ = v___y_5958_;
                                    v___y_5982_ = v___y_5959_;
                                    v___y_5983_ = v___y_5960_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_a_5976_);
                                    lean_dec(v_a_5974_);
                                    lean_dec(v_ctorSyntax_5952_);
                                    lean_dec(v_levelParams_5951_);
                                    lean_dec(v_name_5948_);
                                    return v___x_6006_;
                                }
                            }
                        } else {
                            lean_dec(v_a_5976_);
                            lean_dec(v_a_5974_);
                            lean_dec(v_ctorSyntax_5952_);
                            lean_dec(v_levelParams_5951_);
                            lean_dec(v_cls_5949_);
                            lean_dec(v_name_5948_);
                            v_a_6007_ = lean_ctor_get(v___x_6000_, 0);
                            v_isSharedCheck_6014_ = (!lean_is_exclusive(v___x_6000_)) as u8;
                            if v_isSharedCheck_6014_ == 0 {
                                v___x_6009_ = v___x_6000_;
                                v_isShared_6010_ = v_isSharedCheck_6014_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_6007_);
                                lean_dec(v___x_6000_);
                                v___x_6009_ = lean_box(0);
                                v_isShared_6010_ = v_isSharedCheck_6014_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5974_);
                        lean_dec(v_ctorSyntax_5952_);
                        lean_dec(v_levelParams_5951_);
                        lean_dec_ref(v___f_5950_);
                        lean_dec(v_cls_5949_);
                        lean_dec(v_name_5948_);
                        v_a_6015_ = lean_ctor_get(v___x_5975_, 0);
                        v_isSharedCheck_6022_ = (!lean_is_exclusive(v___x_5975_)) as u8;
                        if v_isSharedCheck_6022_ == 0 {
                            v___x_6017_ = v___x_5975_;
                            v_isShared_6018_ = v_isSharedCheck_6022_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6015_);
                            lean_dec(v___x_5975_);
                            v___x_6017_ = lean_box(0);
                            v_isShared_6018_ = v_isSharedCheck_6022_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_ctorSyntax_5952_);
                    lean_dec(v_levelParams_5951_);
                    lean_dec_ref(v___f_5950_);
                    lean_dec(v_cls_5949_);
                    lean_dec(v_name_5948_);
                    v_a_6023_ = lean_ctor_get(v___x_5973_, 0);
                    v_isSharedCheck_6030_ = (!lean_is_exclusive(v___x_5973_)) as u8;
                    if v_isSharedCheck_6030_ == 0 {
                        v___x_6025_ = v___x_5973_;
                        v_isShared_6026_ = v_isSharedCheck_6030_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6023_);
                        lean_dec(v___x_5973_);
                        v___x_6025_ = lean_box(0);
                        v_isShared_6026_ = v_isSharedCheck_6030_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5984_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_5948_);
                v___x_5985_ = lean_box(0);
                lean_inc(v_a_5974_);
                v___x_5986_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v___x_5984_, v_levelParams_5951_, v_a_5976_, v_a_5974_, v___x_5985_, v___y_5983_);
                v_a_5987_ = lean_ctor_get(v___x_5986_, 0);
                v_isSharedCheck_5999_ = (!lean_is_exclusive(v___x_5986_)) as u8;
                if v_isSharedCheck_5999_ == 0 {
                    v___x_5989_ = v___x_5986_;
                    v_isShared_5990_ = v_isSharedCheck_5999_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_5987_);
                    lean_dec(v___x_5986_);
                    v___x_5989_ = lean_box(0);
                    v_isShared_5990_ = v_isSharedCheck_5999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5990_ == 0 {
                    lean_ctor_set_tag(v___x_5989_, 1);
                    v___x_5992_ = v___x_5989_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5998_, 0, v_a_5987_);
                    v___x_5992_ = v_reuseFailAlloc_5998_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5993_ = l_Lean_addDecl(v___x_5992_, v___x_5972_, v___y_5982_, v___y_5983_);
                if lean_obj_tag(v___x_5993_) == 0 {
                    lean_dec_ref_known(v___x_5993_, 1);
                    v___x_5994_ = lean_box(0);
                    v___x_5995_ = lean_box(0);
                    v___x_5996_ = 1;
                    v___x_5997_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_ctorSyntax_5952_,
                        v_a_5974_,
                        v___x_5994_,
                        v___x_5994_,
                        v___x_5995_,
                        v___x_5996_,
                        v___x_5972_,
                        v___y_5978_,
                        v___y_5979_,
                        v___y_5980_,
                        v___y_5981_,
                        v___y_5982_,
                        v___y_5983_,
                    );
                    return v___x_5997_;
                } else {
                    lean_dec(v_a_5974_);
                    lean_dec(v_ctorSyntax_5952_);
                    return v___x_5993_;
                }
            }
            4 => {
                if v_isShared_6010_ == 0 {
                    v___x_6012_ = v___x_6009_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_a_6007_);
                    v___x_6012_ = v_reuseFailAlloc_6013_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6012_;
            }
            6 => {
                if v_isShared_6018_ == 0 {
                    v___x_6020_ = v___x_6017_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6021_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6021_, 0, v_a_6015_);
                    v___x_6020_ = v_reuseFailAlloc_6021_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6020_;
            }
            8 => {
                if v_isShared_6026_ == 0 {
                    v___x_6028_ = v___x_6025_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6029_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6029_, 0, v_a_6023_);
                    v___x_6028_ = v_reuseFailAlloc_6029_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6031_: *mut LeanObject = *_args.add(0);
    let mut v_numParams_6032_: *mut LeanObject = *_args.add(1);
    let mut v___x_6033_: *mut LeanObject = *_args.add(2);
    let mut v___x_6034_: *mut LeanObject = *_args.add(3);
    let mut v___x_6035_: *mut LeanObject = *_args.add(4);
    let mut v___x_6036_: *mut LeanObject = *_args.add(5);
    let mut v_name_6037_: *mut LeanObject = *_args.add(6);
    let mut v_name_6038_: *mut LeanObject = *_args.add(7);
    let mut v_cls_6039_: *mut LeanObject = *_args.add(8);
    let mut v___f_6040_: *mut LeanObject = *_args.add(9);
    let mut v_levelParams_6041_: *mut LeanObject = *_args.add(10);
    let mut v_ctorSyntax_6042_: *mut LeanObject = *_args.add(11);
    let mut v_args_6043_: *mut LeanObject = *_args.add(12);
    let mut v_body_6044_: *mut LeanObject = *_args.add(13);
    let mut v___y_6045_: *mut LeanObject = *_args.add(14);
    let mut v___y_6046_: *mut LeanObject = *_args.add(15);
    let mut v___y_6047_: *mut LeanObject = *_args.add(16);
    let mut v___y_6048_: *mut LeanObject = *_args.add(17);
    let mut v___y_6049_: *mut LeanObject = *_args.add(18);
    let mut v___y_6050_: *mut LeanObject = *_args.add(19);
    let mut v___y_6051_: *mut LeanObject = *_args.add(20);
    let mut v___x_9125__boxed_6052_: usize = 0;
    let mut v_res_6053_: *mut LeanObject = core::ptr::null_mut();
    v___x_9125__boxed_6052_ = lean_unbox_usize(v___x_6035_);
    lean_dec(v___x_6035_);
    v_res_6053_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(v___x_6031_, v_numParams_6032_, v___x_6033_, v___x_6034_, v___x_9125__boxed_6052_, v___x_6036_, v_name_6037_, v_name_6038_, v_cls_6039_, v___f_6040_, v_levelParams_6041_, v_ctorSyntax_6042_, v_args_6043_, v_body_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_);
    lean_dec(v___y_6050_);
    lean_dec_ref(v___y_6049_);
    lean_dec(v___y_6048_);
    lean_dec_ref(v___y_6047_);
    lean_dec(v___y_6046_);
    lean_dec_ref(v___y_6045_);
    lean_dec_ref(v_body_6044_);
    return v_res_6053_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(
    mut v_sz_6054_: usize,
    mut v_i_6055_: usize,
    mut v_bs_6056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6057_: u8 = 0;
    let mut v_v_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: usize = 0;
    let mut v___x_6065_: usize = 0;
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6057_ = lean_usize_dec_lt(v_i_6055_, v_sz_6054_);
                if v___x_6057_ == 0 {
                    return v_bs_6056_;
                } else {
                    v_v_6058_ = lean_array_uget_borrowed(v_bs_6056_, v_i_6055_);
                    v_toConstantVal_6059_ = lean_ctor_get(v_v_6058_, 0);
                    v_name_6060_ = lean_ctor_get(v_toConstantVal_6059_, 0);
                    lean_inc(v_name_6060_);
                    v___x_6061_ = lean_unsigned_to_nat(0);
                    v_bs_x27_6062_ = lean_array_uset(v_bs_6056_, v_i_6055_, v___x_6061_);
                    v___x_6063_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_6060_);
                    v___x_6064_ = 1usize;
                    v___x_6065_ = lean_usize_add(v_i_6055_, v___x_6064_);
                    v___x_6066_ = lean_array_uset(v_bs_x27_6062_, v_i_6055_, v___x_6063_);
                    v_i_6055_ = v___x_6065_;
                    v_bs_6056_ = v___x_6066_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(
    mut v_sz_6068_: *mut LeanObject,
    mut v_i_6069_: *mut LeanObject,
    mut v_bs_6070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6071_: usize = 0;
    let mut v_i_boxed_6072_: usize = 0;
    let mut v_res_6073_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6071_ = lean_unbox_usize(v_sz_6068_);
    lean_dec(v_sz_6068_);
    v_i_boxed_6072_ = lean_unbox_usize(v_i_6069_);
    lean_dec(v_i_6069_);
    v_res_6073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_boxed_6071_, v_i_boxed_6072_, v_bs_6070_);
    return v_res_6073_;
}
pub unsafe fn _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2()
-> *mut LeanObject {
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    v___x_6077_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1;
    v___x_6078_ = l_Lean_stringToMessageData(v___x_6077_);
    return v___x_6078_;
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(
    mut v_infos_6081_: *mut LeanObject,
    mut v_ctorSyntax_6082_: *mut LeanObject,
    mut v_numParams_6083_: *mut LeanObject,
    mut v_name_6084_: *mut LeanObject,
    mut v_ctor_6085_: *mut LeanObject,
    mut v_a_6086_: *mut LeanObject,
    mut v_a_6087_: *mut LeanObject,
    mut v_a_6088_: *mut LeanObject,
    mut v_a_6089_: *mut LeanObject,
    mut v_a_6090_: *mut LeanObject,
    mut v_a_6091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cls_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6099_: u8 = 0;
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6117_: usize = 0;
    let mut v___x_6118_: usize = 0;
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: u8 = 0;
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: u8 = 0;
    let mut v_toConstantVal_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cls_6093_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_;
                v___f_6094_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0;
                v___x_6095_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_6093_, v_a_6086_, v_a_6087_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_);
                v_a_6096_ = lean_ctor_get(v___x_6095_, 0);
                v_isSharedCheck_6138_ = (!lean_is_exclusive(v___x_6095_)) as u8;
                if v_isSharedCheck_6138_ == 0 {
                    v___x_6098_ = v___x_6095_;
                    v_isShared_6099_ = v_isSharedCheck_6138_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6096_);
                    lean_dec(v___x_6095_);
                    v___x_6098_ = lean_box(0);
                    v_isShared_6099_ = v_isSharedCheck_6138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6100_ = l_Lean_instInhabitedInductiveVal_default;
                v___x_6130_ = (lean_unbox(v_a_6096_) as u8);
                lean_dec(v_a_6096_);
                if v___x_6130_ == 0 {
                    v___y_6102_ = v_a_6086_;
                    v___y_6103_ = v_a_6087_;
                    v___y_6104_ = v_a_6088_;
                    v___y_6105_ = v_a_6089_;
                    v___y_6106_ = v_a_6090_;
                    v___y_6107_ = v_a_6091_;
                    state = 2;
                    continue;
                } else {
                    v_toConstantVal_6131_ = lean_ctor_get(v_ctor_6085_, 0);
                    v_name_6132_ = lean_ctor_get(v_toConstantVal_6131_, 0);
                    v___x_6133_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once), _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2);
                    lean_inc(v_name_6132_);
                    v___x_6134_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_6132_);
                    v___x_6135_ = l_Lean_MessageData_ofName(v___x_6134_);
                    v___x_6136_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6136_, 0, v___x_6133_);
                    lean_ctor_set(v___x_6136_, 1, v___x_6135_);
                    v___x_6137_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_6093_, v___x_6136_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_);
                    if lean_obj_tag(v___x_6137_) == 0 {
                        lean_dec_ref_known(v___x_6137_, 1);
                        v___y_6102_ = v_a_6086_;
                        v___y_6103_ = v_a_6087_;
                        v___y_6104_ = v_a_6088_;
                        v___y_6105_ = v_a_6089_;
                        v___y_6106_ = v_a_6090_;
                        v___y_6107_ = v_a_6091_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_6098_);
                        lean_dec_ref(v_ctor_6085_);
                        lean_dec(v_name_6084_);
                        lean_dec(v_numParams_6083_);
                        lean_dec(v_ctorSyntax_6082_);
                        lean_dec_ref(v_infos_6081_);
                        return v___x_6137_;
                    }
                }
            }
            2 => {
                v___x_6108_ = lean_unsigned_to_nat(0);
                v___x_6109_ = lean_array_get_borrowed(v___x_6100_, v_infos_6081_, v___x_6108_);
                v_toConstantVal_6110_ = lean_ctor_get(v___x_6109_, 0);
                v_toConstantVal_6111_ = lean_ctor_get(v_ctor_6085_, 0);
                lean_inc_ref(v_toConstantVal_6111_);
                lean_dec_ref(v_ctor_6085_);
                v_levelParams_6112_ = lean_ctor_get(v_toConstantVal_6110_, 1);
                lean_inc(v_levelParams_6112_);
                v_name_6113_ = lean_ctor_get(v_toConstantVal_6111_, 0);
                lean_inc(v_name_6113_);
                v_levelParams_6114_ = lean_ctor_get(v_toConstantVal_6111_, 1);
                lean_inc(v_levelParams_6114_);
                v_type_6115_ = lean_ctor_get(v_toConstantVal_6111_, 2);
                lean_inc_ref(v_type_6115_);
                lean_dec_ref(v_toConstantVal_6111_);
                v___x_6116_ = lean_array_get_size(v_infos_6081_);
                v_sz_6117_ = lean_array_size(v_infos_6081_);
                v___x_6118_ = 0usize;
                v___x_6119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_6117_, v___x_6118_, v_infos_6081_);
                v___x_6120_ = lean_box(0);
                v___x_6121_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_6112_, v___x_6120_);
                v___x_6122_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1;
                lean_inc(v_numParams_6083_);
                v___f_6123_ = lean_alloc_closure(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed as *mut core::ffi::c_void, 21, 12);
                lean_closure_set(v___f_6123_, 0, v___x_6108_);
                lean_closure_set(v___f_6123_, 1, v_numParams_6083_);
                lean_closure_set(v___f_6123_, 2, v___x_6119_);
                lean_closure_set(v___f_6123_, 3, v___x_6121_);
                lean_closure_set(v___f_6123_, 4, v___x_6122_);
                lean_closure_set(v___f_6123_, 5, v___x_6116_);
                lean_closure_set(v___f_6123_, 6, v_name_6084_);
                lean_closure_set(v___f_6123_, 7, v_name_6113_);
                lean_closure_set(v___f_6123_, 8, v_cls_6093_);
                lean_closure_set(v___f_6123_, 9, v___f_6094_);
                lean_closure_set(v___f_6123_, 10, v_levelParams_6114_);
                lean_closure_set(v___f_6123_, 11, v_ctorSyntax_6082_);
                v___x_6124_ = lean_nat_add(v_numParams_6083_, v___x_6116_);
                lean_dec(v_numParams_6083_);
                if v_isShared_6099_ == 0 {
                    lean_ctor_set_tag(v___x_6098_, 1);
                    lean_ctor_set(v___x_6098_, 0, v___x_6124_);
                    v___x_6126_ = v___x_6098_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6129_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6129_, 0, v___x_6124_);
                    v___x_6126_ = v_reuseFailAlloc_6129_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6127_ = 0;
                v___x_6128_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_6115_, v___x_6126_, v___f_6123_, v___x_6127_, v___x_6127_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
                return v___x_6128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(
    mut v_infos_6139_: *mut LeanObject,
    mut v_ctorSyntax_6140_: *mut LeanObject,
    mut v_numParams_6141_: *mut LeanObject,
    mut v_name_6142_: *mut LeanObject,
    mut v_ctor_6143_: *mut LeanObject,
    mut v_a_6144_: *mut LeanObject,
    mut v_a_6145_: *mut LeanObject,
    mut v_a_6146_: *mut LeanObject,
    mut v_a_6147_: *mut LeanObject,
    mut v_a_6148_: *mut LeanObject,
    mut v_a_6149_: *mut LeanObject,
    mut v_a_6150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6151_: *mut LeanObject = core::ptr::null_mut();
    v_res_6151_ =
        l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(
            v_infos_6139_,
            v_ctorSyntax_6140_,
            v_numParams_6141_,
            v_name_6142_,
            v_ctor_6143_,
            v_a_6144_,
            v_a_6145_,
            v_a_6146_,
            v_a_6147_,
            v_a_6148_,
            v_a_6149_,
        );
    lean_dec(v_a_6149_);
    lean_dec_ref(v_a_6148_);
    lean_dec(v_a_6147_);
    lean_dec_ref(v_a_6146_);
    lean_dec(v_a_6145_);
    lean_dec_ref(v_a_6144_);
    return v_res_6151_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(
    mut v_mvarId_6152_: *mut LeanObject,
    mut v_val_6153_: *mut LeanObject,
    mut v___y_6154_: *mut LeanObject,
    mut v___y_6155_: *mut LeanObject,
    mut v___y_6156_: *mut LeanObject,
    mut v___y_6157_: *mut LeanObject,
    mut v___y_6158_: *mut LeanObject,
    mut v___y_6159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    v___x_6161_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_6152_, v_val_6153_, v___y_6157_);
    return v___x_6161_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(
    mut v_mvarId_6162_: *mut LeanObject,
    mut v_val_6163_: *mut LeanObject,
    mut v___y_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
    mut v___y_6167_: *mut LeanObject,
    mut v___y_6168_: *mut LeanObject,
    mut v___y_6169_: *mut LeanObject,
    mut v___y_6170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6171_: *mut LeanObject = core::ptr::null_mut();
    v_res_6171_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_mvarId_6162_, v_val_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
    lean_dec(v___y_6169_);
    lean_dec_ref(v___y_6168_);
    lean_dec(v___y_6167_);
    lean_dec_ref(v___y_6166_);
    lean_dec(v___y_6165_);
    lean_dec_ref(v___y_6164_);
    return v_res_6171_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(
    mut v_cls_6172_: *mut LeanObject,
    mut v_msg_6173_: *mut LeanObject,
    mut v___y_6174_: *mut LeanObject,
    mut v___y_6175_: *mut LeanObject,
    mut v___y_6176_: *mut LeanObject,
    mut v___y_6177_: *mut LeanObject,
    mut v___y_6178_: *mut LeanObject,
    mut v___y_6179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    v___x_6181_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_6172_, v_msg_6173_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
    return v___x_6181_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(
    mut v_cls_6182_: *mut LeanObject,
    mut v_msg_6183_: *mut LeanObject,
    mut v___y_6184_: *mut LeanObject,
    mut v___y_6185_: *mut LeanObject,
    mut v___y_6186_: *mut LeanObject,
    mut v___y_6187_: *mut LeanObject,
    mut v___y_6188_: *mut LeanObject,
    mut v___y_6189_: *mut LeanObject,
    mut v___y_6190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6191_: *mut LeanObject = core::ptr::null_mut();
    v_res_6191_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_cls_6182_, v_msg_6183_, v___y_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_);
    lean_dec(v___y_6189_);
    lean_dec_ref(v___y_6188_);
    lean_dec(v___y_6187_);
    lean_dec_ref(v___y_6186_);
    lean_dec(v___y_6185_);
    lean_dec_ref(v___y_6184_);
    return v_res_6191_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    v___x_6192_ = l_instMonadEIO(lean_box(0));
    return v___x_6192_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(
    mut v_msg_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
    mut v___y_6202_: *mut LeanObject,
    mut v___y_6203_: *mut LeanObject,
    mut v___y_6204_: *mut LeanObject,
    mut v___y_6205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6212_: u8 = 0;
    let mut v_toFunctor_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6219_: u8 = 0;
    let mut v___f_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6236_: u8 = 0;
    let mut v_toFunctor_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6243_: u8 = 0;
    let mut v___f_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6260_: u8 = 0;
    let mut v_toFunctor_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6267_: u8 = 0;
    let mut v___f_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780__overap_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6286_: u8 = 0;
    let mut v_unused_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6288_: u8 = 0;
    let mut v_unused_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6292_: u8 = 0;
    let mut v_unused_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6294_: u8 = 0;
    let mut v_unused_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6298_: u8 = 0;
    let mut v_unused_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6300_: u8 = 0;
    let mut v_unused_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6207_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0);
                v___x_6208_ = l_StateRefT_x27_instMonad___redArg(v___x_6207_);
                v_toApplicative_6209_ = lean_ctor_get(v___x_6208_, 0);
                v_isSharedCheck_6300_ = (!lean_is_exclusive(v___x_6208_)) as u8;
                if v_isSharedCheck_6300_ == 0 {
                    v_unused_6301_ = lean_ctor_get(v___x_6208_, 1);
                    lean_dec(v_unused_6301_);
                    v___x_6211_ = v___x_6208_;
                    v_isShared_6212_ = v_isSharedCheck_6300_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_6209_);
                    lean_dec(v___x_6208_);
                    v___x_6211_ = lean_box(0);
                    v_isShared_6212_ = v_isSharedCheck_6300_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_6213_ = lean_ctor_get(v_toApplicative_6209_, 0);
                v_toSeq_6214_ = lean_ctor_get(v_toApplicative_6209_, 2);
                v_toSeqLeft_6215_ = lean_ctor_get(v_toApplicative_6209_, 3);
                v_toSeqRight_6216_ = lean_ctor_get(v_toApplicative_6209_, 4);
                v_isSharedCheck_6298_ = (!lean_is_exclusive(v_toApplicative_6209_)) as u8;
                if v_isSharedCheck_6298_ == 0 {
                    v_unused_6299_ = lean_ctor_get(v_toApplicative_6209_, 1);
                    lean_dec(v_unused_6299_);
                    v___x_6218_ = v_toApplicative_6209_;
                    v_isShared_6219_ = v_isSharedCheck_6298_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_6216_);
                    lean_inc(v_toSeqLeft_6215_);
                    lean_inc(v_toSeq_6214_);
                    lean_inc(v_toFunctor_6213_);
                    lean_dec(v_toApplicative_6209_);
                    v___x_6218_ = lean_box(0);
                    v_isShared_6219_ = v_isSharedCheck_6298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_6220_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1;
                v___f_6221_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2;
                lean_inc_ref(v_toFunctor_6213_);
                v___f_6222_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6222_, 0, v_toFunctor_6213_);
                v___f_6223_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6223_, 0, v_toFunctor_6213_);
                v___x_6224_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6224_, 0, v___f_6222_);
                lean_ctor_set(v___x_6224_, 1, v___f_6223_);
                v___f_6225_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6225_, 0, v_toSeqRight_6216_);
                v___f_6226_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6226_, 0, v_toSeqLeft_6215_);
                v___f_6227_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6227_, 0, v_toSeq_6214_);
                if v_isShared_6219_ == 0 {
                    lean_ctor_set(v___x_6218_, 4, v___f_6225_);
                    lean_ctor_set(v___x_6218_, 3, v___f_6226_);
                    lean_ctor_set(v___x_6218_, 2, v___f_6227_);
                    lean_ctor_set(v___x_6218_, 1, v___f_6220_);
                    lean_ctor_set(v___x_6218_, 0, v___x_6224_);
                    v___x_6229_ = v___x_6218_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6297_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6297_, 0, v___x_6224_);
                    lean_ctor_set(v_reuseFailAlloc_6297_, 1, v___f_6220_);
                    lean_ctor_set(v_reuseFailAlloc_6297_, 2, v___f_6227_);
                    lean_ctor_set(v_reuseFailAlloc_6297_, 3, v___f_6226_);
                    lean_ctor_set(v_reuseFailAlloc_6297_, 4, v___f_6225_);
                    v___x_6229_ = v_reuseFailAlloc_6297_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6212_ == 0 {
                    lean_ctor_set(v___x_6211_, 1, v___f_6221_);
                    lean_ctor_set(v___x_6211_, 0, v___x_6229_);
                    v___x_6231_ = v___x_6211_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6296_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6296_, 0, v___x_6229_);
                    lean_ctor_set(v_reuseFailAlloc_6296_, 1, v___f_6221_);
                    v___x_6231_ = v_reuseFailAlloc_6296_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6232_ = l_StateRefT_x27_instMonad___redArg(v___x_6231_);
                v_toApplicative_6233_ = lean_ctor_get(v___x_6232_, 0);
                v_isSharedCheck_6294_ = (!lean_is_exclusive(v___x_6232_)) as u8;
                if v_isSharedCheck_6294_ == 0 {
                    v_unused_6295_ = lean_ctor_get(v___x_6232_, 1);
                    lean_dec(v_unused_6295_);
                    v___x_6235_ = v___x_6232_;
                    v_isShared_6236_ = v_isSharedCheck_6294_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_6233_);
                    lean_dec(v___x_6232_);
                    v___x_6235_ = lean_box(0);
                    v_isShared_6236_ = v_isSharedCheck_6294_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_6237_ = lean_ctor_get(v_toApplicative_6233_, 0);
                v_toSeq_6238_ = lean_ctor_get(v_toApplicative_6233_, 2);
                v_toSeqLeft_6239_ = lean_ctor_get(v_toApplicative_6233_, 3);
                v_toSeqRight_6240_ = lean_ctor_get(v_toApplicative_6233_, 4);
                v_isSharedCheck_6292_ = (!lean_is_exclusive(v_toApplicative_6233_)) as u8;
                if v_isSharedCheck_6292_ == 0 {
                    v_unused_6293_ = lean_ctor_get(v_toApplicative_6233_, 1);
                    lean_dec(v_unused_6293_);
                    v___x_6242_ = v_toApplicative_6233_;
                    v_isShared_6243_ = v_isSharedCheck_6292_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_6240_);
                    lean_inc(v_toSeqLeft_6239_);
                    lean_inc(v_toSeq_6238_);
                    lean_inc(v_toFunctor_6237_);
                    lean_dec(v_toApplicative_6233_);
                    v___x_6242_ = lean_box(0);
                    v_isShared_6243_ = v_isSharedCheck_6292_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_6244_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3;
                v___f_6245_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4;
                lean_inc_ref(v_toFunctor_6237_);
                v___f_6246_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6246_, 0, v_toFunctor_6237_);
                v___f_6247_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6247_, 0, v_toFunctor_6237_);
                v___x_6248_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6248_, 0, v___f_6246_);
                lean_ctor_set(v___x_6248_, 1, v___f_6247_);
                v___f_6249_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6249_, 0, v_toSeqRight_6240_);
                v___f_6250_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6250_, 0, v_toSeqLeft_6239_);
                v___f_6251_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6251_, 0, v_toSeq_6238_);
                if v_isShared_6243_ == 0 {
                    lean_ctor_set(v___x_6242_, 4, v___f_6249_);
                    lean_ctor_set(v___x_6242_, 3, v___f_6250_);
                    lean_ctor_set(v___x_6242_, 2, v___f_6251_);
                    lean_ctor_set(v___x_6242_, 1, v___f_6244_);
                    lean_ctor_set(v___x_6242_, 0, v___x_6248_);
                    v___x_6253_ = v___x_6242_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6291_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6291_, 0, v___x_6248_);
                    lean_ctor_set(v_reuseFailAlloc_6291_, 1, v___f_6244_);
                    lean_ctor_set(v_reuseFailAlloc_6291_, 2, v___f_6251_);
                    lean_ctor_set(v_reuseFailAlloc_6291_, 3, v___f_6250_);
                    lean_ctor_set(v_reuseFailAlloc_6291_, 4, v___f_6249_);
                    v___x_6253_ = v_reuseFailAlloc_6291_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6236_ == 0 {
                    lean_ctor_set(v___x_6235_, 1, v___f_6245_);
                    lean_ctor_set(v___x_6235_, 0, v___x_6253_);
                    v___x_6255_ = v___x_6235_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6290_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6290_, 0, v___x_6253_);
                    lean_ctor_set(v_reuseFailAlloc_6290_, 1, v___f_6245_);
                    v___x_6255_ = v_reuseFailAlloc_6290_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6256_ = l_StateRefT_x27_instMonad___redArg(v___x_6255_);
                v_toApplicative_6257_ = lean_ctor_get(v___x_6256_, 0);
                v_isSharedCheck_6288_ = (!lean_is_exclusive(v___x_6256_)) as u8;
                if v_isSharedCheck_6288_ == 0 {
                    v_unused_6289_ = lean_ctor_get(v___x_6256_, 1);
                    lean_dec(v_unused_6289_);
                    v___x_6259_ = v___x_6256_;
                    v_isShared_6260_ = v_isSharedCheck_6288_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_toApplicative_6257_);
                    lean_dec(v___x_6256_);
                    v___x_6259_ = lean_box(0);
                    v_isShared_6260_ = v_isSharedCheck_6288_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_toFunctor_6261_ = lean_ctor_get(v_toApplicative_6257_, 0);
                v_toSeq_6262_ = lean_ctor_get(v_toApplicative_6257_, 2);
                v_toSeqLeft_6263_ = lean_ctor_get(v_toApplicative_6257_, 3);
                v_toSeqRight_6264_ = lean_ctor_get(v_toApplicative_6257_, 4);
                v_isSharedCheck_6286_ = (!lean_is_exclusive(v_toApplicative_6257_)) as u8;
                if v_isSharedCheck_6286_ == 0 {
                    v_unused_6287_ = lean_ctor_get(v_toApplicative_6257_, 1);
                    lean_dec(v_unused_6287_);
                    v___x_6266_ = v_toApplicative_6257_;
                    v_isShared_6267_ = v_isSharedCheck_6286_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_6264_);
                    lean_inc(v_toSeqLeft_6263_);
                    lean_inc(v_toSeq_6262_);
                    lean_inc(v_toFunctor_6261_);
                    lean_dec(v_toApplicative_6257_);
                    v___x_6266_ = lean_box(0);
                    v_isShared_6267_ = v_isSharedCheck_6286_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___f_6268_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5;
                v___f_6269_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6;
                lean_inc_ref(v_toFunctor_6261_);
                v___f_6270_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6270_, 0, v_toFunctor_6261_);
                v___f_6271_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6271_, 0, v_toFunctor_6261_);
                v___x_6272_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6272_, 0, v___f_6270_);
                lean_ctor_set(v___x_6272_, 1, v___f_6271_);
                v___f_6273_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6273_, 0, v_toSeqRight_6264_);
                v___f_6274_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6274_, 0, v_toSeqLeft_6263_);
                v___f_6275_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6275_, 0, v_toSeq_6262_);
                if v_isShared_6267_ == 0 {
                    lean_ctor_set(v___x_6266_, 4, v___f_6273_);
                    lean_ctor_set(v___x_6266_, 3, v___f_6274_);
                    lean_ctor_set(v___x_6266_, 2, v___f_6275_);
                    lean_ctor_set(v___x_6266_, 1, v___f_6268_);
                    lean_ctor_set(v___x_6266_, 0, v___x_6272_);
                    v___x_6277_ = v___x_6266_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6285_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 0, v___x_6272_);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 1, v___f_6268_);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 2, v___f_6275_);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 3, v___f_6274_);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 4, v___f_6273_);
                    v___x_6277_ = v_reuseFailAlloc_6285_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_6260_ == 0 {
                    lean_ctor_set(v___x_6259_, 1, v___f_6269_);
                    lean_ctor_set(v___x_6259_, 0, v___x_6277_);
                    v___x_6279_ = v___x_6259_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6284_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6284_, 0, v___x_6277_);
                    lean_ctor_set(v_reuseFailAlloc_6284_, 1, v___f_6269_);
                    v___x_6279_ = v_reuseFailAlloc_6284_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6280_ = lean_box(0);
                v___x_6281_ = l_instInhabitedOfMonad___redArg(v___x_6279_, v___x_6280_);
                v___x_3780__overap_6282_ = lean_panic_fn_borrowed(v___x_6281_, v_msg_6199_);
                lean_dec(v___x_6281_);
                lean_inc(v___y_6205_);
                lean_inc_ref(v___y_6204_);
                lean_inc(v___y_6203_);
                lean_inc_ref(v___y_6202_);
                lean_inc(v___y_6201_);
                lean_inc_ref(v___y_6200_);
                v___x_6283_ = lean_apply_7(
                    v___x_3780__overap_6282_,
                    v___y_6200_,
                    v___y_6201_,
                    v___y_6202_,
                    v___y_6203_,
                    v___y_6204_,
                    v___y_6205_,
                    lean_box(0),
                );
                return v___x_6283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(
    mut v_msg_6302_: *mut LeanObject,
    mut v___y_6303_: *mut LeanObject,
    mut v___y_6304_: *mut LeanObject,
    mut v___y_6305_: *mut LeanObject,
    mut v___y_6306_: *mut LeanObject,
    mut v___y_6307_: *mut LeanObject,
    mut v___y_6308_: *mut LeanObject,
    mut v___y_6309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6310_: *mut LeanObject = core::ptr::null_mut();
    v_res_6310_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_, v___y_6308_);
    lean_dec(v___y_6308_);
    lean_dec_ref(v___y_6307_);
    lean_dec(v___y_6306_);
    lean_dec_ref(v___y_6305_);
    lean_dec(v___y_6304_);
    lean_dec_ref(v___y_6303_);
    return v_res_6310_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(
    mut v_opts_6311_: *mut LeanObject,
    mut v_opt_6312_: *mut LeanObject,
) -> u8 {
    let mut v_name_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    v_name_6313_ = lean_ctor_get(v_opt_6312_, 0);
    v_defValue_6314_ = lean_ctor_get(v_opt_6312_, 1);
    v_map_6315_ = lean_ctor_get(v_opts_6311_, 0);
    v___x_6316_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_6315_,
            v_name_6313_,
        );
    if lean_obj_tag(v___x_6316_) == 0 {
        let mut v___x_6317_: u8 = 0;
        v___x_6317_ = (lean_unbox(v_defValue_6314_) as u8);
        return v___x_6317_;
    } else {
        let mut v_val_6318_: *mut LeanObject = core::ptr::null_mut();
        v_val_6318_ = lean_ctor_get(v___x_6316_, 0);
        lean_inc(v_val_6318_);
        lean_dec_ref_known(v___x_6316_, 1);
        if lean_obj_tag(v_val_6318_) == 1 {
            let mut v_v_6319_: u8 = 0;
            v_v_6319_ = lean_ctor_get_uint8(v_val_6318_, 0 as u32);
            lean_dec_ref_known(v_val_6318_, 0);
            return v_v_6319_;
        } else {
            let mut v___x_6320_: u8 = 0;
            lean_dec(v_val_6318_);
            v___x_6320_ = (lean_unbox(v_defValue_6314_) as u8);
            return v___x_6320_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_opts_6321_: *mut LeanObject,
    mut v_opt_6322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6323_: u8 = 0;
    let mut v_r_6324_: *mut LeanObject = core::ptr::null_mut();
    v_res_6323_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_6321_, v_opt_6322_);
    lean_dec_ref(v_opt_6322_);
    lean_dec_ref(v_opts_6321_);
    v_r_6324_ = lean_box((v_res_6323_) as usize);
    return v_r_6324_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0()
-> *mut LeanObject {
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    v___x_6325_ = lean_box(1);
    v___x_6326_ = l_Lean_MessageData_ofFormat(v___x_6325_);
    return v___x_6326_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3()
-> *mut LeanObject {
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    v___x_6330_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2;
    v___x_6331_ = l_Lean_MessageData_ofFormat(v___x_6330_);
    return v___x_6331_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(
    mut v_x_6332_: *mut LeanObject,
    mut v_x_6333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6338_: u8 = 0;
    let mut v_before_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6342_: u8 = 0;
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6355_: u8 = 0;
    let mut v_unused_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6333_) == 0 {
                    return v_x_6332_;
                } else {
                    v_head_6334_ = lean_ctor_get(v_x_6333_, 0);
                    v_tail_6335_ = lean_ctor_get(v_x_6333_, 1);
                    v_isSharedCheck_6357_ = (!lean_is_exclusive(v_x_6333_)) as u8;
                    if v_isSharedCheck_6357_ == 0 {
                        v___x_6337_ = v_x_6333_;
                        v_isShared_6338_ = v_isSharedCheck_6357_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6335_);
                        lean_inc(v_head_6334_);
                        lean_dec(v_x_6333_);
                        v___x_6337_ = lean_box(0);
                        v_isShared_6338_ = v_isSharedCheck_6357_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_6339_ = lean_ctor_get(v_head_6334_, 0);
                v_isSharedCheck_6355_ = (!lean_is_exclusive(v_head_6334_)) as u8;
                if v_isSharedCheck_6355_ == 0 {
                    v_unused_6356_ = lean_ctor_get(v_head_6334_, 1);
                    lean_dec(v_unused_6356_);
                    v___x_6341_ = v_head_6334_;
                    v_isShared_6342_ = v_isSharedCheck_6355_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_6339_);
                    lean_dec(v_head_6334_);
                    v___x_6341_ = lean_box(0);
                    v_isShared_6342_ = v_isSharedCheck_6355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6343_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
                if v_isShared_6342_ == 0 {
                    lean_ctor_set_tag(v___x_6341_, 7);
                    lean_ctor_set(v___x_6341_, 1, v___x_6343_);
                    lean_ctor_set(v___x_6341_, 0, v_x_6332_);
                    v___x_6345_ = v___x_6341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6354_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6354_, 0, v_x_6332_);
                    lean_ctor_set(v_reuseFailAlloc_6354_, 1, v___x_6343_);
                    v___x_6345_ = v_reuseFailAlloc_6354_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6346_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3);
                if v_isShared_6338_ == 0 {
                    lean_ctor_set_tag(v___x_6337_, 7);
                    lean_ctor_set(v___x_6337_, 1, v___x_6346_);
                    lean_ctor_set(v___x_6337_, 0, v___x_6345_);
                    v___x_6348_ = v___x_6337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6353_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6353_, 0, v___x_6345_);
                    lean_ctor_set(v_reuseFailAlloc_6353_, 1, v___x_6346_);
                    v___x_6348_ = v_reuseFailAlloc_6353_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6349_ = l_Lean_MessageData_ofSyntax(v_before_6339_);
                v___x_6350_ = l_Lean_indentD(v___x_6349_);
                v___x_6351_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6351_, 0, v___x_6348_);
                lean_ctor_set(v___x_6351_, 1, v___x_6350_);
                v_x_6332_ = v___x_6351_;
                v_x_6333_ = v_tail_6335_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    v___x_6361_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1;
    v___x_6362_ = l_Lean_MessageData_ofFormat(v___x_6361_);
    return v___x_6362_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(
    mut v_msgData_6363_: *mut LeanObject,
    mut v_macroStack_6364_: *mut LeanObject,
    mut v___y_6365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: u8 = 0;
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6376_: u8 = 0;
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6388_: u8 = 0;
    let mut v_unused_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_6367_ = lean_ctor_get(v___y_6365_, 2);
                v___x_6368_ = l_Lean_Elab_pp_macroStack;
                v___x_6369_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_options_6367_, v___x_6368_);
                if v___x_6369_ == 0 {
                    lean_dec(v_macroStack_6364_);
                    v___x_6370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6370_, 0, v_msgData_6363_);
                    return v___x_6370_;
                } else {
                    if lean_obj_tag(v_macroStack_6364_) == 0 {
                        v___x_6371_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6371_, 0, v_msgData_6363_);
                        return v___x_6371_;
                    } else {
                        v_head_6372_ = lean_ctor_get(v_macroStack_6364_, 0);
                        lean_inc(v_head_6372_);
                        v_after_6373_ = lean_ctor_get(v_head_6372_, 1);
                        v_isSharedCheck_6388_ = (!lean_is_exclusive(v_head_6372_)) as u8;
                        if v_isSharedCheck_6388_ == 0 {
                            v_unused_6389_ = lean_ctor_get(v_head_6372_, 0);
                            lean_dec(v_unused_6389_);
                            v___x_6375_ = v_head_6372_;
                            v_isShared_6376_ = v_isSharedCheck_6388_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_6373_);
                            lean_dec(v_head_6372_);
                            v___x_6375_ = lean_box(0);
                            v_isShared_6376_ = v_isSharedCheck_6388_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6377_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
                if v_isShared_6376_ == 0 {
                    lean_ctor_set_tag(v___x_6375_, 7);
                    lean_ctor_set(v___x_6375_, 1, v___x_6377_);
                    lean_ctor_set(v___x_6375_, 0, v_msgData_6363_);
                    v___x_6379_ = v___x_6375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6387_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6387_, 0, v_msgData_6363_);
                    lean_ctor_set(v_reuseFailAlloc_6387_, 1, v___x_6377_);
                    v___x_6379_ = v_reuseFailAlloc_6387_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6380_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2);
                v___x_6381_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6381_, 0, v___x_6379_);
                lean_ctor_set(v___x_6381_, 1, v___x_6380_);
                v___x_6382_ = l_Lean_MessageData_ofSyntax(v_after_6373_);
                v___x_6383_ = l_Lean_indentD(v___x_6382_);
                v_msgData_6384_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_6384_, 0, v___x_6381_);
                lean_ctor_set(v_msgData_6384_, 1, v___x_6383_);
                v___x_6385_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(v_msgData_6384_, v_macroStack_6364_);
                v___x_6386_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6386_, 0, v___x_6385_);
                return v___x_6386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msgData_6390_: *mut LeanObject,
    mut v_macroStack_6391_: *mut LeanObject,
    mut v___y_6392_: *mut LeanObject,
    mut v___y_6393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6394_: *mut LeanObject = core::ptr::null_mut();
    v_res_6394_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_6390_, v_macroStack_6391_, v___y_6392_);
    lean_dec_ref(v___y_6392_);
    return v_res_6394_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(
    mut v_msg_6395_: *mut LeanObject,
    mut v___y_6396_: *mut LeanObject,
    mut v___y_6397_: *mut LeanObject,
    mut v___y_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
    mut v___y_6400_: *mut LeanObject,
    mut v___y_6401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6412_: u8 = 0;
    let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6403_ = lean_ctor_get(v___y_6400_, 5);
                v___x_6404_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_6395_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_);
                v_a_6405_ = lean_ctor_get(v___x_6404_, 0);
                lean_inc(v_a_6405_);
                lean_dec_ref(v___x_6404_);
                v_macroStack_6406_ = lean_ctor_get(v___y_6396_, 1);
                v___x_6407_ = l_Lean_Elab_getBetterRef(v_ref_6403_, v_macroStack_6406_);
                lean_inc(v_macroStack_6406_);
                v___x_6408_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_6405_, v_macroStack_6406_, v___y_6400_);
                v_a_6409_ = lean_ctor_get(v___x_6408_, 0);
                v_isSharedCheck_6417_ = (!lean_is_exclusive(v___x_6408_)) as u8;
                if v_isSharedCheck_6417_ == 0 {
                    v___x_6411_ = v___x_6408_;
                    v_isShared_6412_ = v_isSharedCheck_6417_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6409_);
                    lean_dec(v___x_6408_);
                    v___x_6411_ = lean_box(0);
                    v_isShared_6412_ = v_isSharedCheck_6417_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6413_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6413_, 0, v___x_6407_);
                lean_ctor_set(v___x_6413_, 1, v_a_6409_);
                if v_isShared_6412_ == 0 {
                    lean_ctor_set_tag(v___x_6411_, 1);
                    lean_ctor_set(v___x_6411_, 0, v___x_6413_);
                    v___x_6415_ = v___x_6411_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6416_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6416_, 0, v___x_6413_);
                    v___x_6415_ = v_reuseFailAlloc_6416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6415_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(
    mut v_msg_6418_: *mut LeanObject,
    mut v___y_6419_: *mut LeanObject,
    mut v___y_6420_: *mut LeanObject,
    mut v___y_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
    mut v___y_6425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6426_: *mut LeanObject = core::ptr::null_mut();
    v_res_6426_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_);
    lean_dec(v___y_6424_);
    lean_dec_ref(v___y_6423_);
    lean_dec(v___y_6422_);
    lean_dec_ref(v___y_6421_);
    lean_dec(v___y_6420_);
    lean_dec_ref(v___y_6419_);
    return v_res_6426_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    v___x_6428_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0;
    v___x_6429_ = l_Lean_stringToMessageData(v___x_6428_);
    return v___x_6429_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    v___x_6431_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2;
    v___x_6432_ = l_Lean_stringToMessageData(v___x_6431_);
    return v___x_6432_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7()
-> *mut LeanObject {
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    v___x_6436_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6;
    v___x_6437_ = lean_unsigned_to_nat(11);
    v___x_6438_ = lean_unsigned_to_nat(122);
    v___x_6439_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5;
    v___x_6440_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4;
    v___x_6441_ = l_mkPanicMessageWithDecl(
        v___x_6440_,
        v___x_6439_,
        v___x_6438_,
        v___x_6437_,
        v___x_6436_,
    );
    return v___x_6441_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(
    mut v_constName_6442_: *mut LeanObject,
    mut v___y_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
    mut v___y_6445_: *mut LeanObject,
    mut v___y_6446_: *mut LeanObject,
    mut v___y_6447_: *mut LeanObject,
    mut v___y_6448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: u8 = 0;
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: u8 = 0;
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_6463_: u8 = 0;
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6468_: u8 = 0;
    let mut v___x_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6472_: u8 = 0;
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6478_: u8 = 0;
    let mut v_val_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6483_: u8 = 0;
    let mut v_a_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6487_: u8 = 0;
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6458_ = lean_st_ref_get(v___y_6448_);
                v_env_6459_ = lean_ctor_get(v___x_6458_, 0);
                lean_inc_ref(v_env_6459_);
                lean_dec(v___x_6458_);
                v___x_6460_ = 0;
                lean_inc(v_constName_6442_);
                v___x_6461_ =
                    l_Lean_Environment_findAsync_x3f(v_env_6459_, v_constName_6442_, v___x_6460_);
                if lean_obj_tag(v___x_6461_) == 1 {
                    v_val_6462_ = lean_ctor_get(v___x_6461_, 0);
                    lean_inc(v_val_6462_);
                    lean_dec_ref_known(v___x_6461_, 1);
                    v_kind_6463_ = lean_ctor_get_uint8(
                        v_val_6462_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_kind_6463_ == 6 {
                        v___x_6464_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_6462_);
                        if lean_obj_tag(v___x_6464_) == 6 {
                            lean_dec(v_constName_6442_);
                            v_val_6465_ = lean_ctor_get(v___x_6464_, 0);
                            v_isSharedCheck_6472_ = (!lean_is_exclusive(v___x_6464_)) as u8;
                            if v_isSharedCheck_6472_ == 0 {
                                v___x_6467_ = v___x_6464_;
                                v_isShared_6468_ = v_isSharedCheck_6472_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_6465_);
                                lean_dec(v___x_6464_);
                                v___x_6467_ = lean_box(0);
                                v_isShared_6468_ = v_isSharedCheck_6472_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_6464_);
                            v___x_6473_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7);
                            v___x_6474_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v___x_6473_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
                            if lean_obj_tag(v___x_6474_) == 0 {
                                v_a_6475_ = lean_ctor_get(v___x_6474_, 0);
                                v_isSharedCheck_6483_ = (!lean_is_exclusive(v___x_6474_)) as u8;
                                if v_isSharedCheck_6483_ == 0 {
                                    v___x_6477_ = v___x_6474_;
                                    v_isShared_6478_ = v_isSharedCheck_6483_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_6475_);
                                    lean_dec(v___x_6474_);
                                    v___x_6477_ = lean_box(0);
                                    v_isShared_6478_ = v_isSharedCheck_6483_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_constName_6442_);
                                v_a_6484_ = lean_ctor_get(v___x_6474_, 0);
                                v_isSharedCheck_6491_ = (!lean_is_exclusive(v___x_6474_)) as u8;
                                if v_isSharedCheck_6491_ == 0 {
                                    v___x_6486_ = v___x_6474_;
                                    v_isShared_6487_ = v_isSharedCheck_6491_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_6484_);
                                    lean_dec(v___x_6474_);
                                    v___x_6486_ = lean_box(0);
                                    v_isShared_6487_ = v_isSharedCheck_6491_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_6462_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6461_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6451_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
                v___x_6452_ = 0;
                v___x_6453_ = l_Lean_MessageData_ofConstName(v_constName_6442_, v___x_6452_);
                v___x_6454_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6454_, 0, v___x_6451_);
                lean_ctor_set(v___x_6454_, 1, v___x_6453_);
                v___x_6455_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3);
                v___x_6456_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6456_, 0, v___x_6454_);
                lean_ctor_set(v___x_6456_, 1, v___x_6455_);
                v___x_6457_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_6456_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
                return v___x_6457_;
            }
            2 => {
                if v_isShared_6468_ == 0 {
                    lean_ctor_set_tag(v___x_6467_, 0);
                    v___x_6470_ = v___x_6467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6471_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6471_, 0, v_val_6465_);
                    v___x_6470_ = v_reuseFailAlloc_6471_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6470_;
            }
            4 => {
                if lean_obj_tag(v_a_6475_) == 0 {
                    lean_del_object(v___x_6477_);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_constName_6442_);
                    v_val_6479_ = lean_ctor_get(v_a_6475_, 0);
                    lean_inc(v_val_6479_);
                    lean_dec_ref_known(v_a_6475_, 1);
                    if v_isShared_6478_ == 0 {
                        lean_ctor_set(v___x_6477_, 0, v_val_6479_);
                        v___x_6481_ = v___x_6477_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6482_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6482_, 0, v_val_6479_);
                        v___x_6481_ = v_reuseFailAlloc_6482_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_6481_;
            }
            6 => {
                if v_isShared_6487_ == 0 {
                    v___x_6489_ = v___x_6486_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6490_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6490_, 0, v_a_6484_);
                    v___x_6489_ = v_reuseFailAlloc_6490_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6489_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(
    mut v_constName_6492_: *mut LeanObject,
    mut v___y_6493_: *mut LeanObject,
    mut v___y_6494_: *mut LeanObject,
    mut v___y_6495_: *mut LeanObject,
    mut v___y_6496_: *mut LeanObject,
    mut v___y_6497_: *mut LeanObject,
    mut v___y_6498_: *mut LeanObject,
    mut v___y_6499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6500_: *mut LeanObject = core::ptr::null_mut();
    v_res_6500_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_);
    lean_dec(v___y_6498_);
    lean_dec_ref(v___y_6497_);
    lean_dec(v___y_6496_);
    lean_dec_ref(v___y_6495_);
    lean_dec(v___y_6494_);
    lean_dec_ref(v___y_6493_);
    return v_res_6500_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(
    mut v_a_6501_: *mut LeanObject,
    mut v_infos_6502_: *mut LeanObject,
    mut v_numParams_6503_: *mut LeanObject,
    mut v_as_x27_6504_: *mut LeanObject,
    mut v_b_6505_: *mut LeanObject,
    mut v___y_6506_: *mut LeanObject,
    mut v___y_6507_: *mut LeanObject,
    mut v___y_6508_: *mut LeanObject,
    mut v___y_6509_: *mut LeanObject,
    mut v___y_6510_: *mut LeanObject,
    mut v___y_6511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: u8 = 0;
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6523_: u8 = 0;
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6539_: u8 = 0;
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6543_: u8 = 0;
    let mut v_a_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6547_: u8 = 0;
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6551_: u8 = 0;
    let mut v_isSharedCheck_6552_: u8 = 0;
    let mut v_unused_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_6504_) == 0 {
                    lean_dec(v_numParams_6503_);
                    lean_dec_ref(v_infos_6502_);
                    lean_dec_ref(v_a_6501_);
                    v___x_6513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6513_, 0, v_b_6505_);
                    return v___x_6513_;
                } else {
                    v_head_6514_ = lean_ctor_get(v_as_x27_6504_, 0);
                    v_tail_6515_ = lean_ctor_get(v_as_x27_6504_, 1);
                    v_array_6516_ = lean_ctor_get(v_b_6505_, 0);
                    v_start_6517_ = lean_ctor_get(v_b_6505_, 1);
                    v_stop_6518_ = lean_ctor_get(v_b_6505_, 2);
                    v___x_6519_ = lean_nat_dec_lt(v_start_6517_, v_stop_6518_);
                    if v___x_6519_ == 0 {
                        lean_dec(v_numParams_6503_);
                        lean_dec_ref(v_infos_6502_);
                        lean_dec_ref(v_a_6501_);
                        v___x_6520_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6520_, 0, v_b_6505_);
                        return v___x_6520_;
                    } else {
                        lean_inc(v_stop_6518_);
                        lean_inc(v_start_6517_);
                        lean_inc_ref(v_array_6516_);
                        v_isSharedCheck_6552_ = (!lean_is_exclusive(v_b_6505_)) as u8;
                        if v_isSharedCheck_6552_ == 0 {
                            v_unused_6553_ = lean_ctor_get(v_b_6505_, 2);
                            lean_dec(v_unused_6553_);
                            v_unused_6554_ = lean_ctor_get(v_b_6505_, 1);
                            lean_dec(v_unused_6554_);
                            v_unused_6555_ = lean_ctor_get(v_b_6505_, 0);
                            lean_dec(v_unused_6555_);
                            v___x_6522_ = v_b_6505_;
                            v_isShared_6523_ = v_isSharedCheck_6552_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_b_6505_);
                            v___x_6522_ = lean_box(0);
                            v_isShared_6523_ = v_isSharedCheck_6552_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_head_6514_);
                v___x_6524_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_6514_, v___y_6506_, v___y_6507_, v___y_6508_, v___y_6509_, v___y_6510_, v___y_6511_);
                if lean_obj_tag(v___x_6524_) == 0 {
                    v_toConstantVal_6525_ = lean_ctor_get(v_a_6501_, 0);
                    v_a_6526_ = lean_ctor_get(v___x_6524_, 0);
                    lean_inc(v_a_6526_);
                    lean_dec_ref_known(v___x_6524_, 1);
                    v_name_6527_ = lean_ctor_get(v_toConstantVal_6525_, 0);
                    v___x_6528_ = lean_array_fget_borrowed(v_array_6516_, v_start_6517_);
                    lean_inc(v_name_6527_);
                    lean_inc(v_numParams_6503_);
                    lean_inc(v___x_6528_);
                    lean_inc_ref(v_infos_6502_);
                    v___x_6529_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_6502_, v___x_6528_, v_numParams_6503_, v_name_6527_, v_a_6526_, v___y_6506_, v___y_6507_, v___y_6508_, v___y_6509_, v___y_6510_, v___y_6511_);
                    if lean_obj_tag(v___x_6529_) == 0 {
                        lean_dec_ref_known(v___x_6529_, 1);
                        v___x_6530_ = lean_unsigned_to_nat(1);
                        v___x_6531_ = lean_nat_add(v_start_6517_, v___x_6530_);
                        lean_dec(v_start_6517_);
                        if v_isShared_6523_ == 0 {
                            lean_ctor_set(v___x_6522_, 1, v___x_6531_);
                            v___x_6533_ = v___x_6522_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6535_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6535_, 0, v_array_6516_);
                            lean_ctor_set(v_reuseFailAlloc_6535_, 1, v___x_6531_);
                            lean_ctor_set(v_reuseFailAlloc_6535_, 2, v_stop_6518_);
                            v___x_6533_ = v_reuseFailAlloc_6535_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6522_);
                        lean_dec(v_stop_6518_);
                        lean_dec(v_start_6517_);
                        lean_dec_ref(v_array_6516_);
                        lean_dec(v_numParams_6503_);
                        lean_dec_ref(v_infos_6502_);
                        lean_dec_ref(v_a_6501_);
                        v_a_6536_ = lean_ctor_get(v___x_6529_, 0);
                        v_isSharedCheck_6543_ = (!lean_is_exclusive(v___x_6529_)) as u8;
                        if v_isSharedCheck_6543_ == 0 {
                            v___x_6538_ = v___x_6529_;
                            v_isShared_6539_ = v_isSharedCheck_6543_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6536_);
                            lean_dec(v___x_6529_);
                            v___x_6538_ = lean_box(0);
                            v_isShared_6539_ = v_isSharedCheck_6543_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6522_);
                    lean_dec(v_stop_6518_);
                    lean_dec(v_start_6517_);
                    lean_dec_ref(v_array_6516_);
                    lean_dec(v_numParams_6503_);
                    lean_dec_ref(v_infos_6502_);
                    lean_dec_ref(v_a_6501_);
                    v_a_6544_ = lean_ctor_get(v___x_6524_, 0);
                    v_isSharedCheck_6551_ = (!lean_is_exclusive(v___x_6524_)) as u8;
                    if v_isSharedCheck_6551_ == 0 {
                        v___x_6546_ = v___x_6524_;
                        v_isShared_6547_ = v_isSharedCheck_6551_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6544_);
                        lean_dec(v___x_6524_);
                        v___x_6546_ = lean_box(0);
                        v_isShared_6547_ = v_isSharedCheck_6551_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_as_x27_6504_ = v_tail_6515_;
                v_b_6505_ = v___x_6533_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6539_ == 0 {
                    v___x_6541_ = v___x_6538_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6542_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6542_, 0, v_a_6536_);
                    v___x_6541_ = v_reuseFailAlloc_6542_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6541_;
            }
            5 => {
                if v_isShared_6547_ == 0 {
                    v___x_6549_ = v___x_6546_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6550_, 0, v_a_6544_);
                    v___x_6549_ = v_reuseFailAlloc_6550_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(
    mut v_a_6556_: *mut LeanObject,
    mut v_infos_6557_: *mut LeanObject,
    mut v_numParams_6558_: *mut LeanObject,
    mut v_as_x27_6559_: *mut LeanObject,
    mut v_b_6560_: *mut LeanObject,
    mut v___y_6561_: *mut LeanObject,
    mut v___y_6562_: *mut LeanObject,
    mut v___y_6563_: *mut LeanObject,
    mut v___y_6564_: *mut LeanObject,
    mut v___y_6565_: *mut LeanObject,
    mut v___y_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6568_: *mut LeanObject = core::ptr::null_mut();
    v_res_6568_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_6556_, v_infos_6557_, v_numParams_6558_, v_as_x27_6559_, v_b_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_, v___y_6566_);
    lean_dec(v___y_6566_);
    lean_dec_ref(v___y_6565_);
    lean_dec(v___y_6564_);
    lean_dec_ref(v___y_6563_);
    lean_dec(v___y_6562_);
    lean_dec_ref(v___y_6561_);
    lean_dec(v_as_x27_6559_);
    return v_res_6568_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(
    mut v_infos_6569_: *mut LeanObject,
    mut v_numParams_6570_: *mut LeanObject,
    mut v_as_6571_: *mut LeanObject,
    mut v_sz_6572_: usize,
    mut v_i_6573_: usize,
    mut v_b_6574_: *mut LeanObject,
    mut v___y_6575_: *mut LeanObject,
    mut v___y_6576_: *mut LeanObject,
    mut v___y_6577_: *mut LeanObject,
    mut v___y_6578_: *mut LeanObject,
    mut v___y_6579_: *mut LeanObject,
    mut v___y_6580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6582_: u8 = 0;
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: u8 = 0;
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6591_: u8 = 0;
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorSyntax_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: usize = 0;
    let mut v___x_6605_: usize = 0;
    let mut v_reuseFailAlloc_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6611_: u8 = 0;
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6615_: u8 = 0;
    let mut v_isSharedCheck_6616_: u8 = 0;
    let mut v_unused_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6582_ = lean_usize_dec_lt(v_i_6573_, v_sz_6572_);
                if v___x_6582_ == 0 {
                    lean_dec(v_numParams_6570_);
                    lean_dec_ref(v_infos_6569_);
                    v___x_6583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6583_, 0, v_b_6574_);
                    return v___x_6583_;
                } else {
                    v_array_6584_ = lean_ctor_get(v_b_6574_, 0);
                    v_start_6585_ = lean_ctor_get(v_b_6574_, 1);
                    v_stop_6586_ = lean_ctor_get(v_b_6574_, 2);
                    v___x_6587_ = lean_nat_dec_lt(v_start_6585_, v_stop_6586_);
                    if v___x_6587_ == 0 {
                        lean_dec(v_numParams_6570_);
                        lean_dec_ref(v_infos_6569_);
                        v___x_6588_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6588_, 0, v_b_6574_);
                        return v___x_6588_;
                    } else {
                        lean_inc(v_stop_6586_);
                        lean_inc(v_start_6585_);
                        lean_inc_ref(v_array_6584_);
                        v_isSharedCheck_6616_ = (!lean_is_exclusive(v_b_6574_)) as u8;
                        if v_isSharedCheck_6616_ == 0 {
                            v_unused_6617_ = lean_ctor_get(v_b_6574_, 2);
                            lean_dec(v_unused_6617_);
                            v_unused_6618_ = lean_ctor_get(v_b_6574_, 1);
                            lean_dec(v_unused_6618_);
                            v_unused_6619_ = lean_ctor_get(v_b_6574_, 0);
                            lean_dec(v_unused_6619_);
                            v___x_6590_ = v_b_6574_;
                            v_isShared_6591_ = v_isSharedCheck_6616_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_b_6574_);
                            v___x_6590_ = lean_box(0);
                            v_isShared_6591_ = v_isSharedCheck_6616_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6592_ = lean_array_fget_borrowed(v_array_6584_, v_start_6585_);
                v_ctorSyntax_6593_ = lean_ctor_get(v___x_6592_, 4);
                v_a_6594_ = lean_array_uget_borrowed(v_as_6571_, v_i_6573_);
                v_ctors_6595_ = lean_ctor_get(v_a_6594_, 4);
                v___x_6596_ = lean_array_get_size(v_ctorSyntax_6593_);
                v___x_6597_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_ctorSyntax_6593_);
                v___x_6598_ =
                    l_Array_toSubarray___redArg(v_ctorSyntax_6593_, v___x_6597_, v___x_6596_);
                lean_inc(v_numParams_6570_);
                lean_inc_ref(v_infos_6569_);
                lean_inc(v_a_6594_);
                v___x_6599_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_6594_, v_infos_6569_, v_numParams_6570_, v_ctors_6595_, v___x_6598_, v___y_6575_, v___y_6576_, v___y_6577_, v___y_6578_, v___y_6579_, v___y_6580_);
                if lean_obj_tag(v___x_6599_) == 0 {
                    lean_dec_ref_known(v___x_6599_, 1);
                    v___x_6600_ = lean_unsigned_to_nat(1);
                    v___x_6601_ = lean_nat_add(v_start_6585_, v___x_6600_);
                    lean_dec(v_start_6585_);
                    if v_isShared_6591_ == 0 {
                        lean_ctor_set(v___x_6590_, 1, v___x_6601_);
                        v___x_6603_ = v___x_6590_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6607_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6607_, 0, v_array_6584_);
                        lean_ctor_set(v_reuseFailAlloc_6607_, 1, v___x_6601_);
                        lean_ctor_set(v_reuseFailAlloc_6607_, 2, v_stop_6586_);
                        v___x_6603_ = v_reuseFailAlloc_6607_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6590_);
                    lean_dec(v_stop_6586_);
                    lean_dec(v_start_6585_);
                    lean_dec_ref(v_array_6584_);
                    lean_dec(v_numParams_6570_);
                    lean_dec_ref(v_infos_6569_);
                    v_a_6608_ = lean_ctor_get(v___x_6599_, 0);
                    v_isSharedCheck_6615_ = (!lean_is_exclusive(v___x_6599_)) as u8;
                    if v_isSharedCheck_6615_ == 0 {
                        v___x_6610_ = v___x_6599_;
                        v_isShared_6611_ = v_isSharedCheck_6615_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6608_);
                        lean_dec(v___x_6599_);
                        v___x_6610_ = lean_box(0);
                        v_isShared_6611_ = v_isSharedCheck_6615_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6604_ = 1usize;
                v___x_6605_ = lean_usize_add(v_i_6573_, v___x_6604_);
                v_i_6573_ = v___x_6605_;
                v_b_6574_ = v___x_6603_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6611_ == 0 {
                    v___x_6613_ = v___x_6610_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6614_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6614_, 0, v_a_6608_);
                    v___x_6613_ = v_reuseFailAlloc_6614_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6613_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(
    mut v_infos_6620_: *mut LeanObject,
    mut v_numParams_6621_: *mut LeanObject,
    mut v_as_6622_: *mut LeanObject,
    mut v_sz_6623_: *mut LeanObject,
    mut v_i_6624_: *mut LeanObject,
    mut v_b_6625_: *mut LeanObject,
    mut v___y_6626_: *mut LeanObject,
    mut v___y_6627_: *mut LeanObject,
    mut v___y_6628_: *mut LeanObject,
    mut v___y_6629_: *mut LeanObject,
    mut v___y_6630_: *mut LeanObject,
    mut v___y_6631_: *mut LeanObject,
    mut v___y_6632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6633_: usize = 0;
    let mut v_i_boxed_6634_: usize = 0;
    let mut v_res_6635_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6633_ = lean_unbox_usize(v_sz_6623_);
    lean_dec(v_sz_6623_);
    v_i_boxed_6634_ = lean_unbox_usize(v_i_6624_);
    lean_dec(v_i_6624_);
    v_res_6635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_6620_, v_numParams_6621_, v_as_6622_, v_sz_boxed_6633_, v_i_boxed_6634_, v_b_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_);
    lean_dec(v___y_6631_);
    lean_dec_ref(v___y_6630_);
    lean_dec(v___y_6629_);
    lean_dec_ref(v___y_6628_);
    lean_dec(v___y_6627_);
    lean_dec_ref(v___y_6626_);
    lean_dec_ref(v_as_6622_);
    return v_res_6635_;
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(
    mut v_numParams_6636_: *mut LeanObject,
    mut v_infos_6637_: *mut LeanObject,
    mut v_coinductiveElabData_6638_: *mut LeanObject,
    mut v_a_6639_: *mut LeanObject,
    mut v_a_6640_: *mut LeanObject,
    mut v_a_6641_: *mut LeanObject,
    mut v_a_6642_: *mut LeanObject,
    mut v_a_6643_: *mut LeanObject,
    mut v_a_6644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6649_: usize = 0;
    let mut v___x_6650_: usize = 0;
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6654_: u8 = 0;
    let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6659_: u8 = 0;
    let mut v_unused_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6664_: u8 = 0;
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6646_ = lean_unsigned_to_nat(0);
                v___x_6647_ = lean_array_get_size(v_coinductiveElabData_6638_);
                v___x_6648_ = l_Array_toSubarray___redArg(
                    v_coinductiveElabData_6638_,
                    v___x_6646_,
                    v___x_6647_,
                );
                v_sz_6649_ = lean_array_size(v_infos_6637_);
                v___x_6650_ = 0usize;
                lean_inc_ref(v_infos_6637_);
                v___x_6651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_6637_, v_numParams_6636_, v_infos_6637_, v_sz_6649_, v___x_6650_, v___x_6648_, v_a_6639_, v_a_6640_, v_a_6641_, v_a_6642_, v_a_6643_, v_a_6644_);
                lean_dec_ref(v_infos_6637_);
                if lean_obj_tag(v___x_6651_) == 0 {
                    v_isSharedCheck_6659_ = (!lean_is_exclusive(v___x_6651_)) as u8;
                    if v_isSharedCheck_6659_ == 0 {
                        v_unused_6660_ = lean_ctor_get(v___x_6651_, 0);
                        lean_dec(v_unused_6660_);
                        v___x_6653_ = v___x_6651_;
                        v_isShared_6654_ = v_isSharedCheck_6659_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_6651_);
                        v___x_6653_ = lean_box(0);
                        v_isShared_6654_ = v_isSharedCheck_6659_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6661_ = lean_ctor_get(v___x_6651_, 0);
                    v_isSharedCheck_6668_ = (!lean_is_exclusive(v___x_6651_)) as u8;
                    if v_isSharedCheck_6668_ == 0 {
                        v___x_6663_ = v___x_6651_;
                        v_isShared_6664_ = v_isSharedCheck_6668_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6661_);
                        lean_dec(v___x_6651_);
                        v___x_6663_ = lean_box(0);
                        v_isShared_6664_ = v_isSharedCheck_6668_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6655_ = lean_box(0);
                if v_isShared_6654_ == 0 {
                    lean_ctor_set(v___x_6653_, 0, v___x_6655_);
                    v___x_6657_ = v___x_6653_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6658_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6658_, 0, v___x_6655_);
                    v___x_6657_ = v_reuseFailAlloc_6658_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6657_;
            }
            3 => {
                if v_isShared_6664_ == 0 {
                    v___x_6666_ = v___x_6663_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6667_, 0, v_a_6661_);
                    v___x_6666_ = v_reuseFailAlloc_6667_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(
    mut v_numParams_6669_: *mut LeanObject,
    mut v_infos_6670_: *mut LeanObject,
    mut v_coinductiveElabData_6671_: *mut LeanObject,
    mut v_a_6672_: *mut LeanObject,
    mut v_a_6673_: *mut LeanObject,
    mut v_a_6674_: *mut LeanObject,
    mut v_a_6675_: *mut LeanObject,
    mut v_a_6676_: *mut LeanObject,
    mut v_a_6677_: *mut LeanObject,
    mut v_a_6678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6679_: *mut LeanObject = core::ptr::null_mut();
    v_res_6679_ =
        l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(
            v_numParams_6669_,
            v_infos_6670_,
            v_coinductiveElabData_6671_,
            v_a_6672_,
            v_a_6673_,
            v_a_6674_,
            v_a_6675_,
            v_a_6676_,
            v_a_6677_,
        );
    lean_dec(v_a_6677_);
    lean_dec_ref(v_a_6676_);
    lean_dec(v_a_6675_);
    lean_dec_ref(v_a_6674_);
    lean_dec(v_a_6673_);
    lean_dec_ref(v_a_6672_);
    return v_res_6679_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(
    mut v_a_6680_: *mut LeanObject,
    mut v_infos_6681_: *mut LeanObject,
    mut v_numParams_6682_: *mut LeanObject,
    mut v_as_6683_: *mut LeanObject,
    mut v_as_x27_6684_: *mut LeanObject,
    mut v_b_6685_: *mut LeanObject,
    mut v_a_6686_: *mut LeanObject,
    mut v___y_6687_: *mut LeanObject,
    mut v___y_6688_: *mut LeanObject,
    mut v___y_6689_: *mut LeanObject,
    mut v___y_6690_: *mut LeanObject,
    mut v___y_6691_: *mut LeanObject,
    mut v___y_6692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    v___x_6694_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_6680_, v_infos_6681_, v_numParams_6682_, v_as_x27_6684_, v_b_6685_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_, v___y_6691_, v___y_6692_);
    return v___x_6694_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(
    mut v_a_6695_: *mut LeanObject,
    mut v_infos_6696_: *mut LeanObject,
    mut v_numParams_6697_: *mut LeanObject,
    mut v_as_6698_: *mut LeanObject,
    mut v_as_x27_6699_: *mut LeanObject,
    mut v_b_6700_: *mut LeanObject,
    mut v_a_6701_: *mut LeanObject,
    mut v___y_6702_: *mut LeanObject,
    mut v___y_6703_: *mut LeanObject,
    mut v___y_6704_: *mut LeanObject,
    mut v___y_6705_: *mut LeanObject,
    mut v___y_6706_: *mut LeanObject,
    mut v___y_6707_: *mut LeanObject,
    mut v___y_6708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6709_: *mut LeanObject = core::ptr::null_mut();
    v_res_6709_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_6695_, v_infos_6696_, v_numParams_6697_, v_as_6698_, v_as_x27_6699_, v_b_6700_, v_a_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_);
    lean_dec(v___y_6707_);
    lean_dec_ref(v___y_6706_);
    lean_dec(v___y_6705_);
    lean_dec_ref(v___y_6704_);
    lean_dec(v___y_6703_);
    lean_dec_ref(v___y_6702_);
    lean_dec(v_as_x27_6699_);
    lean_dec(v_as_6698_);
    return v_res_6709_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(
    mut v_00_u03b1_6710_: *mut LeanObject,
    mut v_msg_6711_: *mut LeanObject,
    mut v___y_6712_: *mut LeanObject,
    mut v___y_6713_: *mut LeanObject,
    mut v___y_6714_: *mut LeanObject,
    mut v___y_6715_: *mut LeanObject,
    mut v___y_6716_: *mut LeanObject,
    mut v___y_6717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    v___x_6719_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_6711_, v___y_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_, v___y_6717_);
    return v___x_6719_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(
    mut v_00_u03b1_6720_: *mut LeanObject,
    mut v_msg_6721_: *mut LeanObject,
    mut v___y_6722_: *mut LeanObject,
    mut v___y_6723_: *mut LeanObject,
    mut v___y_6724_: *mut LeanObject,
    mut v___y_6725_: *mut LeanObject,
    mut v___y_6726_: *mut LeanObject,
    mut v___y_6727_: *mut LeanObject,
    mut v___y_6728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6729_: *mut LeanObject = core::ptr::null_mut();
    v_res_6729_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(v_00_u03b1_6720_, v_msg_6721_, v___y_6722_, v___y_6723_, v___y_6724_, v___y_6725_, v___y_6726_, v___y_6727_);
    lean_dec(v___y_6727_);
    lean_dec_ref(v___y_6726_);
    lean_dec(v___y_6725_);
    lean_dec_ref(v___y_6724_);
    lean_dec(v___y_6723_);
    lean_dec_ref(v___y_6722_);
    return v_res_6729_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(
    mut v_msgData_6730_: *mut LeanObject,
    mut v_macroStack_6731_: *mut LeanObject,
    mut v___y_6732_: *mut LeanObject,
    mut v___y_6733_: *mut LeanObject,
    mut v___y_6734_: *mut LeanObject,
    mut v___y_6735_: *mut LeanObject,
    mut v___y_6736_: *mut LeanObject,
    mut v___y_6737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    v___x_6739_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_6730_, v_macroStack_6731_, v___y_6736_);
    return v___x_6739_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_6740_: *mut LeanObject,
    mut v_macroStack_6741_: *mut LeanObject,
    mut v___y_6742_: *mut LeanObject,
    mut v___y_6743_: *mut LeanObject,
    mut v___y_6744_: *mut LeanObject,
    mut v___y_6745_: *mut LeanObject,
    mut v___y_6746_: *mut LeanObject,
    mut v___y_6747_: *mut LeanObject,
    mut v___y_6748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6749_: *mut LeanObject = core::ptr::null_mut();
    v_res_6749_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_6740_, v_macroStack_6741_, v___y_6742_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_, v___y_6747_);
    lean_dec(v___y_6747_);
    lean_dec_ref(v___y_6746_);
    lean_dec(v___y_6745_);
    lean_dec_ref(v___y_6744_);
    lean_dec(v___y_6743_);
    lean_dec_ref(v___y_6742_);
    return v_res_6749_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(
    mut v_mvarId_6750_: *mut LeanObject,
    mut v_x_6751_: *mut LeanObject,
    mut v___y_6752_: *mut LeanObject,
    mut v___y_6753_: *mut LeanObject,
    mut v___y_6754_: *mut LeanObject,
    mut v___y_6755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6761_: u8 = 0;
    let mut v___x_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6765_: u8 = 0;
    let mut v_a_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6769_: u8 = 0;
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6757_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_6750_,
                    v_x_6751_,
                    v___y_6752_,
                    v___y_6753_,
                    v___y_6754_,
                    v___y_6755_,
                );
                if lean_obj_tag(v___x_6757_) == 0 {
                    v_a_6758_ = lean_ctor_get(v___x_6757_, 0);
                    v_isSharedCheck_6765_ = (!lean_is_exclusive(v___x_6757_)) as u8;
                    if v_isSharedCheck_6765_ == 0 {
                        v___x_6760_ = v___x_6757_;
                        v_isShared_6761_ = v_isSharedCheck_6765_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6758_);
                        lean_dec(v___x_6757_);
                        v___x_6760_ = lean_box(0);
                        v_isShared_6761_ = v_isSharedCheck_6765_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6766_ = lean_ctor_get(v___x_6757_, 0);
                    v_isSharedCheck_6773_ = (!lean_is_exclusive(v___x_6757_)) as u8;
                    if v_isSharedCheck_6773_ == 0 {
                        v___x_6768_ = v___x_6757_;
                        v_isShared_6769_ = v_isSharedCheck_6773_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6766_);
                        lean_dec(v___x_6757_);
                        v___x_6768_ = lean_box(0);
                        v_isShared_6769_ = v_isSharedCheck_6773_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6761_ == 0 {
                    v___x_6763_ = v___x_6760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6764_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6764_, 0, v_a_6758_);
                    v___x_6763_ = v_reuseFailAlloc_6764_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6763_;
            }
            3 => {
                if v_isShared_6769_ == 0 {
                    v___x_6771_ = v___x_6768_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6772_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6772_, 0, v_a_6766_);
                    v___x_6771_ = v_reuseFailAlloc_6772_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(
    mut v_mvarId_6774_: *mut LeanObject,
    mut v_x_6775_: *mut LeanObject,
    mut v___y_6776_: *mut LeanObject,
    mut v___y_6777_: *mut LeanObject,
    mut v___y_6778_: *mut LeanObject,
    mut v___y_6779_: *mut LeanObject,
    mut v___y_6780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6781_: *mut LeanObject = core::ptr::null_mut();
    v_res_6781_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_6774_, v_x_6775_, v___y_6776_, v___y_6777_, v___y_6778_, v___y_6779_);
    lean_dec(v___y_6779_);
    lean_dec_ref(v___y_6778_);
    lean_dec(v___y_6777_);
    lean_dec_ref(v___y_6776_);
    return v_res_6781_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(
    mut v_00_u03b1_6782_: *mut LeanObject,
    mut v_mvarId_6783_: *mut LeanObject,
    mut v_x_6784_: *mut LeanObject,
    mut v___y_6785_: *mut LeanObject,
    mut v___y_6786_: *mut LeanObject,
    mut v___y_6787_: *mut LeanObject,
    mut v___y_6788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    v___x_6790_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_6783_, v_x_6784_, v___y_6785_, v___y_6786_, v___y_6787_, v___y_6788_);
    return v___x_6790_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(
    mut v_00_u03b1_6791_: *mut LeanObject,
    mut v_mvarId_6792_: *mut LeanObject,
    mut v_x_6793_: *mut LeanObject,
    mut v___y_6794_: *mut LeanObject,
    mut v___y_6795_: *mut LeanObject,
    mut v___y_6796_: *mut LeanObject,
    mut v___y_6797_: *mut LeanObject,
    mut v___y_6798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6799_: *mut LeanObject = core::ptr::null_mut();
    v_res_6799_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(v_00_u03b1_6791_, v_mvarId_6792_, v_x_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_);
    lean_dec(v___y_6797_);
    lean_dec_ref(v___y_6796_);
    lean_dec(v___y_6795_);
    lean_dec_ref(v___y_6794_);
    return v_res_6799_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(
    mut v_type_6800_: *mut LeanObject,
    mut v_maxFVars_x3f_6801_: *mut LeanObject,
    mut v_k_6802_: *mut LeanObject,
    mut v_cleanupAnnotations_6803_: u8,
    mut v_whnfType_6804_: u8,
    mut v___y_6805_: *mut LeanObject,
    mut v___y_6806_: *mut LeanObject,
    mut v___y_6807_: *mut LeanObject,
    mut v___y_6808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6815_: u8 = 0;
    let mut v___x_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6819_: u8 = 0;
    let mut v_a_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6823_: u8 = 0;
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6810_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_6810_, 0, v_k_6802_);
                v___x_6811_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_6800_,
                    v_maxFVars_x3f_6801_,
                    v___f_6810_,
                    v_cleanupAnnotations_6803_,
                    v_whnfType_6804_,
                    v___y_6805_,
                    v___y_6806_,
                    v___y_6807_,
                    v___y_6808_,
                );
                if lean_obj_tag(v___x_6811_) == 0 {
                    v_a_6812_ = lean_ctor_get(v___x_6811_, 0);
                    v_isSharedCheck_6819_ = (!lean_is_exclusive(v___x_6811_)) as u8;
                    if v_isSharedCheck_6819_ == 0 {
                        v___x_6814_ = v___x_6811_;
                        v_isShared_6815_ = v_isSharedCheck_6819_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6812_);
                        lean_dec(v___x_6811_);
                        v___x_6814_ = lean_box(0);
                        v_isShared_6815_ = v_isSharedCheck_6819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6820_ = lean_ctor_get(v___x_6811_, 0);
                    v_isSharedCheck_6827_ = (!lean_is_exclusive(v___x_6811_)) as u8;
                    if v_isSharedCheck_6827_ == 0 {
                        v___x_6822_ = v___x_6811_;
                        v_isShared_6823_ = v_isSharedCheck_6827_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6820_);
                        lean_dec(v___x_6811_);
                        v___x_6822_ = lean_box(0);
                        v_isShared_6823_ = v_isSharedCheck_6827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6815_ == 0 {
                    v___x_6817_ = v___x_6814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6818_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6818_, 0, v_a_6812_);
                    v___x_6817_ = v_reuseFailAlloc_6818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6817_;
            }
            3 => {
                if v_isShared_6823_ == 0 {
                    v___x_6825_ = v___x_6822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6826_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6826_, 0, v_a_6820_);
                    v___x_6825_ = v_reuseFailAlloc_6826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(
    mut v_type_6828_: *mut LeanObject,
    mut v_maxFVars_x3f_6829_: *mut LeanObject,
    mut v_k_6830_: *mut LeanObject,
    mut v_cleanupAnnotations_6831_: *mut LeanObject,
    mut v_whnfType_6832_: *mut LeanObject,
    mut v___y_6833_: *mut LeanObject,
    mut v___y_6834_: *mut LeanObject,
    mut v___y_6835_: *mut LeanObject,
    mut v___y_6836_: *mut LeanObject,
    mut v___y_6837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_6838_: u8 = 0;
    let mut v_whnfType_boxed_6839_: u8 = 0;
    let mut v_res_6840_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6838_ = (lean_unbox(v_cleanupAnnotations_6831_) as u8);
    v_whnfType_boxed_6839_ = (lean_unbox(v_whnfType_6832_) as u8);
    v_res_6840_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_6828_, v_maxFVars_x3f_6829_, v_k_6830_, v_cleanupAnnotations_boxed_6838_, v_whnfType_boxed_6839_, v___y_6833_, v___y_6834_, v___y_6835_, v___y_6836_);
    lean_dec(v___y_6836_);
    lean_dec_ref(v___y_6835_);
    lean_dec(v___y_6834_);
    lean_dec_ref(v___y_6833_);
    return v_res_6840_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(
    mut v_00_u03b1_6841_: *mut LeanObject,
    mut v_type_6842_: *mut LeanObject,
    mut v_maxFVars_x3f_6843_: *mut LeanObject,
    mut v_k_6844_: *mut LeanObject,
    mut v_cleanupAnnotations_6845_: u8,
    mut v_whnfType_6846_: u8,
    mut v___y_6847_: *mut LeanObject,
    mut v___y_6848_: *mut LeanObject,
    mut v___y_6849_: *mut LeanObject,
    mut v___y_6850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    v___x_6852_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_6842_, v_maxFVars_x3f_6843_, v_k_6844_, v_cleanupAnnotations_6845_, v_whnfType_6846_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_);
    return v___x_6852_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(
    mut v_00_u03b1_6853_: *mut LeanObject,
    mut v_type_6854_: *mut LeanObject,
    mut v_maxFVars_x3f_6855_: *mut LeanObject,
    mut v_k_6856_: *mut LeanObject,
    mut v_cleanupAnnotations_6857_: *mut LeanObject,
    mut v_whnfType_6858_: *mut LeanObject,
    mut v___y_6859_: *mut LeanObject,
    mut v___y_6860_: *mut LeanObject,
    mut v___y_6861_: *mut LeanObject,
    mut v___y_6862_: *mut LeanObject,
    mut v___y_6863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_6864_: u8 = 0;
    let mut v_whnfType_boxed_6865_: u8 = 0;
    let mut v_res_6866_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6864_ = (lean_unbox(v_cleanupAnnotations_6857_) as u8);
    v_whnfType_boxed_6865_ = (lean_unbox(v_whnfType_6858_) as u8);
    v_res_6866_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(v_00_u03b1_6853_, v_type_6854_, v_maxFVars_x3f_6855_, v_k_6856_, v_cleanupAnnotations_boxed_6864_, v_whnfType_boxed_6865_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_);
    lean_dec(v___y_6862_);
    lean_dec_ref(v___y_6861_);
    lean_dec(v___y_6860_);
    lean_dec_ref(v___y_6859_);
    return v_res_6866_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(
    mut v_ref_6867_: *mut LeanObject,
    mut v_msg_6868_: *mut LeanObject,
    mut v___y_6869_: *mut LeanObject,
    mut v___y_6870_: *mut LeanObject,
    mut v___y_6871_: *mut LeanObject,
    mut v___y_6872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6886_: u8 = 0;
    let mut v_cancelTk_x3f_6887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6888_: u8 = 0;
    let mut v_inheritedTraceOptions_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_6874_ = lean_ctor_get(v___y_6871_, 0);
    v_fileMap_6875_ = lean_ctor_get(v___y_6871_, 1);
    v_options_6876_ = lean_ctor_get(v___y_6871_, 2);
    v_currRecDepth_6877_ = lean_ctor_get(v___y_6871_, 3);
    v_maxRecDepth_6878_ = lean_ctor_get(v___y_6871_, 4);
    v_ref_6879_ = lean_ctor_get(v___y_6871_, 5);
    v_currNamespace_6880_ = lean_ctor_get(v___y_6871_, 6);
    v_openDecls_6881_ = lean_ctor_get(v___y_6871_, 7);
    v_initHeartbeats_6882_ = lean_ctor_get(v___y_6871_, 8);
    v_maxHeartbeats_6883_ = lean_ctor_get(v___y_6871_, 9);
    v_quotContext_6884_ = lean_ctor_get(v___y_6871_, 10);
    v_currMacroScope_6885_ = lean_ctor_get(v___y_6871_, 11);
    v_diag_6886_ = lean_ctor_get_uint8(
        v___y_6871_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_6887_ = lean_ctor_get(v___y_6871_, 12);
    v_suppressElabErrors_6888_ = lean_ctor_get_uint8(
        v___y_6871_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_6889_ = lean_ctor_get(v___y_6871_, 13);
    v_ref_6890_ = l_Lean_replaceRef(v_ref_6867_, v_ref_6879_);
    lean_inc_ref(v_inheritedTraceOptions_6889_);
    lean_inc(v_cancelTk_x3f_6887_);
    lean_inc(v_currMacroScope_6885_);
    lean_inc(v_quotContext_6884_);
    lean_inc(v_maxHeartbeats_6883_);
    lean_inc(v_initHeartbeats_6882_);
    lean_inc(v_openDecls_6881_);
    lean_inc(v_currNamespace_6880_);
    lean_inc(v_maxRecDepth_6878_);
    lean_inc(v_currRecDepth_6877_);
    lean_inc_ref(v_options_6876_);
    lean_inc_ref(v_fileMap_6875_);
    lean_inc_ref(v_fileName_6874_);
    v___x_6891_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_6891_, 0, v_fileName_6874_);
    lean_ctor_set(v___x_6891_, 1, v_fileMap_6875_);
    lean_ctor_set(v___x_6891_, 2, v_options_6876_);
    lean_ctor_set(v___x_6891_, 3, v_currRecDepth_6877_);
    lean_ctor_set(v___x_6891_, 4, v_maxRecDepth_6878_);
    lean_ctor_set(v___x_6891_, 5, v_ref_6890_);
    lean_ctor_set(v___x_6891_, 6, v_currNamespace_6880_);
    lean_ctor_set(v___x_6891_, 7, v_openDecls_6881_);
    lean_ctor_set(v___x_6891_, 8, v_initHeartbeats_6882_);
    lean_ctor_set(v___x_6891_, 9, v_maxHeartbeats_6883_);
    lean_ctor_set(v___x_6891_, 10, v_quotContext_6884_);
    lean_ctor_set(v___x_6891_, 11, v_currMacroScope_6885_);
    lean_ctor_set(v___x_6891_, 12, v_cancelTk_x3f_6887_);
    lean_ctor_set(v___x_6891_, 13, v_inheritedTraceOptions_6889_);
    lean_ctor_set_uint8(
        v___x_6891_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_6886_,
    );
    lean_ctor_set_uint8(
        v___x_6891_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_6888_,
    );
    v___x_6892_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_6868_, v___y_6869_, v___y_6870_, v___x_6891_, v___y_6872_);
    lean_dec_ref_known(v___x_6891_, 14);
    return v___x_6892_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(
    mut v_ref_6893_: *mut LeanObject,
    mut v_msg_6894_: *mut LeanObject,
    mut v___y_6895_: *mut LeanObject,
    mut v___y_6896_: *mut LeanObject,
    mut v___y_6897_: *mut LeanObject,
    mut v___y_6898_: *mut LeanObject,
    mut v___y_6899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6900_: *mut LeanObject = core::ptr::null_mut();
    v_res_6900_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_6893_, v_msg_6894_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_);
    lean_dec(v___y_6898_);
    lean_dec_ref(v___y_6897_);
    lean_dec(v___y_6896_);
    lean_dec_ref(v___y_6895_);
    lean_dec(v_ref_6893_);
    return v_res_6900_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6901_: *mut LeanObject = core::ptr::null_mut();
    v___x_6901_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6901_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut LeanObject = core::ptr::null_mut();
    v___x_6902_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
    v___x_6903_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6903_, 0, v___x_6902_);
    return v___x_6903_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    v___x_6904_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
    v___x_6905_ = lean_unsigned_to_nat(0);
    v___x_6906_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_6906_, 0, v___x_6905_);
    lean_ctor_set(v___x_6906_, 1, v___x_6905_);
    lean_ctor_set(v___x_6906_, 2, v___x_6905_);
    lean_ctor_set(v___x_6906_, 3, v___x_6905_);
    lean_ctor_set(v___x_6906_, 4, v___x_6904_);
    lean_ctor_set(v___x_6906_, 5, v___x_6904_);
    lean_ctor_set(v___x_6906_, 6, v___x_6904_);
    lean_ctor_set(v___x_6906_, 7, v___x_6904_);
    lean_ctor_set(v___x_6906_, 8, v___x_6904_);
    lean_ctor_set(v___x_6906_, 9, v___x_6904_);
    return v___x_6906_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    v___x_6907_ = lean_unsigned_to_nat(32);
    v___x_6908_ = lean_mk_empty_array_with_capacity(v___x_6907_);
    v___x_6909_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6909_, 0, v___x_6908_);
    return v___x_6909_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_6910_: usize = 0;
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    v___x_6910_ = 5usize;
    v___x_6911_ = lean_unsigned_to_nat(0);
    v___x_6912_ = lean_unsigned_to_nat(32);
    v___x_6913_ = lean_mk_empty_array_with_capacity(v___x_6912_);
    v___x_6914_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
    v___x_6915_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6915_, 0, v___x_6914_);
    lean_ctor_set(v___x_6915_, 1, v___x_6913_);
    lean_ctor_set(v___x_6915_, 2, v___x_6911_);
    lean_ctor_set(v___x_6915_, 3, v___x_6911_);
    lean_ctor_set_usize(v___x_6915_, 4, v___x_6910_);
    return v___x_6915_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_6916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
    v___x_6916_ = lean_box(1);
    v___x_6917_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
    v___x_6918_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
    v___x_6919_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6919_, 0, v___x_6918_);
    lean_ctor_set(v___x_6919_, 1, v___x_6917_);
    lean_ctor_set(v___x_6919_, 2, v___x_6916_);
    return v___x_6919_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut LeanObject = core::ptr::null_mut();
    v___x_6921_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6;
    v___x_6922_ = l_Lean_stringToMessageData(v___x_6921_);
    return v___x_6922_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut LeanObject = core::ptr::null_mut();
    v___x_6924_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8;
    v___x_6925_ = l_Lean_stringToMessageData(v___x_6924_);
    return v___x_6925_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    v___x_6927_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10;
    v___x_6928_ = l_Lean_stringToMessageData(v___x_6927_);
    return v___x_6928_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    v___x_6930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12;
    v___x_6931_ = l_Lean_stringToMessageData(v___x_6930_);
    return v___x_6931_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut LeanObject = core::ptr::null_mut();
    v___x_6933_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14;
    v___x_6934_ = l_Lean_stringToMessageData(v___x_6933_);
    return v___x_6934_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut LeanObject = core::ptr::null_mut();
    v___x_6936_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16;
    v___x_6937_ = l_Lean_stringToMessageData(v___x_6936_);
    return v___x_6937_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut LeanObject = core::ptr::null_mut();
    v___x_6939_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18;
    v___x_6940_ = l_Lean_stringToMessageData(v___x_6939_);
    return v___x_6940_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(
    mut v_msg_6941_: *mut LeanObject,
    mut v_declHint_6942_: *mut LeanObject,
    mut v___y_6943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: u8 = 0;
    let mut v_isExporting_6948_: u8 = 0;
    let mut v___x_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: u8 = 0;
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6970_: u8 = 0;
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: u8 = 0;
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7002_: u8 = 0;
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6945_ = lean_st_ref_get(v___y_6943_);
                v_env_6946_ = lean_ctor_get(v___x_6945_, 0);
                lean_inc_ref(v_env_6946_);
                lean_dec(v___x_6945_);
                v___x_6947_ = l_Lean_Name_isAnonymous(v_declHint_6942_);
                if v___x_6947_ == 0 {
                    v_isExporting_6948_ = lean_ctor_get_uint8(
                        v_env_6946_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_6948_ == 0 {
                        lean_dec_ref(v_env_6946_);
                        lean_dec(v_declHint_6942_);
                        v___x_6949_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6949_, 0, v_msg_6941_);
                        return v___x_6949_;
                    } else {
                        lean_inc_ref(v_env_6946_);
                        v___x_6950_ = l_Lean_Environment_setExporting(v_env_6946_, v___x_6947_);
                        lean_inc(v_declHint_6942_);
                        lean_inc_ref(v___x_6950_);
                        v___x_6951_ = l_Lean_Environment_contains(
                            v___x_6950_,
                            v_declHint_6942_,
                            v_isExporting_6948_,
                        );
                        if v___x_6951_ == 0 {
                            lean_dec_ref(v___x_6950_);
                            lean_dec_ref(v_env_6946_);
                            lean_dec(v_declHint_6942_);
                            v___x_6952_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_6952_, 0, v_msg_6941_);
                            return v___x_6952_;
                        } else {
                            v___x_6953_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2);
                            v___x_6954_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5);
                            v___x_6955_ = l_Lean_Options_empty;
                            v___x_6956_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_6956_, 0, v___x_6950_);
                            lean_ctor_set(v___x_6956_, 1, v___x_6953_);
                            lean_ctor_set(v___x_6956_, 2, v___x_6954_);
                            lean_ctor_set(v___x_6956_, 3, v___x_6955_);
                            lean_inc(v_declHint_6942_);
                            v___x_6957_ =
                                l_Lean_MessageData_ofConstName(v_declHint_6942_, v___x_6947_);
                            v_c_6958_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_6958_, 0, v___x_6956_);
                            lean_ctor_set(v_c_6958_, 1, v___x_6957_);
                            v___x_6959_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_6946_,
                                v_declHint_6942_,
                            );
                            if lean_obj_tag(v___x_6959_) == 0 {
                                lean_dec_ref(v_env_6946_);
                                lean_dec(v_declHint_6942_);
                                v___x_6960_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
                                v___x_6961_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6961_, 0, v___x_6960_);
                                lean_ctor_set(v___x_6961_, 1, v_c_6958_);
                                v___x_6962_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9);
                                v___x_6963_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6963_, 0, v___x_6961_);
                                lean_ctor_set(v___x_6963_, 1, v___x_6962_);
                                v___x_6964_ = l_Lean_MessageData_note(v___x_6963_);
                                v___x_6965_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6965_, 0, v_msg_6941_);
                                lean_ctor_set(v___x_6965_, 1, v___x_6964_);
                                v___x_6966_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_6966_, 0, v___x_6965_);
                                return v___x_6966_;
                            } else {
                                v_val_6967_ = lean_ctor_get(v___x_6959_, 0);
                                v_isSharedCheck_7002_ = (!lean_is_exclusive(v___x_6959_)) as u8;
                                if v_isSharedCheck_7002_ == 0 {
                                    v___x_6969_ = v___x_6959_;
                                    v_isShared_6970_ = v_isSharedCheck_7002_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_6967_);
                                    lean_dec(v___x_6959_);
                                    v___x_6969_ = lean_box(0);
                                    v_isShared_6970_ = v_isSharedCheck_7002_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_6946_);
                    lean_dec(v_declHint_6942_);
                    v___x_7003_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7003_, 0, v_msg_6941_);
                    return v___x_7003_;
                }
            }
            1 => {
                v___x_6971_ = lean_box(0);
                v___x_6972_ = l_Lean_Environment_header(v_env_6946_);
                lean_dec_ref(v_env_6946_);
                v___x_6973_ = l_Lean_EnvironmentHeader_moduleNames(v___x_6972_);
                v_mod_6974_ = lean_array_get(v___x_6971_, v___x_6973_, v_val_6967_);
                lean_dec(v_val_6967_);
                lean_dec_ref(v___x_6973_);
                v___x_6975_ = l_Lean_isPrivateName(v_declHint_6942_);
                lean_dec(v_declHint_6942_);
                if v___x_6975_ == 0 {
                    v___x_6976_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11);
                    v___x_6977_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6977_, 0, v___x_6976_);
                    lean_ctor_set(v___x_6977_, 1, v_c_6958_);
                    v___x_6978_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13);
                    v___x_6979_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6979_, 0, v___x_6977_);
                    lean_ctor_set(v___x_6979_, 1, v___x_6978_);
                    v___x_6980_ = l_Lean_MessageData_ofName(v_mod_6974_);
                    v___x_6981_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6981_, 0, v___x_6979_);
                    lean_ctor_set(v___x_6981_, 1, v___x_6980_);
                    v___x_6982_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15);
                    v___x_6983_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6983_, 0, v___x_6981_);
                    lean_ctor_set(v___x_6983_, 1, v___x_6982_);
                    v___x_6984_ = l_Lean_MessageData_note(v___x_6983_);
                    v___x_6985_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6985_, 0, v_msg_6941_);
                    lean_ctor_set(v___x_6985_, 1, v___x_6984_);
                    if v_isShared_6970_ == 0 {
                        lean_ctor_set_tag(v___x_6969_, 0);
                        lean_ctor_set(v___x_6969_, 0, v___x_6985_);
                        v___x_6987_ = v___x_6969_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6988_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6988_, 0, v___x_6985_);
                        v___x_6987_ = v_reuseFailAlloc_6988_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6989_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
                    v___x_6990_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6990_, 0, v___x_6989_);
                    lean_ctor_set(v___x_6990_, 1, v_c_6958_);
                    v___x_6991_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17);
                    v___x_6992_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6992_, 0, v___x_6990_);
                    lean_ctor_set(v___x_6992_, 1, v___x_6991_);
                    v___x_6993_ = l_Lean_MessageData_ofName(v_mod_6974_);
                    v___x_6994_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6994_, 0, v___x_6992_);
                    lean_ctor_set(v___x_6994_, 1, v___x_6993_);
                    v___x_6995_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19);
                    v___x_6996_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6996_, 0, v___x_6994_);
                    lean_ctor_set(v___x_6996_, 1, v___x_6995_);
                    v___x_6997_ = l_Lean_MessageData_note(v___x_6996_);
                    v___x_6998_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6998_, 0, v_msg_6941_);
                    lean_ctor_set(v___x_6998_, 1, v___x_6997_);
                    if v_isShared_6970_ == 0 {
                        lean_ctor_set_tag(v___x_6969_, 0);
                        lean_ctor_set(v___x_6969_, 0, v___x_6998_);
                        v___x_7000_ = v___x_6969_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7001_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7001_, 0, v___x_6998_);
                        v___x_7000_ = v_reuseFailAlloc_7001_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6987_;
            }
            3 => {
                return v___x_7000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(
    mut v_msg_7004_: *mut LeanObject,
    mut v_declHint_7005_: *mut LeanObject,
    mut v___y_7006_: *mut LeanObject,
    mut v___y_7007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7008_: *mut LeanObject = core::ptr::null_mut();
    v_res_7008_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_7004_, v_declHint_7005_, v___y_7006_);
    lean_dec(v___y_7006_);
    return v_res_7008_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(
    mut v_msg_7009_: *mut LeanObject,
    mut v_declHint_7010_: *mut LeanObject,
    mut v___y_7011_: *mut LeanObject,
    mut v___y_7012_: *mut LeanObject,
    mut v___y_7013_: *mut LeanObject,
    mut v___y_7014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7020_: u8 = 0;
    let mut v___x_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7016_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_7009_, v_declHint_7010_, v___y_7014_);
                v_a_7017_ = lean_ctor_get(v___x_7016_, 0);
                v_isSharedCheck_7026_ = (!lean_is_exclusive(v___x_7016_)) as u8;
                if v_isSharedCheck_7026_ == 0 {
                    v___x_7019_ = v___x_7016_;
                    v_isShared_7020_ = v_isSharedCheck_7026_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7017_);
                    lean_dec(v___x_7016_);
                    v___x_7019_ = lean_box(0);
                    v_isShared_7020_ = v_isSharedCheck_7026_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7021_ = l_Lean_unknownIdentifierMessageTag;
                v___x_7022_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_7022_, 0, v___x_7021_);
                lean_ctor_set(v___x_7022_, 1, v_a_7017_);
                if v_isShared_7020_ == 0 {
                    lean_ctor_set(v___x_7019_, 0, v___x_7022_);
                    v___x_7024_ = v___x_7019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7025_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7025_, 0, v___x_7022_);
                    v___x_7024_ = v_reuseFailAlloc_7025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(
    mut v_msg_7027_: *mut LeanObject,
    mut v_declHint_7028_: *mut LeanObject,
    mut v___y_7029_: *mut LeanObject,
    mut v___y_7030_: *mut LeanObject,
    mut v___y_7031_: *mut LeanObject,
    mut v___y_7032_: *mut LeanObject,
    mut v___y_7033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7034_: *mut LeanObject = core::ptr::null_mut();
    v_res_7034_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_7027_, v_declHint_7028_, v___y_7029_, v___y_7030_, v___y_7031_, v___y_7032_);
    lean_dec(v___y_7032_);
    lean_dec_ref(v___y_7031_);
    lean_dec(v___y_7030_);
    lean_dec_ref(v___y_7029_);
    return v_res_7034_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(
    mut v_ref_7035_: *mut LeanObject,
    mut v_msg_7036_: *mut LeanObject,
    mut v_declHint_7037_: *mut LeanObject,
    mut v___y_7038_: *mut LeanObject,
    mut v___y_7039_: *mut LeanObject,
    mut v___y_7040_: *mut LeanObject,
    mut v___y_7041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    v___x_7043_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_7036_, v_declHint_7037_, v___y_7038_, v___y_7039_, v___y_7040_, v___y_7041_);
    v_a_7044_ = lean_ctor_get(v___x_7043_, 0);
    lean_inc(v_a_7044_);
    lean_dec_ref(v___x_7043_);
    v___x_7045_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_7035_, v_a_7044_, v___y_7038_, v___y_7039_, v___y_7040_, v___y_7041_);
    return v___x_7045_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(
    mut v_ref_7046_: *mut LeanObject,
    mut v_msg_7047_: *mut LeanObject,
    mut v_declHint_7048_: *mut LeanObject,
    mut v___y_7049_: *mut LeanObject,
    mut v___y_7050_: *mut LeanObject,
    mut v___y_7051_: *mut LeanObject,
    mut v___y_7052_: *mut LeanObject,
    mut v___y_7053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7054_: *mut LeanObject = core::ptr::null_mut();
    v_res_7054_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_7046_, v_msg_7047_, v_declHint_7048_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_);
    lean_dec(v___y_7052_);
    lean_dec_ref(v___y_7051_);
    lean_dec(v___y_7050_);
    lean_dec_ref(v___y_7049_);
    lean_dec(v_ref_7046_);
    return v_res_7054_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut LeanObject = core::ptr::null_mut();
    v___x_7056_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0;
    v___x_7057_ = l_Lean_stringToMessageData(v___x_7056_);
    return v___x_7057_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(
    mut v_ref_7058_: *mut LeanObject,
    mut v_constName_7059_: *mut LeanObject,
    mut v___y_7060_: *mut LeanObject,
    mut v___y_7061_: *mut LeanObject,
    mut v___y_7062_: *mut LeanObject,
    mut v___y_7063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: u8 = 0;
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    v___x_7065_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
    v___x_7066_ = 0;
    lean_inc(v_constName_7059_);
    v___x_7067_ = l_Lean_MessageData_ofConstName(v_constName_7059_, v___x_7066_);
    v___x_7068_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7068_, 0, v___x_7065_);
    lean_ctor_set(v___x_7068_, 1, v___x_7067_);
    v___x_7069_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
    v___x_7070_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7070_, 0, v___x_7068_);
    lean_ctor_set(v___x_7070_, 1, v___x_7069_);
    v___x_7071_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_7058_, v___x_7070_, v_constName_7059_, v___y_7060_, v___y_7061_, v___y_7062_, v___y_7063_);
    return v___x_7071_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(
    mut v_ref_7072_: *mut LeanObject,
    mut v_constName_7073_: *mut LeanObject,
    mut v___y_7074_: *mut LeanObject,
    mut v___y_7075_: *mut LeanObject,
    mut v___y_7076_: *mut LeanObject,
    mut v___y_7077_: *mut LeanObject,
    mut v___y_7078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7079_: *mut LeanObject = core::ptr::null_mut();
    v_res_7079_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_7072_, v_constName_7073_, v___y_7074_, v___y_7075_, v___y_7076_, v___y_7077_);
    lean_dec(v___y_7077_);
    lean_dec_ref(v___y_7076_);
    lean_dec(v___y_7075_);
    lean_dec_ref(v___y_7074_);
    lean_dec(v_ref_7072_);
    return v_res_7079_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(
    mut v_constName_7080_: *mut LeanObject,
    mut v___y_7081_: *mut LeanObject,
    mut v___y_7082_: *mut LeanObject,
    mut v___y_7083_: *mut LeanObject,
    mut v___y_7084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    v_ref_7086_ = lean_ctor_get(v___y_7083_, 5);
    v___x_7087_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_7086_, v_constName_7080_, v___y_7081_, v___y_7082_, v___y_7083_, v___y_7084_);
    return v___x_7087_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(
    mut v_constName_7088_: *mut LeanObject,
    mut v___y_7089_: *mut LeanObject,
    mut v___y_7090_: *mut LeanObject,
    mut v___y_7091_: *mut LeanObject,
    mut v___y_7092_: *mut LeanObject,
    mut v___y_7093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7094_: *mut LeanObject = core::ptr::null_mut();
    v_res_7094_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_7088_, v___y_7089_, v___y_7090_, v___y_7091_, v___y_7092_);
    lean_dec(v___y_7092_);
    lean_dec_ref(v___y_7091_);
    lean_dec(v___y_7090_);
    lean_dec_ref(v___y_7089_);
    return v_res_7094_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(
    mut v_constName_7095_: *mut LeanObject,
    mut v___y_7096_: *mut LeanObject,
    mut v___y_7097_: *mut LeanObject,
    mut v___y_7098_: *mut LeanObject,
    mut v___y_7099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: u8 = 0;
    let mut v___x_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7109_: u8 = 0;
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7101_ = lean_st_ref_get(v___y_7099_);
                v_env_7102_ = lean_ctor_get(v___x_7101_, 0);
                lean_inc_ref(v_env_7102_);
                lean_dec(v___x_7101_);
                v___x_7103_ = 0;
                lean_inc(v_constName_7095_);
                v___x_7104_ =
                    l_Lean_Environment_find_x3f(v_env_7102_, v_constName_7095_, v___x_7103_);
                if lean_obj_tag(v___x_7104_) == 0 {
                    v___x_7105_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_7095_, v___y_7096_, v___y_7097_, v___y_7098_, v___y_7099_);
                    return v___x_7105_;
                } else {
                    lean_dec(v_constName_7095_);
                    v_val_7106_ = lean_ctor_get(v___x_7104_, 0);
                    v_isSharedCheck_7113_ = (!lean_is_exclusive(v___x_7104_)) as u8;
                    if v_isSharedCheck_7113_ == 0 {
                        v___x_7108_ = v___x_7104_;
                        v_isShared_7109_ = v_isSharedCheck_7113_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_7106_);
                        lean_dec(v___x_7104_);
                        v___x_7108_ = lean_box(0);
                        v_isShared_7109_ = v_isSharedCheck_7113_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7109_ == 0 {
                    lean_ctor_set_tag(v___x_7108_, 0);
                    v___x_7111_ = v___x_7108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7112_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7112_, 0, v_val_7106_);
                    v___x_7111_ = v_reuseFailAlloc_7112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(
    mut v_constName_7114_: *mut LeanObject,
    mut v___y_7115_: *mut LeanObject,
    mut v___y_7116_: *mut LeanObject,
    mut v___y_7117_: *mut LeanObject,
    mut v___y_7118_: *mut LeanObject,
    mut v___y_7119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7120_: *mut LeanObject = core::ptr::null_mut();
    v_res_7120_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_);
    lean_dec(v___y_7118_);
    lean_dec_ref(v___y_7117_);
    lean_dec(v___y_7116_);
    lean_dec_ref(v___y_7115_);
    return v_res_7120_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(
    mut v_e_7121_: *mut LeanObject,
    mut v_as_7122_: *mut LeanObject,
    mut v_i_7123_: usize,
    mut v_stop_7124_: usize,
) -> u8 {
    let mut v___x_7125_: u8 = 0;
    let mut v___x_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: u8 = 0;
    let mut v___x_7128_: usize = 0;
    let mut v___x_7129_: usize = 0;
    let mut v___x_7131_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7125_ = lean_usize_dec_eq(v_i_7123_, v_stop_7124_);
                if v___x_7125_ == 0 {
                    v___x_7126_ = lean_array_uget_borrowed(v_as_7122_, v_i_7123_);
                    v___x_7127_ = l_Lean_Expr_isAppOf(v_e_7121_, v___x_7126_);
                    if v___x_7127_ == 0 {
                        v___x_7128_ = 1usize;
                        v___x_7129_ = lean_usize_add(v_i_7123_, v___x_7128_);
                        v_i_7123_ = v___x_7129_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7127_;
                    }
                } else {
                    v___x_7131_ = 0;
                    return v___x_7131_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(
    mut v_e_7132_: *mut LeanObject,
    mut v_as_7133_: *mut LeanObject,
    mut v_i_7134_: *mut LeanObject,
    mut v_stop_7135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7136_: usize = 0;
    let mut v_stop_boxed_7137_: usize = 0;
    let mut v_res_7138_: u8 = 0;
    let mut v_r_7139_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7136_ = lean_unbox_usize(v_i_7134_);
    lean_dec(v_i_7134_);
    v_stop_boxed_7137_ = lean_unbox_usize(v_stop_7135_);
    lean_dec(v_stop_7135_);
    v_res_7138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_7132_, v_as_7133_, v_i_boxed_7136_, v_stop_boxed_7137_);
    lean_dec_ref(v_as_7133_);
    lean_dec_ref(v_e_7132_);
    v_r_7139_ = lean_box((v_res_7138_) as usize);
    return v_r_7139_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(
    mut v_numParams_7140_: *mut LeanObject,
    mut v_name_7141_: *mut LeanObject,
    mut v_levels_7142_: *mut LeanObject,
    mut v_params_7143_: *mut LeanObject,
    mut v___y_7144_: *mut LeanObject,
    mut v___x_7145_: *mut LeanObject,
    mut v_e_7146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7147_: u8 = 0;
    let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7158_: u8 = 0;
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: u8 = 0;
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: u8 = 0;
    let mut v___x_7171_: usize = 0;
    let mut v___x_7172_: usize = 0;
    let mut v___x_7173_: u8 = 0;
    let mut v___x_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7147_ = l_Lean_Expr_isApp(v_e_7146_);
                if v___x_7147_ == 0 {
                    lean_dec_ref(v_e_7146_);
                    lean_dec_ref(v_params_7143_);
                    lean_dec(v_levels_7142_);
                    lean_dec(v_name_7141_);
                    lean_dec(v_numParams_7140_);
                    v___x_7148_ = lean_box(0);
                    return v___x_7148_;
                } else {
                    v_dummy_7149_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once), _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
                    v_nargs_7150_ = l_Lean_Expr_getAppNumArgs(v_e_7146_);
                    lean_inc(v_nargs_7150_);
                    v___x_7151_ = lean_mk_array(v_nargs_7150_, v_dummy_7149_);
                    v___x_7152_ = lean_unsigned_to_nat(1);
                    v___x_7153_ = lean_nat_sub(v_nargs_7150_, v___x_7152_);
                    lean_dec(v_nargs_7150_);
                    lean_inc_ref(v_e_7146_);
                    v___x_7154_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_7146_,
                        v___x_7151_,
                        v___x_7153_,
                    );
                    v___x_7155_ = lean_array_get_size(v___x_7154_);
                    v___x_7156_ =
                        l_Array_toSubarray___redArg(v___x_7154_, v_numParams_7140_, v___x_7155_);
                    v___x_7168_ = l_Lean_Expr_isAppOf(v_e_7146_, v_name_7141_);
                    if v___x_7168_ == 0 {
                        lean_dec(v_name_7141_);
                        v___x_7169_ = lean_array_get_size(v___y_7144_);
                        v___x_7170_ = lean_nat_dec_lt(v___x_7145_, v___x_7169_);
                        if v___x_7170_ == 0 {
                            v___y_7158_ = v___x_7168_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_7170_ == 0 {
                                v___y_7158_ = v___x_7168_;
                                state = 1;
                                continue;
                            } else {
                                v___x_7171_ = 0usize;
                                v___x_7172_ = lean_usize_of_nat(v___x_7169_);
                                v___x_7173_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_7146_, v___y_7144_, v___x_7171_, v___x_7172_);
                                v___y_7158_ = v___x_7173_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_7146_);
                        v___x_7174_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_7141_);
                        v___x_7175_ = l_Lean_mkConst(v___x_7174_, v_levels_7142_);
                        v___x_7176_ = l_Subarray_copy___redArg(v___x_7156_);
                        v___x_7177_ = l_Array_append___redArg(v_params_7143_, v___x_7176_);
                        lean_dec_ref(v___x_7176_);
                        v___x_7178_ = l_Lean_mkAppN(v___x_7175_, v___x_7177_);
                        lean_dec_ref(v___x_7177_);
                        v___x_7179_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_7179_, 0, v___x_7178_);
                        return v___x_7179_;
                    }
                }
            }
            1 => {
                if v___y_7158_ == 0 {
                    lean_dec_ref(v___x_7156_);
                    lean_dec_ref(v_e_7146_);
                    lean_dec_ref(v_params_7143_);
                    lean_dec(v_levels_7142_);
                    v___x_7159_ = lean_box(0);
                    return v___x_7159_;
                } else {
                    v___x_7160_ = l_Lean_Expr_getAppFn(v_e_7146_);
                    lean_dec_ref(v_e_7146_);
                    v___x_7161_ = l_Lean_Expr_constName(v___x_7160_);
                    lean_dec_ref(v___x_7160_);
                    v___x_7162_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_7161_);
                    v___x_7163_ = l_Lean_mkConst(v___x_7162_, v_levels_7142_);
                    v___x_7164_ = l_Subarray_copy___redArg(v___x_7156_);
                    v___x_7165_ = l_Array_append___redArg(v_params_7143_, v___x_7164_);
                    lean_dec_ref(v___x_7164_);
                    v___x_7166_ = l_Lean_mkAppN(v___x_7163_, v___x_7165_);
                    lean_dec_ref(v___x_7165_);
                    v___x_7167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7167_, 0, v___x_7166_);
                    return v___x_7167_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(
    mut v_numParams_7180_: *mut LeanObject,
    mut v_name_7181_: *mut LeanObject,
    mut v_levels_7182_: *mut LeanObject,
    mut v_params_7183_: *mut LeanObject,
    mut v___y_7184_: *mut LeanObject,
    mut v___x_7185_: *mut LeanObject,
    mut v_e_7186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7187_: *mut LeanObject = core::ptr::null_mut();
    v_res_7187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_7180_, v_name_7181_, v_levels_7182_, v_params_7183_, v___y_7184_, v___x_7185_, v_e_7186_);
    lean_dec(v___x_7185_);
    lean_dec_ref(v___y_7184_);
    return v_res_7187_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(
    mut v_eqProof_7188_: *mut LeanObject,
    mut v___x_7189_: *mut LeanObject,
    mut v_eNew_7190_: *mut LeanObject,
    mut v_snd_7191_: *mut LeanObject,
    mut v___x_7192_: *mut LeanObject,
    mut v___y_7193_: *mut LeanObject,
    mut v___y_7194_: *mut LeanObject,
    mut v___y_7195_: *mut LeanObject,
    mut v___y_7196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7206_: u8 = 0;
    let mut v___x_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7198_ = l_Lean_Meta_mkEqMP(
                    v_eqProof_7188_,
                    v___x_7189_,
                    v___y_7193_,
                    v___y_7194_,
                    v___y_7195_,
                    v___y_7196_,
                );
                if lean_obj_tag(v___x_7198_) == 0 {
                    v_a_7199_ = lean_ctor_get(v___x_7198_, 0);
                    lean_inc(v_a_7199_);
                    lean_dec_ref_known(v___x_7198_, 1);
                    v___x_7200_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7200_, 0, v_eNew_7190_);
                    v___x_7201_ = lean_box(0);
                    v___x_7202_ = l_Lean_MVarId_replace(
                        v_snd_7191_,
                        v___x_7192_,
                        v_a_7199_,
                        v___x_7200_,
                        v___x_7201_,
                        v___y_7193_,
                        v___y_7194_,
                        v___y_7195_,
                        v___y_7196_,
                    );
                    return v___x_7202_;
                } else {
                    lean_dec(v___x_7192_);
                    lean_dec(v_snd_7191_);
                    lean_dec_ref(v_eNew_7190_);
                    v_a_7203_ = lean_ctor_get(v___x_7198_, 0);
                    v_isSharedCheck_7210_ = (!lean_is_exclusive(v___x_7198_)) as u8;
                    if v_isSharedCheck_7210_ == 0 {
                        v___x_7205_ = v___x_7198_;
                        v_isShared_7206_ = v_isSharedCheck_7210_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7203_);
                        lean_dec(v___x_7198_);
                        v___x_7205_ = lean_box(0);
                        v_isShared_7206_ = v_isSharedCheck_7210_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7206_ == 0 {
                    v___x_7208_ = v___x_7205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7209_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7209_, 0, v_a_7203_);
                    v___x_7208_ = v_reuseFailAlloc_7209_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(
    mut v_eqProof_7211_: *mut LeanObject,
    mut v___x_7212_: *mut LeanObject,
    mut v_eNew_7213_: *mut LeanObject,
    mut v_snd_7214_: *mut LeanObject,
    mut v___x_7215_: *mut LeanObject,
    mut v___y_7216_: *mut LeanObject,
    mut v___y_7217_: *mut LeanObject,
    mut v___y_7218_: *mut LeanObject,
    mut v___y_7219_: *mut LeanObject,
    mut v___y_7220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7221_: *mut LeanObject = core::ptr::null_mut();
    v_res_7221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v_eqProof_7211_, v___x_7212_, v_eNew_7213_, v_snd_7214_, v___x_7215_, v___y_7216_, v___y_7217_, v___y_7218_, v___y_7219_);
    lean_dec(v___y_7219_);
    lean_dec_ref(v___y_7218_);
    lean_dec(v___y_7217_);
    lean_dec_ref(v___y_7216_);
    return v_res_7221_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1()
-> *mut LeanObject {
    let mut v___x_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
    v___x_7223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0;
    v___x_7224_ = l_Lean_stringToMessageData(v___x_7223_);
    return v___x_7224_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10()
-> *mut LeanObject {
    let mut v___x_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    v___x_7246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9;
    v___x_7247_ = l_Lean_stringToMessageData(v___x_7246_);
    return v___x_7247_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(
    mut v___x_7248_: *mut LeanObject,
    mut v___x_7249_: *mut LeanObject,
    mut v___x_7250_: u8,
    mut v___x_7251_: *mut LeanObject,
    mut v___x_7252_: *mut LeanObject,
    mut v___x_7253_: u8,
    mut v___x_7254_: *mut LeanObject,
    mut v_params_7255_: *mut LeanObject,
    mut v_args_7256_: *mut LeanObject,
    mut v_indices_7257_: *mut LeanObject,
    mut v___x_7258_: u8,
    mut v___x_7259_: *mut LeanObject,
    mut v_a_7260_: *mut LeanObject,
    mut v___x_7261_: *mut LeanObject,
    mut v___f_7262_: *mut LeanObject,
    mut v___x_7263_: *mut LeanObject,
    mut v_targetArgs_7264_: *mut LeanObject,
    mut v_x_7265_: *mut LeanObject,
    mut v___y_7266_: *mut LeanObject,
    mut v___y_7267_: *mut LeanObject,
    mut v___y_7268_: *mut LeanObject,
    mut v___y_7269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: u8 = 0;
    let mut v___x_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7288_: u8 = 0;
    let mut v___x_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: u8 = 0;
    let mut v___x_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7320_: u8 = 0;
    let mut v_fst_7321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7325_: u8 = 0;
    let mut v_a_7326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7329_: u8 = 0;
    let mut v___x_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7333_: u8 = 0;
    let mut v_reuseFailAlloc_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7338_: u8 = 0;
    let mut v___x_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7342_: u8 = 0;
    let mut v_a_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7346_: u8 = 0;
    let mut v___x_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7350_: u8 = 0;
    let mut v_a_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7354_: u8 = 0;
    let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7358_: u8 = 0;
    let mut v_a_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7362_: u8 = 0;
    let mut v___x_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7366_: u8 = 0;
    let mut v_isSharedCheck_7367_: u8 = 0;
    let mut v_unused_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7372_: u8 = 0;
    let mut v___x_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7376_: u8 = 0;
    let mut v_a_7377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7380_: u8 = 0;
    let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7384_: u8 = 0;
    let mut v___x_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7390_: u8 = 0;
    let mut v___x_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7271_ = lean_array_get_size(v_targetArgs_7264_);
                v___x_7272_ = lean_nat_dec_eq(v___x_7271_, v___x_7248_);
                if v___x_7272_ == 0 {
                    lean_dec(v___x_7263_);
                    lean_dec_ref(v___f_7262_);
                    lean_dec(v___x_7261_);
                    lean_dec_ref(v___x_7259_);
                    lean_dec_ref(v_params_7255_);
                    lean_dec_ref(v___x_7252_);
                    lean_dec(v___x_7251_);
                    lean_dec_ref(v___x_7249_);
                    v___x_7273_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
                    v___x_7274_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_7273_, v___y_7266_, v___y_7267_, v___y_7268_, v___y_7269_);
                    return v___x_7274_;
                } else {
                    lean_inc(v___y_7269_);
                    lean_inc_ref(v___y_7268_);
                    lean_inc(v___y_7267_);
                    lean_inc_ref(v___y_7266_);
                    lean_inc_ref(v___x_7249_);
                    v___x_7275_ = lean_infer_type(
                        v___x_7249_,
                        v___y_7266_,
                        v___y_7267_,
                        v___y_7268_,
                        v___y_7269_,
                    );
                    if lean_obj_tag(v___x_7275_) == 0 {
                        v_a_7276_ = lean_ctor_get(v___x_7275_, 0);
                        lean_inc(v_a_7276_);
                        lean_dec_ref_known(v___x_7275_, 1);
                        if lean_obj_tag(v_a_7276_) == 7 {
                            v_binderType_7277_ = lean_ctor_get(v_a_7276_, 1);
                            lean_inc_ref(v_binderType_7277_);
                            lean_dec_ref_known(v_a_7276_, 3);
                            v___x_7278_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_7278_, 0, v_binderType_7277_);
                            v___x_7279_ = l_Lean_Meta_mkFreshExprMVar(
                                v___x_7278_,
                                v___x_7250_,
                                v___x_7251_,
                                v___y_7266_,
                                v___y_7267_,
                                v___y_7268_,
                                v___y_7269_,
                            );
                            if lean_obj_tag(v___x_7279_) == 0 {
                                v_a_7280_ = lean_ctor_get(v___x_7279_, 0);
                                lean_inc(v_a_7280_);
                                lean_dec_ref_known(v___x_7279_, 1);
                                v___x_7281_ = l_Lean_Expr_mvarId_x21(v_a_7280_);
                                v___x_7282_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_7281_, v___x_7252_, v___x_7253_, v___y_7266_, v___y_7267_, v___y_7268_, v___y_7269_);
                                if lean_obj_tag(v___x_7282_) == 0 {
                                    v_a_7283_ = lean_ctor_get(v___x_7282_, 0);
                                    lean_inc(v_a_7283_);
                                    lean_dec_ref_known(v___x_7282_, 1);
                                    v___x_7284_ =
                                        lean_array_fget_borrowed(v_targetArgs_7264_, v___x_7254_);
                                    lean_inc(v___x_7284_);
                                    v___x_7285_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_7283_, v___x_7284_, v___y_7267_);
                                    if lean_obj_tag(v___x_7285_) == 0 {
                                        v_isSharedCheck_7367_ =
                                            (!lean_is_exclusive(v___x_7285_)) as u8;
                                        if v_isSharedCheck_7367_ == 0 {
                                            v_unused_7368_ = lean_ctor_get(v___x_7285_, 0);
                                            lean_dec(v_unused_7368_);
                                            v___x_7287_ = v___x_7285_;
                                            v_isShared_7288_ = v_isSharedCheck_7367_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec(v___x_7285_);
                                            v___x_7287_ = lean_box(0);
                                            v_isShared_7288_ = v_isSharedCheck_7367_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_7280_);
                                        lean_dec(v___x_7263_);
                                        lean_dec_ref(v___f_7262_);
                                        lean_dec(v___x_7261_);
                                        lean_dec_ref(v___x_7259_);
                                        lean_dec_ref(v_params_7255_);
                                        lean_dec_ref(v___x_7249_);
                                        return v___x_7285_;
                                    }
                                } else {
                                    lean_dec(v_a_7280_);
                                    lean_dec(v___x_7263_);
                                    lean_dec_ref(v___f_7262_);
                                    lean_dec(v___x_7261_);
                                    lean_dec_ref(v___x_7259_);
                                    lean_dec_ref(v_params_7255_);
                                    lean_dec_ref(v___x_7249_);
                                    v_a_7369_ = lean_ctor_get(v___x_7282_, 0);
                                    v_isSharedCheck_7376_ = (!lean_is_exclusive(v___x_7282_)) as u8;
                                    if v_isSharedCheck_7376_ == 0 {
                                        v___x_7371_ = v___x_7282_;
                                        v_isShared_7372_ = v_isSharedCheck_7376_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7369_);
                                        lean_dec(v___x_7282_);
                                        v___x_7371_ = lean_box(0);
                                        v_isShared_7372_ = v_isSharedCheck_7376_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___x_7263_);
                                lean_dec_ref(v___f_7262_);
                                lean_dec(v___x_7261_);
                                lean_dec_ref(v___x_7259_);
                                lean_dec_ref(v_params_7255_);
                                lean_dec_ref(v___x_7252_);
                                lean_dec_ref(v___x_7249_);
                                v_a_7377_ = lean_ctor_get(v___x_7279_, 0);
                                v_isSharedCheck_7384_ = (!lean_is_exclusive(v___x_7279_)) as u8;
                                if v_isSharedCheck_7384_ == 0 {
                                    v___x_7379_ = v___x_7279_;
                                    v_isShared_7380_ = v_isSharedCheck_7384_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_7377_);
                                    lean_dec(v___x_7279_);
                                    v___x_7379_ = lean_box(0);
                                    v_isShared_7380_ = v_isSharedCheck_7384_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_7276_);
                            lean_dec(v___x_7263_);
                            lean_dec_ref(v___f_7262_);
                            lean_dec(v___x_7261_);
                            lean_dec_ref(v___x_7259_);
                            lean_dec_ref(v_params_7255_);
                            lean_dec_ref(v___x_7252_);
                            lean_dec(v___x_7251_);
                            lean_dec_ref(v___x_7249_);
                            v___x_7385_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
                            v___x_7386_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_7385_, v___y_7266_, v___y_7267_, v___y_7268_, v___y_7269_);
                            return v___x_7386_;
                        }
                    } else {
                        lean_dec(v___x_7263_);
                        lean_dec_ref(v___f_7262_);
                        lean_dec(v___x_7261_);
                        lean_dec_ref(v___x_7259_);
                        lean_dec_ref(v_params_7255_);
                        lean_dec_ref(v___x_7252_);
                        lean_dec(v___x_7251_);
                        lean_dec_ref(v___x_7249_);
                        v_a_7387_ = lean_ctor_get(v___x_7275_, 0);
                        v_isSharedCheck_7394_ = (!lean_is_exclusive(v___x_7275_)) as u8;
                        if v_isSharedCheck_7394_ == 0 {
                            v___x_7389_ = v___x_7275_;
                            v_isShared_7390_ = v_isSharedCheck_7394_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_7387_);
                            lean_dec(v___x_7275_);
                            v___x_7389_ = lean_box(0);
                            v_isShared_7390_ = v_isSharedCheck_7394_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7289_ = l_Lean_Expr_app___override(v___x_7249_, v_a_7280_);
                lean_inc_ref(v_params_7255_);
                v___x_7290_ = l_Array_append___redArg(v_params_7255_, v_args_7256_);
                v___x_7291_ = l_Array_append___redArg(v___x_7290_, v_indices_7257_);
                v___x_7292_ = l_Array_append___redArg(v___x_7291_, v_targetArgs_7264_);
                v___x_7293_ = 1;
                v___x_7294_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_7292_,
                    v___x_7289_,
                    v___x_7258_,
                    v___x_7253_,
                    v___x_7258_,
                    v___x_7253_,
                    v___x_7293_,
                    v___y_7266_,
                    v___y_7267_,
                    v___y_7268_,
                    v___y_7269_,
                );
                lean_dec_ref(v___x_7292_);
                if lean_obj_tag(v___x_7294_) == 0 {
                    v_a_7295_ = lean_ctor_get(v___x_7294_, 0);
                    lean_inc(v_a_7295_);
                    lean_dec_ref_known(v___x_7294_, 1);
                    v___x_7296_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_7295_, v___y_7267_);
                    if lean_obj_tag(v___x_7296_) == 0 {
                        v_a_7297_ = lean_ctor_get(v___x_7296_, 0);
                        lean_inc(v_a_7297_);
                        lean_dec_ref_known(v___x_7296_, 1);
                        v___x_7298_ = l_Lean_Meta_mkForallFVars(
                            v_params_7255_,
                            v___x_7259_,
                            v___x_7258_,
                            v___x_7253_,
                            v___x_7253_,
                            v___x_7293_,
                            v___y_7266_,
                            v___y_7267_,
                            v___y_7268_,
                            v___y_7269_,
                        );
                        lean_dec_ref(v_params_7255_);
                        if lean_obj_tag(v___x_7298_) == 0 {
                            v_a_7299_ = lean_ctor_get(v___x_7298_, 0);
                            lean_inc(v_a_7299_);
                            lean_dec_ref_known(v___x_7298_, 1);
                            v___x_7300_ = l_Lean_ConstantInfo_levelParams(v_a_7260_);
                            v___x_7301_ = l_Lean_mkCasesOnName(v___x_7261_);
                            v___x_7302_ = lean_box(0);
                            lean_inc(v___x_7301_);
                            v___x_7303_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_7301_, v___x_7300_, v_a_7299_, v_a_7297_, v___x_7302_, v___y_7269_);
                            if lean_obj_tag(v___x_7303_) == 0 {
                                v_a_7304_ = lean_ctor_get(v___x_7303_, 0);
                                lean_inc(v_a_7304_);
                                lean_dec_ref_known(v___x_7303_, 1);
                                if v_isShared_7288_ == 0 {
                                    lean_ctor_set_tag(v___x_7287_, 1);
                                    lean_ctor_set(v___x_7287_, 0, v_a_7304_);
                                    v___x_7306_ = v___x_7287_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7334_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_7334_, 0, v_a_7304_);
                                    v___x_7306_ = v_reuseFailAlloc_7334_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_7301_);
                                lean_del_object(v___x_7287_);
                                lean_dec(v___x_7263_);
                                lean_dec_ref(v___f_7262_);
                                v_a_7335_ = lean_ctor_get(v___x_7303_, 0);
                                v_isSharedCheck_7342_ = (!lean_is_exclusive(v___x_7303_)) as u8;
                                if v_isSharedCheck_7342_ == 0 {
                                    v___x_7337_ = v___x_7303_;
                                    v_isShared_7338_ = v_isSharedCheck_7342_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_7335_);
                                    lean_dec(v___x_7303_);
                                    v___x_7337_ = lean_box(0);
                                    v_isShared_7338_ = v_isSharedCheck_7342_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_7297_);
                            lean_del_object(v___x_7287_);
                            lean_dec(v___x_7263_);
                            lean_dec_ref(v___f_7262_);
                            lean_dec(v___x_7261_);
                            v_a_7343_ = lean_ctor_get(v___x_7298_, 0);
                            v_isSharedCheck_7350_ = (!lean_is_exclusive(v___x_7298_)) as u8;
                            if v_isSharedCheck_7350_ == 0 {
                                v___x_7345_ = v___x_7298_;
                                v_isShared_7346_ = v_isSharedCheck_7350_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_7343_);
                                lean_dec(v___x_7298_);
                                v___x_7345_ = lean_box(0);
                                v_isShared_7346_ = v_isSharedCheck_7350_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_7287_);
                        lean_dec(v___x_7263_);
                        lean_dec_ref(v___f_7262_);
                        lean_dec(v___x_7261_);
                        lean_dec_ref(v___x_7259_);
                        lean_dec_ref(v_params_7255_);
                        v_a_7351_ = lean_ctor_get(v___x_7296_, 0);
                        v_isSharedCheck_7358_ = (!lean_is_exclusive(v___x_7296_)) as u8;
                        if v_isSharedCheck_7358_ == 0 {
                            v___x_7353_ = v___x_7296_;
                            v_isShared_7354_ = v_isSharedCheck_7358_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_7351_);
                            lean_dec(v___x_7296_);
                            v___x_7353_ = lean_box(0);
                            v_isShared_7354_ = v_isSharedCheck_7358_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_7287_);
                    lean_dec(v___x_7263_);
                    lean_dec_ref(v___f_7262_);
                    lean_dec(v___x_7261_);
                    lean_dec_ref(v___x_7259_);
                    lean_dec_ref(v_params_7255_);
                    v_a_7359_ = lean_ctor_get(v___x_7294_, 0);
                    v_isSharedCheck_7366_ = (!lean_is_exclusive(v___x_7294_)) as u8;
                    if v_isSharedCheck_7366_ == 0 {
                        v___x_7361_ = v___x_7294_;
                        v_isShared_7362_ = v_isSharedCheck_7366_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_7359_);
                        lean_dec(v___x_7294_);
                        v___x_7361_ = lean_box(0);
                        v_isShared_7362_ = v_isSharedCheck_7366_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7307_ = l_Lean_addDecl(v___x_7306_, v___x_7258_, v___y_7268_, v___y_7269_);
                if lean_obj_tag(v___x_7307_) == 0 {
                    lean_dec_ref_known(v___x_7307_, 1);
                    v___x_7308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8;
                    v___x_7309_ = lean_alloc_closure(
                        l_Lean_Elab_Term_applyAttributes___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___x_7309_, 0, v___x_7301_);
                    lean_closure_set(v___x_7309_, 1, v___x_7308_);
                    v___x_7310_ = lean_box(0);
                    v___x_7311_ = lean_box(0);
                    v___x_7312_ = lean_box(1);
                    v___x_7313_ = lean_mk_empty_array_with_capacity(v___x_7254_);
                    v___x_7314_ = lean_alloc_ctor(0, 8, (11) as u32);
                    lean_ctor_set(v___x_7314_, 0, v___x_7310_);
                    lean_ctor_set(v___x_7314_, 1, v___x_7311_);
                    lean_ctor_set(v___x_7314_, 2, v___x_7310_);
                    lean_ctor_set(v___x_7314_, 3, v___f_7262_);
                    lean_ctor_set(v___x_7314_, 4, v___x_7312_);
                    lean_ctor_set(v___x_7314_, 5, v___x_7312_);
                    lean_ctor_set(v___x_7314_, 6, v___x_7310_);
                    lean_ctor_set(v___x_7314_, 7, v___x_7313_);
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                        v___x_7253_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 1) as u32,
                        v___x_7253_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                        v___x_7253_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 3) as u32,
                        v___x_7253_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 4) as u32,
                        v___x_7258_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 5) as u32,
                        v___x_7258_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 6) as u32,
                        v___x_7258_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 7) as u32,
                        v___x_7258_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 8) as u32,
                        v___x_7253_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 9) as u32,
                        v___x_7258_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7314_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 10) as u32,
                        v___x_7253_,
                    );
                    v___x_7315_ = lean_alloc_ctor(0, 7, (0) as u32);
                    lean_ctor_set(v___x_7315_, 0, v___x_7263_);
                    lean_ctor_set(v___x_7315_, 1, v___x_7312_);
                    lean_ctor_set(v___x_7315_, 2, v___x_7311_);
                    lean_ctor_set(v___x_7315_, 3, v___x_7311_);
                    lean_ctor_set(v___x_7315_, 4, v___x_7311_);
                    lean_ctor_set(v___x_7315_, 5, v___x_7312_);
                    lean_ctor_set(v___x_7315_, 6, v___x_7311_);
                    v___x_7316_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                        v___x_7309_,
                        v___x_7314_,
                        v___x_7315_,
                        v___y_7266_,
                        v___y_7267_,
                        v___y_7268_,
                        v___y_7269_,
                    );
                    if lean_obj_tag(v___x_7316_) == 0 {
                        v_a_7317_ = lean_ctor_get(v___x_7316_, 0);
                        v_isSharedCheck_7325_ = (!lean_is_exclusive(v___x_7316_)) as u8;
                        if v_isSharedCheck_7325_ == 0 {
                            v___x_7319_ = v___x_7316_;
                            v_isShared_7320_ = v_isSharedCheck_7325_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7317_);
                            lean_dec(v___x_7316_);
                            v___x_7319_ = lean_box(0);
                            v_isShared_7320_ = v_isSharedCheck_7325_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7326_ = lean_ctor_get(v___x_7316_, 0);
                        v_isSharedCheck_7333_ = (!lean_is_exclusive(v___x_7316_)) as u8;
                        if v_isSharedCheck_7333_ == 0 {
                            v___x_7328_ = v___x_7316_;
                            v_isShared_7329_ = v_isSharedCheck_7333_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_7326_);
                            lean_dec(v___x_7316_);
                            v___x_7328_ = lean_box(0);
                            v_isShared_7329_ = v_isSharedCheck_7333_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_7301_);
                    lean_dec(v___x_7263_);
                    lean_dec_ref(v___f_7262_);
                    return v___x_7307_;
                }
            }
            3 => {
                v_fst_7321_ = lean_ctor_get(v_a_7317_, 0);
                lean_inc(v_fst_7321_);
                lean_dec(v_a_7317_);
                if v_isShared_7320_ == 0 {
                    lean_ctor_set(v___x_7319_, 0, v_fst_7321_);
                    v___x_7323_ = v___x_7319_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7324_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7324_, 0, v_fst_7321_);
                    v___x_7323_ = v_reuseFailAlloc_7324_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7323_;
            }
            5 => {
                if v_isShared_7329_ == 0 {
                    v___x_7331_ = v___x_7328_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7332_, 0, v_a_7326_);
                    v___x_7331_ = v_reuseFailAlloc_7332_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7331_;
            }
            7 => {
                if v_isShared_7338_ == 0 {
                    v___x_7340_ = v___x_7337_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7341_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7341_, 0, v_a_7335_);
                    v___x_7340_ = v_reuseFailAlloc_7341_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7340_;
            }
            9 => {
                if v_isShared_7346_ == 0 {
                    v___x_7348_ = v___x_7345_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7349_, 0, v_a_7343_);
                    v___x_7348_ = v_reuseFailAlloc_7349_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7348_;
            }
            11 => {
                if v_isShared_7354_ == 0 {
                    v___x_7356_ = v___x_7353_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7357_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7357_, 0, v_a_7351_);
                    v___x_7356_ = v_reuseFailAlloc_7357_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7356_;
            }
            13 => {
                if v_isShared_7362_ == 0 {
                    v___x_7364_ = v___x_7361_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7365_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7365_, 0, v_a_7359_);
                    v___x_7364_ = v_reuseFailAlloc_7365_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7364_;
            }
            15 => {
                if v_isShared_7372_ == 0 {
                    v___x_7374_ = v___x_7371_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7375_, 0, v_a_7369_);
                    v___x_7374_ = v_reuseFailAlloc_7375_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7374_;
            }
            17 => {
                if v_isShared_7380_ == 0 {
                    v___x_7382_ = v___x_7379_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7383_, 0, v_a_7377_);
                    v___x_7382_ = v_reuseFailAlloc_7383_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7382_;
            }
            19 => {
                if v_isShared_7390_ == 0 {
                    v___x_7392_ = v___x_7389_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7393_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7393_, 0, v_a_7387_);
                    v___x_7392_ = v_reuseFailAlloc_7393_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7392_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7395_: *mut LeanObject = *_args.add(0);
    let mut v___x_7396_: *mut LeanObject = *_args.add(1);
    let mut v___x_7397_: *mut LeanObject = *_args.add(2);
    let mut v___x_7398_: *mut LeanObject = *_args.add(3);
    let mut v___x_7399_: *mut LeanObject = *_args.add(4);
    let mut v___x_7400_: *mut LeanObject = *_args.add(5);
    let mut v___x_7401_: *mut LeanObject = *_args.add(6);
    let mut v_params_7402_: *mut LeanObject = *_args.add(7);
    let mut v_args_7403_: *mut LeanObject = *_args.add(8);
    let mut v_indices_7404_: *mut LeanObject = *_args.add(9);
    let mut v___x_7405_: *mut LeanObject = *_args.add(10);
    let mut v___x_7406_: *mut LeanObject = *_args.add(11);
    let mut v_a_7407_: *mut LeanObject = *_args.add(12);
    let mut v___x_7408_: *mut LeanObject = *_args.add(13);
    let mut v___f_7409_: *mut LeanObject = *_args.add(14);
    let mut v___x_7410_: *mut LeanObject = *_args.add(15);
    let mut v_targetArgs_7411_: *mut LeanObject = *_args.add(16);
    let mut v_x_7412_: *mut LeanObject = *_args.add(17);
    let mut v___y_7413_: *mut LeanObject = *_args.add(18);
    let mut v___y_7414_: *mut LeanObject = *_args.add(19);
    let mut v___y_7415_: *mut LeanObject = *_args.add(20);
    let mut v___y_7416_: *mut LeanObject = *_args.add(21);
    let mut v___y_7417_: *mut LeanObject = *_args.add(22);
    let mut v___x_16827__boxed_7418_: u8 = 0;
    let mut v___x_16830__boxed_7419_: u8 = 0;
    let mut v___x_16832__boxed_7420_: u8 = 0;
    let mut v_res_7421_: *mut LeanObject = core::ptr::null_mut();
    v___x_16827__boxed_7418_ = (lean_unbox(v___x_7397_) as u8);
    v___x_16830__boxed_7419_ = (lean_unbox(v___x_7400_) as u8);
    v___x_16832__boxed_7420_ = (lean_unbox(v___x_7405_) as u8);
    v_res_7421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_7395_, v___x_7396_, v___x_16827__boxed_7418_, v___x_7398_, v___x_7399_, v___x_16830__boxed_7419_, v___x_7401_, v_params_7402_, v_args_7403_, v_indices_7404_, v___x_16832__boxed_7420_, v___x_7406_, v_a_7407_, v___x_7408_, v___f_7409_, v___x_7410_, v_targetArgs_7411_, v_x_7412_, v___y_7413_, v___y_7414_, v___y_7415_, v___y_7416_);
    lean_dec(v___y_7416_);
    lean_dec_ref(v___y_7415_);
    lean_dec(v___y_7414_);
    lean_dec_ref(v___y_7413_);
    lean_dec_ref(v_x_7412_);
    lean_dec_ref(v_targetArgs_7411_);
    lean_dec_ref(v_a_7407_);
    lean_dec_ref(v_indices_7404_);
    lean_dec_ref(v_args_7403_);
    lean_dec(v___x_7401_);
    lean_dec(v___x_7395_);
    return v_res_7421_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(
    mut v___x_7422_: *mut LeanObject,
    mut v___x_7423_: *mut LeanObject,
    mut v___x_7424_: u8,
    mut v___x_7425_: *mut LeanObject,
    mut v___x_7426_: *mut LeanObject,
    mut v___x_7427_: u8,
    mut v___x_7428_: *mut LeanObject,
    mut v_params_7429_: *mut LeanObject,
    mut v_args_7430_: *mut LeanObject,
    mut v___x_7431_: u8,
    mut v___x_7432_: *mut LeanObject,
    mut v_a_7433_: *mut LeanObject,
    mut v___x_7434_: *mut LeanObject,
    mut v___f_7435_: *mut LeanObject,
    mut v___x_7436_: *mut LeanObject,
    mut v___x_7437_: *mut LeanObject,
    mut v_indices_7438_: *mut LeanObject,
    mut v_goalType_7439_: *mut LeanObject,
    mut v___y_7440_: *mut LeanObject,
    mut v___y_7441_: *mut LeanObject,
    mut v___y_7442_: *mut LeanObject,
    mut v___y_7443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7450_: *mut LeanObject = core::ptr::null_mut();
    v___x_7445_ = l_Lean_mkAppN(v___x_7422_, v_indices_7438_);
    v___x_7446_ = lean_box((v___x_7424_) as usize);
    v___x_7447_ = lean_box((v___x_7427_) as usize);
    v___x_7448_ = lean_box((v___x_7431_) as usize);
    v___f_7449_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed as *mut core::ffi::c_void, 23, 16);
    lean_closure_set(v___f_7449_, 0, v___x_7423_);
    lean_closure_set(v___f_7449_, 1, v___x_7445_);
    lean_closure_set(v___f_7449_, 2, v___x_7446_);
    lean_closure_set(v___f_7449_, 3, v___x_7425_);
    lean_closure_set(v___f_7449_, 4, v___x_7426_);
    lean_closure_set(v___f_7449_, 5, v___x_7447_);
    lean_closure_set(v___f_7449_, 6, v___x_7428_);
    lean_closure_set(v___f_7449_, 7, v_params_7429_);
    lean_closure_set(v___f_7449_, 8, v_args_7430_);
    lean_closure_set(v___f_7449_, 9, v_indices_7438_);
    lean_closure_set(v___f_7449_, 10, v___x_7448_);
    lean_closure_set(v___f_7449_, 11, v___x_7432_);
    lean_closure_set(v___f_7449_, 12, v_a_7433_);
    lean_closure_set(v___f_7449_, 13, v___x_7434_);
    lean_closure_set(v___f_7449_, 14, v___f_7435_);
    lean_closure_set(v___f_7449_, 15, v___x_7436_);
    v___x_7450_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_7439_, v___x_7437_, v___f_7449_, v___x_7431_, v___x_7431_, v___y_7440_, v___y_7441_, v___y_7442_, v___y_7443_);
    return v___x_7450_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7451_: *mut LeanObject = *_args.add(0);
    let mut v___x_7452_: *mut LeanObject = *_args.add(1);
    let mut v___x_7453_: *mut LeanObject = *_args.add(2);
    let mut v___x_7454_: *mut LeanObject = *_args.add(3);
    let mut v___x_7455_: *mut LeanObject = *_args.add(4);
    let mut v___x_7456_: *mut LeanObject = *_args.add(5);
    let mut v___x_7457_: *mut LeanObject = *_args.add(6);
    let mut v_params_7458_: *mut LeanObject = *_args.add(7);
    let mut v_args_7459_: *mut LeanObject = *_args.add(8);
    let mut v___x_7460_: *mut LeanObject = *_args.add(9);
    let mut v___x_7461_: *mut LeanObject = *_args.add(10);
    let mut v_a_7462_: *mut LeanObject = *_args.add(11);
    let mut v___x_7463_: *mut LeanObject = *_args.add(12);
    let mut v___f_7464_: *mut LeanObject = *_args.add(13);
    let mut v___x_7465_: *mut LeanObject = *_args.add(14);
    let mut v___x_7466_: *mut LeanObject = *_args.add(15);
    let mut v_indices_7467_: *mut LeanObject = *_args.add(16);
    let mut v_goalType_7468_: *mut LeanObject = *_args.add(17);
    let mut v___y_7469_: *mut LeanObject = *_args.add(18);
    let mut v___y_7470_: *mut LeanObject = *_args.add(19);
    let mut v___y_7471_: *mut LeanObject = *_args.add(20);
    let mut v___y_7472_: *mut LeanObject = *_args.add(21);
    let mut v___y_7473_: *mut LeanObject = *_args.add(22);
    let mut v___x_17163__boxed_7474_: u8 = 0;
    let mut v___x_17166__boxed_7475_: u8 = 0;
    let mut v___x_17168__boxed_7476_: u8 = 0;
    let mut v_res_7477_: *mut LeanObject = core::ptr::null_mut();
    v___x_17163__boxed_7474_ = (lean_unbox(v___x_7453_) as u8);
    v___x_17166__boxed_7475_ = (lean_unbox(v___x_7456_) as u8);
    v___x_17168__boxed_7476_ = (lean_unbox(v___x_7460_) as u8);
    v_res_7477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_7451_, v___x_7452_, v___x_17163__boxed_7474_, v___x_7454_, v___x_7455_, v___x_17166__boxed_7475_, v___x_7457_, v_params_7458_, v_args_7459_, v___x_17168__boxed_7476_, v___x_7461_, v_a_7462_, v___x_7463_, v___f_7464_, v___x_7465_, v___x_7466_, v_indices_7467_, v_goalType_7468_, v___y_7469_, v___y_7470_, v___y_7471_, v___y_7472_);
    lean_dec(v___y_7472_);
    lean_dec_ref(v___y_7471_);
    lean_dec(v___y_7470_);
    lean_dec_ref(v___y_7469_);
    return v_res_7477_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(
    mut v___x_7478_: *mut LeanObject,
    mut v___x_7479_: u8,
    mut v_snd_7480_: *mut LeanObject,
    mut v___x_7481_: *mut LeanObject,
    mut v___x_7482_: u8,
    mut v___x_7483_: *mut LeanObject,
    mut v___x_7484_: *mut LeanObject,
    mut v_a_7485_: *mut LeanObject,
    mut v___x_7486_: *mut LeanObject,
    mut v___x_7487_: u8,
    mut v___x_7488_: *mut LeanObject,
    mut v___x_7489_: *mut LeanObject,
    mut v_params_7490_: *mut LeanObject,
    mut v_args_7491_: *mut LeanObject,
    mut v___x_7492_: *mut LeanObject,
    mut v_a_7493_: *mut LeanObject,
    mut v___x_7494_: *mut LeanObject,
    mut v___f_7495_: *mut LeanObject,
    mut v___x_7496_: *mut LeanObject,
    mut v___x_7497_: *mut LeanObject,
    mut v_numIndices_7498_: *mut LeanObject,
    mut v_goalType_7499_: *mut LeanObject,
    mut v___x_7500_: *mut LeanObject,
    mut v___x_7501_: *mut LeanObject,
    mut v_fst_7502_: *mut LeanObject,
    mut v___x_7503_: *mut LeanObject,
    mut v___y_7504_: *mut LeanObject,
    mut v___y_7505_: *mut LeanObject,
    mut v___y_7506_: *mut LeanObject,
    mut v___y_7507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: u8 = 0;
    let mut v___x_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7514_: u8 = 0;
    let mut v___x_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eNew_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqProof_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7533_: u8 = 0;
    let mut v___x_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7543_: u8 = 0;
    let mut v_unused_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7548_: u8 = 0;
    let mut v___x_7550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7552_: u8 = 0;
    let mut v___x_7553_: u8 = 0;
    let mut v_fvarId_7554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_7555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7560_: u8 = 0;
    let mut v___x_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7564_: u8 = 0;
    let mut v_a_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7568_: u8 = 0;
    let mut v___x_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_7509_ = lean_ctor_get(v___y_7504_, 2);
                lean_inc(v___x_7478_);
                lean_inc_ref(v_lctx_7509_);
                v___x_7510_ = l_Lean_LocalContext_get_x21(v_lctx_7509_, v___x_7478_);
                v___x_7511_ = l_Lean_LocalDecl_type(v___x_7510_);
                lean_dec_ref(v___x_7510_);
                v___x_7512_ = 2;
                v___x_7513_ = lean_box(0);
                v___x_7514_ = 0;
                v___x_7515_ = lean_alloc_ctor(0, 1, (3) as u32);
                lean_ctor_set(v___x_7515_, 0, v___x_7513_);
                lean_ctor_set_uint8(
                    v___x_7515_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_7512_,
                );
                lean_ctor_set_uint8(
                    v___x_7515_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_7479_,
                );
                lean_ctor_set_uint8(
                    v___x_7515_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v___x_7514_,
                );
                lean_inc_ref(v___x_7481_);
                lean_inc(v_snd_7480_);
                v___x_7516_ = l_Lean_MVarId_rewrite(
                    v_snd_7480_,
                    v___x_7511_,
                    v___x_7481_,
                    v___x_7479_,
                    v___x_7515_,
                    v___y_7504_,
                    v___y_7505_,
                    v___y_7506_,
                    v___y_7507_,
                );
                if lean_obj_tag(v___x_7516_) == 0 {
                    v_a_7517_ = lean_ctor_get(v___x_7516_, 0);
                    lean_inc(v_a_7517_);
                    lean_dec_ref_known(v___x_7516_, 1);
                    v_eNew_7518_ = lean_ctor_get(v_a_7517_, 0);
                    lean_inc_ref(v_eNew_7518_);
                    v_eqProof_7519_ = lean_ctor_get(v_a_7517_, 1);
                    lean_inc_ref(v_eqProof_7519_);
                    lean_dec(v_a_7517_);
                    lean_inc(v___x_7478_);
                    v___x_7520_ = l_Lean_mkFVar(v___x_7478_);
                    lean_inc(v_snd_7480_);
                    v___f_7521_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed as *mut core::ffi::c_void, 10, 5);
                    lean_closure_set(v___f_7521_, 0, v_eqProof_7519_);
                    lean_closure_set(v___f_7521_, 1, v___x_7520_);
                    lean_closure_set(v___f_7521_, 2, v_eNew_7518_);
                    lean_closure_set(v___f_7521_, 3, v_snd_7480_);
                    lean_closure_set(v___f_7521_, 4, v___x_7478_);
                    v___x_7522_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_7480_, v___f_7521_, v___y_7504_, v___y_7505_, v___y_7506_, v___y_7507_);
                    if lean_obj_tag(v___x_7522_) == 0 {
                        v_a_7523_ = lean_ctor_get(v___x_7522_, 0);
                        lean_inc(v_a_7523_);
                        lean_dec_ref_known(v___x_7522_, 1);
                        v___x_7553_ = lean_nat_dec_lt(v___x_7500_, v___x_7501_);
                        if v___x_7553_ == 0 {
                            v___y_7525_ = v_fst_7502_;
                            state = 1;
                            continue;
                        } else {
                            v_fvarId_7554_ = lean_ctor_get(v_a_7523_, 0);
                            v_xs_x27_7555_ = lean_array_fset(v_fst_7502_, v___x_7500_, v___x_7503_);
                            lean_inc(v_fvarId_7554_);
                            v___x_7556_ =
                                lean_array_fset(v_xs_x27_7555_, v___x_7500_, v_fvarId_7554_);
                            v___y_7525_ = v___x_7556_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___y_7504_);
                        lean_dec_ref(v_fst_7502_);
                        lean_dec_ref(v_goalType_7499_);
                        lean_dec(v_numIndices_7498_);
                        lean_dec(v___x_7497_);
                        lean_dec(v___x_7496_);
                        lean_dec_ref(v___f_7495_);
                        lean_dec(v___x_7494_);
                        lean_dec_ref(v_a_7493_);
                        lean_dec_ref(v___x_7492_);
                        lean_dec_ref(v_args_7491_);
                        lean_dec_ref(v_params_7490_);
                        lean_dec(v___x_7489_);
                        lean_dec(v___x_7488_);
                        lean_dec(v___x_7486_);
                        lean_dec_ref(v_a_7485_);
                        lean_dec_ref(v___x_7484_);
                        lean_dec_ref(v___x_7483_);
                        lean_dec_ref(v___x_7481_);
                        v_a_7557_ = lean_ctor_get(v___x_7522_, 0);
                        v_isSharedCheck_7564_ = (!lean_is_exclusive(v___x_7522_)) as u8;
                        if v_isSharedCheck_7564_ == 0 {
                            v___x_7559_ = v___x_7522_;
                            v_isShared_7560_ = v_isSharedCheck_7564_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7557_);
                            lean_dec(v___x_7522_);
                            v___x_7559_ = lean_box(0);
                            v_isShared_7560_ = v_isSharedCheck_7564_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7504_);
                    lean_dec_ref(v_fst_7502_);
                    lean_dec_ref(v_goalType_7499_);
                    lean_dec(v_numIndices_7498_);
                    lean_dec(v___x_7497_);
                    lean_dec(v___x_7496_);
                    lean_dec_ref(v___f_7495_);
                    lean_dec(v___x_7494_);
                    lean_dec_ref(v_a_7493_);
                    lean_dec_ref(v___x_7492_);
                    lean_dec_ref(v_args_7491_);
                    lean_dec_ref(v_params_7490_);
                    lean_dec(v___x_7489_);
                    lean_dec(v___x_7488_);
                    lean_dec(v___x_7486_);
                    lean_dec_ref(v_a_7485_);
                    lean_dec_ref(v___x_7484_);
                    lean_dec_ref(v___x_7483_);
                    lean_dec_ref(v___x_7481_);
                    lean_dec(v_snd_7480_);
                    lean_dec(v___x_7478_);
                    v_a_7565_ = lean_ctor_get(v___x_7516_, 0);
                    v_isSharedCheck_7572_ = (!lean_is_exclusive(v___x_7516_)) as u8;
                    if v_isSharedCheck_7572_ == 0 {
                        v___x_7567_ = v___x_7516_;
                        v_isShared_7568_ = v_isSharedCheck_7572_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7565_);
                        lean_dec(v___x_7516_);
                        v___x_7567_ = lean_box(0);
                        v_isShared_7568_ = v_isSharedCheck_7572_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_mvarId_7526_ = lean_ctor_get(v_a_7523_, 1);
                lean_inc(v_mvarId_7526_);
                lean_dec(v_a_7523_);
                v___x_7527_ = l_Lean_MVarId_revert(
                    v_mvarId_7526_,
                    v___y_7525_,
                    v___x_7482_,
                    v___x_7482_,
                    v___y_7504_,
                    v___y_7505_,
                    v___y_7506_,
                    v___y_7507_,
                );
                if lean_obj_tag(v___x_7527_) == 0 {
                    v_a_7528_ = lean_ctor_get(v___x_7527_, 0);
                    lean_inc(v_a_7528_);
                    lean_dec_ref_known(v___x_7527_, 1);
                    v_snd_7529_ = lean_ctor_get(v_a_7528_, 1);
                    lean_inc(v_snd_7529_);
                    lean_dec(v_a_7528_);
                    v___x_7530_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_7529_, v___x_7483_, v___y_7505_);
                    if lean_obj_tag(v___x_7530_) == 0 {
                        v_isSharedCheck_7543_ = (!lean_is_exclusive(v___x_7530_)) as u8;
                        if v_isSharedCheck_7543_ == 0 {
                            v_unused_7544_ = lean_ctor_get(v___x_7530_, 0);
                            lean_dec(v_unused_7544_);
                            v___x_7532_ = v___x_7530_;
                            v_isShared_7533_ = v_isSharedCheck_7543_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_7530_);
                            v___x_7532_ = lean_box(0);
                            v_isShared_7533_ = v_isSharedCheck_7543_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___y_7504_);
                        lean_dec_ref(v_goalType_7499_);
                        lean_dec(v_numIndices_7498_);
                        lean_dec(v___x_7497_);
                        lean_dec(v___x_7496_);
                        lean_dec_ref(v___f_7495_);
                        lean_dec(v___x_7494_);
                        lean_dec_ref(v_a_7493_);
                        lean_dec_ref(v___x_7492_);
                        lean_dec_ref(v_args_7491_);
                        lean_dec_ref(v_params_7490_);
                        lean_dec(v___x_7489_);
                        lean_dec(v___x_7488_);
                        lean_dec(v___x_7486_);
                        lean_dec_ref(v_a_7485_);
                        lean_dec_ref(v___x_7484_);
                        lean_dec_ref(v___x_7481_);
                        return v___x_7530_;
                    }
                } else {
                    lean_dec_ref(v___y_7504_);
                    lean_dec_ref(v_goalType_7499_);
                    lean_dec(v_numIndices_7498_);
                    lean_dec(v___x_7497_);
                    lean_dec(v___x_7496_);
                    lean_dec_ref(v___f_7495_);
                    lean_dec(v___x_7494_);
                    lean_dec_ref(v_a_7493_);
                    lean_dec_ref(v___x_7492_);
                    lean_dec_ref(v_args_7491_);
                    lean_dec_ref(v_params_7490_);
                    lean_dec(v___x_7489_);
                    lean_dec(v___x_7488_);
                    lean_dec(v___x_7486_);
                    lean_dec_ref(v_a_7485_);
                    lean_dec_ref(v___x_7484_);
                    lean_dec_ref(v___x_7483_);
                    lean_dec_ref(v___x_7481_);
                    v_a_7545_ = lean_ctor_get(v___x_7527_, 0);
                    v_isSharedCheck_7552_ = (!lean_is_exclusive(v___x_7527_)) as u8;
                    if v_isSharedCheck_7552_ == 0 {
                        v___x_7547_ = v___x_7527_;
                        v_isShared_7548_ = v_isSharedCheck_7552_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_7545_);
                        lean_dec(v___x_7527_);
                        v___x_7547_ = lean_box(0);
                        v_isShared_7548_ = v_isSharedCheck_7552_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7534_ = l_Lean_Expr_app___override(v___x_7484_, v_a_7485_);
                v___x_7535_ = lean_box((v___x_7487_) as usize);
                v___x_7536_ = lean_box((v___x_7479_) as usize);
                v___x_7537_ = lean_box((v___x_7482_) as usize);
                v___f_7538_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed as *mut core::ffi::c_void, 23, 16);
                lean_closure_set(v___f_7538_, 0, v___x_7534_);
                lean_closure_set(v___f_7538_, 1, v___x_7486_);
                lean_closure_set(v___f_7538_, 2, v___x_7535_);
                lean_closure_set(v___f_7538_, 3, v___x_7488_);
                lean_closure_set(v___f_7538_, 4, v___x_7481_);
                lean_closure_set(v___f_7538_, 5, v___x_7536_);
                lean_closure_set(v___f_7538_, 6, v___x_7489_);
                lean_closure_set(v___f_7538_, 7, v_params_7490_);
                lean_closure_set(v___f_7538_, 8, v_args_7491_);
                lean_closure_set(v___f_7538_, 9, v___x_7537_);
                lean_closure_set(v___f_7538_, 10, v___x_7492_);
                lean_closure_set(v___f_7538_, 11, v_a_7493_);
                lean_closure_set(v___f_7538_, 12, v___x_7494_);
                lean_closure_set(v___f_7538_, 13, v___f_7495_);
                lean_closure_set(v___f_7538_, 14, v___x_7496_);
                lean_closure_set(v___f_7538_, 15, v___x_7497_);
                if v_isShared_7533_ == 0 {
                    lean_ctor_set_tag(v___x_7532_, 1);
                    lean_ctor_set(v___x_7532_, 0, v_numIndices_7498_);
                    v___x_7540_ = v___x_7532_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7542_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7542_, 0, v_numIndices_7498_);
                    v___x_7540_ = v_reuseFailAlloc_7542_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7541_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_7499_, v___x_7540_, v___f_7538_, v___x_7482_, v___x_7482_, v___y_7504_, v___y_7505_, v___y_7506_, v___y_7507_);
                lean_dec_ref(v___y_7504_);
                return v___x_7541_;
            }
            4 => {
                if v_isShared_7548_ == 0 {
                    v___x_7550_ = v___x_7547_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7551_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7551_, 0, v_a_7545_);
                    v___x_7550_ = v_reuseFailAlloc_7551_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7550_;
            }
            6 => {
                if v_isShared_7560_ == 0 {
                    v___x_7562_ = v___x_7559_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7563_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7563_, 0, v_a_7557_);
                    v___x_7562_ = v_reuseFailAlloc_7563_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7562_;
            }
            8 => {
                if v_isShared_7568_ == 0 {
                    v___x_7570_ = v___x_7567_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7571_, 0, v_a_7565_);
                    v___x_7570_ = v_reuseFailAlloc_7571_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7573_: *mut LeanObject = *_args.add(0);
    let mut v___x_7574_: *mut LeanObject = *_args.add(1);
    let mut v_snd_7575_: *mut LeanObject = *_args.add(2);
    let mut v___x_7576_: *mut LeanObject = *_args.add(3);
    let mut v___x_7577_: *mut LeanObject = *_args.add(4);
    let mut v___x_7578_: *mut LeanObject = *_args.add(5);
    let mut v___x_7579_: *mut LeanObject = *_args.add(6);
    let mut v_a_7580_: *mut LeanObject = *_args.add(7);
    let mut v___x_7581_: *mut LeanObject = *_args.add(8);
    let mut v___x_7582_: *mut LeanObject = *_args.add(9);
    let mut v___x_7583_: *mut LeanObject = *_args.add(10);
    let mut v___x_7584_: *mut LeanObject = *_args.add(11);
    let mut v_params_7585_: *mut LeanObject = *_args.add(12);
    let mut v_args_7586_: *mut LeanObject = *_args.add(13);
    let mut v___x_7587_: *mut LeanObject = *_args.add(14);
    let mut v_a_7588_: *mut LeanObject = *_args.add(15);
    let mut v___x_7589_: *mut LeanObject = *_args.add(16);
    let mut v___f_7590_: *mut LeanObject = *_args.add(17);
    let mut v___x_7591_: *mut LeanObject = *_args.add(18);
    let mut v___x_7592_: *mut LeanObject = *_args.add(19);
    let mut v_numIndices_7593_: *mut LeanObject = *_args.add(20);
    let mut v_goalType_7594_: *mut LeanObject = *_args.add(21);
    let mut v___x_7595_: *mut LeanObject = *_args.add(22);
    let mut v___x_7596_: *mut LeanObject = *_args.add(23);
    let mut v_fst_7597_: *mut LeanObject = *_args.add(24);
    let mut v___x_7598_: *mut LeanObject = *_args.add(25);
    let mut v___y_7599_: *mut LeanObject = *_args.add(26);
    let mut v___y_7600_: *mut LeanObject = *_args.add(27);
    let mut v___y_7601_: *mut LeanObject = *_args.add(28);
    let mut v___y_7602_: *mut LeanObject = *_args.add(29);
    let mut v___y_7603_: *mut LeanObject = *_args.add(30);
    let mut v___x_17231__boxed_7604_: u8 = 0;
    let mut v___x_17234__boxed_7605_: u8 = 0;
    let mut v___x_17239__boxed_7606_: u8 = 0;
    let mut v_res_7607_: *mut LeanObject = core::ptr::null_mut();
    v___x_17231__boxed_7604_ = (lean_unbox(v___x_7574_) as u8);
    v___x_17234__boxed_7605_ = (lean_unbox(v___x_7577_) as u8);
    v___x_17239__boxed_7606_ = (lean_unbox(v___x_7582_) as u8);
    v_res_7607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(v___x_7573_, v___x_17231__boxed_7604_, v_snd_7575_, v___x_7576_, v___x_17234__boxed_7605_, v___x_7578_, v___x_7579_, v_a_7580_, v___x_7581_, v___x_17239__boxed_7606_, v___x_7583_, v___x_7584_, v_params_7585_, v_args_7586_, v___x_7587_, v_a_7588_, v___x_7589_, v___f_7590_, v___x_7591_, v___x_7592_, v_numIndices_7593_, v_goalType_7594_, v___x_7595_, v___x_7596_, v_fst_7597_, v___x_7598_, v___y_7599_, v___y_7600_, v___y_7601_, v___y_7602_);
    lean_dec(v___y_7602_);
    lean_dec_ref(v___y_7601_);
    lean_dec(v___y_7600_);
    lean_dec(v___x_7596_);
    lean_dec(v___x_7595_);
    return v_res_7607_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(
    mut v___x_7608_: u8,
    mut v_x_7609_: *mut LeanObject,
) -> u8 {
    return v___x_7608_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(
    mut v___x_7610_: *mut LeanObject,
    mut v_x_7611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_17430__boxed_7612_: u8 = 0;
    let mut v_res_7613_: u8 = 0;
    let mut v_r_7614_: *mut LeanObject = core::ptr::null_mut();
    v___x_17430__boxed_7612_ = (lean_unbox(v___x_7610_) as u8);
    v_res_7613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_17430__boxed_7612_, v_x_7611_);
    lean_dec(v_x_7611_);
    v_r_7614_ = lean_box((v_res_7613_) as usize);
    return v_r_7614_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(
    mut v___x_7618_: *mut LeanObject,
    mut v_a_7619_: *mut LeanObject,
    mut v_numIndices_7620_: *mut LeanObject,
    mut v___x_7621_: *mut LeanObject,
    mut v___x_7622_: *mut LeanObject,
    mut v___x_7623_: *mut LeanObject,
    mut v___x_7624_: *mut LeanObject,
    mut v_params_7625_: *mut LeanObject,
    mut v___x_7626_: *mut LeanObject,
    mut v_a_7627_: *mut LeanObject,
    mut v___x_7628_: *mut LeanObject,
    mut v___x_7629_: *mut LeanObject,
    mut v___x_7630_: *mut LeanObject,
    mut v_args_7631_: *mut LeanObject,
    mut v_goalType_7632_: *mut LeanObject,
    mut v___y_7633_: *mut LeanObject,
    mut v___y_7634_: *mut LeanObject,
    mut v___y_7635_: *mut LeanObject,
    mut v___y_7636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7639_: u8 = 0;
    let mut v___x_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: u8 = 0;
    let mut v___x_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: u8 = 0;
    let mut v___x_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7669_: u8 = 0;
    let mut v___x_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7673_: u8 = 0;
    let mut v_a_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7677_: u8 = 0;
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7681_: u8 = 0;
    let mut v___x_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7638_ = lean_array_get_size(v_args_7631_);
                v___x_7639_ = lean_nat_dec_eq(v___x_7638_, v___x_7618_);
                if v___x_7639_ == 0 {
                    lean_dec_ref(v_goalType_7632_);
                    lean_dec_ref(v_args_7631_);
                    lean_dec(v___x_7629_);
                    lean_dec(v___x_7628_);
                    lean_dec_ref(v_a_7627_);
                    lean_dec_ref(v___x_7626_);
                    lean_dec_ref(v_params_7625_);
                    lean_dec_ref(v___x_7624_);
                    lean_dec_ref(v___x_7623_);
                    lean_dec(v___x_7621_);
                    lean_dec(v_numIndices_7620_);
                    lean_dec(v___x_7618_);
                    v___x_7640_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
                    v___x_7641_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_7640_, v___y_7633_, v___y_7634_, v___y_7635_, v___y_7636_);
                    return v___x_7641_;
                } else {
                    if lean_obj_tag(v_a_7619_) == 7 {
                        v_binderType_7642_ = lean_ctor_get(v_a_7619_, 1);
                        lean_inc_ref(v_binderType_7642_);
                        v___x_7643_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_7643_, 0, v_binderType_7642_);
                        v___x_7644_ = 0;
                        v___x_7645_ = lean_box(0);
                        v___x_7646_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_7643_,
                            v___x_7644_,
                            v___x_7645_,
                            v___y_7633_,
                            v___y_7634_,
                            v___y_7635_,
                            v___y_7636_,
                        );
                        if lean_obj_tag(v___x_7646_) == 0 {
                            v_a_7647_ = lean_ctor_get(v___x_7646_, 0);
                            lean_inc(v_a_7647_);
                            lean_dec_ref_known(v___x_7646_, 1);
                            v___x_7648_ = l_Lean_Expr_mvarId_x21(v_a_7647_);
                            v___x_7649_ = lean_nat_add(v_numIndices_7620_, v___x_7618_);
                            v___x_7650_ = lean_box(0);
                            v___x_7651_ = 0;
                            v___x_7652_ = l_Lean_Meta_introNCore(
                                v___x_7648_,
                                v___x_7649_,
                                v___x_7650_,
                                v___x_7651_,
                                v___x_7651_,
                                v___y_7633_,
                                v___y_7634_,
                                v___y_7635_,
                                v___y_7636_,
                            );
                            if lean_obj_tag(v___x_7652_) == 0 {
                                v_a_7653_ = lean_ctor_get(v___x_7652_, 0);
                                lean_inc(v_a_7653_);
                                lean_dec_ref_known(v___x_7652_, 1);
                                v_fst_7654_ = lean_ctor_get(v_a_7653_, 0);
                                lean_inc(v_fst_7654_);
                                v_snd_7655_ = lean_ctor_get(v_a_7653_, 1);
                                lean_inc_n(v_snd_7655_, 2);
                                lean_dec(v_a_7653_);
                                v___f_7656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0;
                                v___x_7657_ = lean_array_fget(v_args_7631_, v___x_7621_);
                                v___x_7658_ = lean_array_get_size(v_fst_7654_);
                                v___x_7659_ = lean_nat_sub(v___x_7658_, v___x_7618_);
                                v___x_7660_ = lean_array_get(v___x_7622_, v_fst_7654_, v___x_7659_);
                                v___x_7661_ = lean_box((v___x_7639_) as usize);
                                v___x_7662_ = lean_box((v___x_7651_) as usize);
                                v___x_7663_ = lean_box((v___x_7644_) as usize);
                                v___f_7664_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed as *mut core::ffi::c_void, 31, 26);
                                lean_closure_set(v___f_7664_, 0, v___x_7660_);
                                lean_closure_set(v___f_7664_, 1, v___x_7661_);
                                lean_closure_set(v___f_7664_, 2, v_snd_7655_);
                                lean_closure_set(v___f_7664_, 3, v___x_7623_);
                                lean_closure_set(v___f_7664_, 4, v___x_7662_);
                                lean_closure_set(v___f_7664_, 5, v___x_7657_);
                                lean_closure_set(v___f_7664_, 6, v___x_7624_);
                                lean_closure_set(v___f_7664_, 7, v_a_7647_);
                                lean_closure_set(v___f_7664_, 8, v___x_7618_);
                                lean_closure_set(v___f_7664_, 9, v___x_7663_);
                                lean_closure_set(v___f_7664_, 10, v___x_7645_);
                                lean_closure_set(v___f_7664_, 11, v___x_7621_);
                                lean_closure_set(v___f_7664_, 12, v_params_7625_);
                                lean_closure_set(v___f_7664_, 13, v_args_7631_);
                                lean_closure_set(v___f_7664_, 14, v___x_7626_);
                                lean_closure_set(v___f_7664_, 15, v_a_7627_);
                                lean_closure_set(v___f_7664_, 16, v___x_7628_);
                                lean_closure_set(v___f_7664_, 17, v___f_7656_);
                                lean_closure_set(v___f_7664_, 18, v___x_7650_);
                                lean_closure_set(v___f_7664_, 19, v___x_7629_);
                                lean_closure_set(v___f_7664_, 20, v_numIndices_7620_);
                                lean_closure_set(v___f_7664_, 21, v_goalType_7632_);
                                lean_closure_set(v___f_7664_, 22, v___x_7659_);
                                lean_closure_set(v___f_7664_, 23, v___x_7658_);
                                lean_closure_set(v___f_7664_, 24, v_fst_7654_);
                                lean_closure_set(v___f_7664_, 25, v___x_7630_);
                                v___x_7665_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_7655_, v___f_7664_, v___y_7633_, v___y_7634_, v___y_7635_, v___y_7636_);
                                return v___x_7665_;
                            } else {
                                lean_dec(v_a_7647_);
                                lean_dec_ref(v_goalType_7632_);
                                lean_dec_ref(v_args_7631_);
                                lean_dec(v___x_7629_);
                                lean_dec(v___x_7628_);
                                lean_dec_ref(v_a_7627_);
                                lean_dec_ref(v___x_7626_);
                                lean_dec_ref(v_params_7625_);
                                lean_dec_ref(v___x_7624_);
                                lean_dec_ref(v___x_7623_);
                                lean_dec(v___x_7621_);
                                lean_dec(v_numIndices_7620_);
                                lean_dec(v___x_7618_);
                                v_a_7666_ = lean_ctor_get(v___x_7652_, 0);
                                v_isSharedCheck_7673_ = (!lean_is_exclusive(v___x_7652_)) as u8;
                                if v_isSharedCheck_7673_ == 0 {
                                    v___x_7668_ = v___x_7652_;
                                    v_isShared_7669_ = v_isSharedCheck_7673_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_7666_);
                                    lean_dec(v___x_7652_);
                                    v___x_7668_ = lean_box(0);
                                    v_isShared_7669_ = v_isSharedCheck_7673_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_goalType_7632_);
                            lean_dec_ref(v_args_7631_);
                            lean_dec(v___x_7629_);
                            lean_dec(v___x_7628_);
                            lean_dec_ref(v_a_7627_);
                            lean_dec_ref(v___x_7626_);
                            lean_dec_ref(v_params_7625_);
                            lean_dec_ref(v___x_7624_);
                            lean_dec_ref(v___x_7623_);
                            lean_dec(v___x_7621_);
                            lean_dec(v_numIndices_7620_);
                            lean_dec(v___x_7618_);
                            v_a_7674_ = lean_ctor_get(v___x_7646_, 0);
                            v_isSharedCheck_7681_ = (!lean_is_exclusive(v___x_7646_)) as u8;
                            if v_isSharedCheck_7681_ == 0 {
                                v___x_7676_ = v___x_7646_;
                                v_isShared_7677_ = v_isSharedCheck_7681_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_7674_);
                                lean_dec(v___x_7646_);
                                v___x_7676_ = lean_box(0);
                                v_isShared_7677_ = v_isSharedCheck_7681_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_goalType_7632_);
                        lean_dec_ref(v_args_7631_);
                        lean_dec(v___x_7629_);
                        lean_dec(v___x_7628_);
                        lean_dec_ref(v_a_7627_);
                        lean_dec_ref(v___x_7626_);
                        lean_dec_ref(v_params_7625_);
                        lean_dec_ref(v___x_7624_);
                        lean_dec_ref(v___x_7623_);
                        lean_dec(v___x_7621_);
                        lean_dec(v_numIndices_7620_);
                        lean_dec(v___x_7618_);
                        v___x_7682_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
                        v___x_7683_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_7682_, v___y_7633_, v___y_7634_, v___y_7635_, v___y_7636_);
                        return v___x_7683_;
                    }
                }
            }
            1 => {
                if v_isShared_7669_ == 0 {
                    v___x_7671_ = v___x_7668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7672_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7672_, 0, v_a_7666_);
                    v___x_7671_ = v_reuseFailAlloc_7672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7671_;
            }
            3 => {
                if v_isShared_7677_ == 0 {
                    v___x_7679_ = v___x_7676_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7680_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7680_, 0, v_a_7674_);
                    v___x_7679_ = v_reuseFailAlloc_7680_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7684_: *mut LeanObject = *_args.add(0);
    let mut v_a_7685_: *mut LeanObject = *_args.add(1);
    let mut v_numIndices_7686_: *mut LeanObject = *_args.add(2);
    let mut v___x_7687_: *mut LeanObject = *_args.add(3);
    let mut v___x_7688_: *mut LeanObject = *_args.add(4);
    let mut v___x_7689_: *mut LeanObject = *_args.add(5);
    let mut v___x_7690_: *mut LeanObject = *_args.add(6);
    let mut v_params_7691_: *mut LeanObject = *_args.add(7);
    let mut v___x_7692_: *mut LeanObject = *_args.add(8);
    let mut v_a_7693_: *mut LeanObject = *_args.add(9);
    let mut v___x_7694_: *mut LeanObject = *_args.add(10);
    let mut v___x_7695_: *mut LeanObject = *_args.add(11);
    let mut v___x_7696_: *mut LeanObject = *_args.add(12);
    let mut v_args_7697_: *mut LeanObject = *_args.add(13);
    let mut v_goalType_7698_: *mut LeanObject = *_args.add(14);
    let mut v___y_7699_: *mut LeanObject = *_args.add(15);
    let mut v___y_7700_: *mut LeanObject = *_args.add(16);
    let mut v___y_7701_: *mut LeanObject = *_args.add(17);
    let mut v___y_7702_: *mut LeanObject = *_args.add(18);
    let mut v___y_7703_: *mut LeanObject = *_args.add(19);
    let mut v_res_7704_: *mut LeanObject = core::ptr::null_mut();
    v_res_7704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(v___x_7684_, v_a_7685_, v_numIndices_7686_, v___x_7687_, v___x_7688_, v___x_7689_, v___x_7690_, v_params_7691_, v___x_7692_, v_a_7693_, v___x_7694_, v___x_7695_, v___x_7696_, v_args_7697_, v_goalType_7698_, v___y_7699_, v___y_7700_, v___y_7701_, v___y_7702_);
    lean_dec(v___y_7702_);
    lean_dec_ref(v___y_7701_);
    lean_dec(v___y_7700_);
    lean_dec_ref(v___y_7699_);
    lean_dec(v___x_7688_);
    lean_dec_ref(v_a_7685_);
    return v_res_7704_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(
    mut v_constName_7705_: *mut LeanObject,
    mut v___y_7706_: *mut LeanObject,
    mut v___y_7707_: *mut LeanObject,
    mut v___y_7708_: *mut LeanObject,
    mut v___y_7709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: u8 = 0;
    let mut v___x_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7719_: u8 = 0;
    let mut v___x_7721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7711_ = lean_st_ref_get(v___y_7709_);
                v_env_7712_ = lean_ctor_get(v___x_7711_, 0);
                lean_inc_ref(v_env_7712_);
                lean_dec(v___x_7711_);
                v___x_7713_ = 0;
                lean_inc(v_constName_7705_);
                v___x_7714_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_7712_,
                    v_constName_7705_,
                    v___x_7713_,
                );
                if lean_obj_tag(v___x_7714_) == 0 {
                    v___x_7715_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_7705_, v___y_7706_, v___y_7707_, v___y_7708_, v___y_7709_);
                    return v___x_7715_;
                } else {
                    lean_dec(v_constName_7705_);
                    v_val_7716_ = lean_ctor_get(v___x_7714_, 0);
                    v_isSharedCheck_7723_ = (!lean_is_exclusive(v___x_7714_)) as u8;
                    if v_isSharedCheck_7723_ == 0 {
                        v___x_7718_ = v___x_7714_;
                        v_isShared_7719_ = v_isSharedCheck_7723_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_7716_);
                        lean_dec(v___x_7714_);
                        v___x_7718_ = lean_box(0);
                        v_isShared_7719_ = v_isSharedCheck_7723_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7719_ == 0 {
                    lean_ctor_set_tag(v___x_7718_, 0);
                    v___x_7721_ = v___x_7718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7722_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7722_, 0, v_val_7716_);
                    v___x_7721_ = v_reuseFailAlloc_7722_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(
    mut v_constName_7724_: *mut LeanObject,
    mut v___y_7725_: *mut LeanObject,
    mut v___y_7726_: *mut LeanObject,
    mut v___y_7727_: *mut LeanObject,
    mut v___y_7728_: *mut LeanObject,
    mut v___y_7729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7730_: *mut LeanObject = core::ptr::null_mut();
    v_res_7730_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_7724_, v___y_7725_, v___y_7726_, v___y_7727_, v___y_7728_);
    lean_dec(v___y_7728_);
    lean_dec_ref(v___y_7727_);
    lean_dec(v___y_7726_);
    lean_dec_ref(v___y_7725_);
    return v_res_7730_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(
    mut v_constName_7731_: *mut LeanObject,
    mut v___y_7732_: *mut LeanObject,
    mut v___y_7733_: *mut LeanObject,
    mut v___y_7734_: *mut LeanObject,
    mut v___y_7735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7741_: u8 = 0;
    let mut v_levelParams_7742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7749_: u8 = 0;
    let mut v_a_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7753_: u8 = 0;
    let mut v___x_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_7731_);
                v___x_7737_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_7731_, v___y_7732_, v___y_7733_, v___y_7734_, v___y_7735_);
                if lean_obj_tag(v___x_7737_) == 0 {
                    v_a_7738_ = lean_ctor_get(v___x_7737_, 0);
                    v_isSharedCheck_7749_ = (!lean_is_exclusive(v___x_7737_)) as u8;
                    if v_isSharedCheck_7749_ == 0 {
                        v___x_7740_ = v___x_7737_;
                        v_isShared_7741_ = v_isSharedCheck_7749_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7738_);
                        lean_dec(v___x_7737_);
                        v___x_7740_ = lean_box(0);
                        v_isShared_7741_ = v_isSharedCheck_7749_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_7731_);
                    v_a_7750_ = lean_ctor_get(v___x_7737_, 0);
                    v_isSharedCheck_7757_ = (!lean_is_exclusive(v___x_7737_)) as u8;
                    if v_isSharedCheck_7757_ == 0 {
                        v___x_7752_ = v___x_7737_;
                        v_isShared_7753_ = v_isSharedCheck_7757_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7750_);
                        lean_dec(v___x_7737_);
                        v___x_7752_ = lean_box(0);
                        v_isShared_7753_ = v_isSharedCheck_7757_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_7742_ = lean_ctor_get(v_a_7738_, 1);
                lean_inc(v_levelParams_7742_);
                lean_dec(v_a_7738_);
                v___x_7743_ = lean_box(0);
                v___x_7744_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_7742_, v___x_7743_);
                v___x_7745_ = l_Lean_mkConst(v_constName_7731_, v___x_7744_);
                if v_isShared_7741_ == 0 {
                    lean_ctor_set(v___x_7740_, 0, v___x_7745_);
                    v___x_7747_ = v___x_7740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7748_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7748_, 0, v___x_7745_);
                    v___x_7747_ = v_reuseFailAlloc_7748_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7747_;
            }
            3 => {
                if v_isShared_7753_ == 0 {
                    v___x_7755_ = v___x_7752_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7756_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7756_, 0, v_a_7750_);
                    v___x_7755_ = v_reuseFailAlloc_7756_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(
    mut v_constName_7758_: *mut LeanObject,
    mut v___y_7759_: *mut LeanObject,
    mut v___y_7760_: *mut LeanObject,
    mut v___y_7761_: *mut LeanObject,
    mut v___y_7762_: *mut LeanObject,
    mut v___y_7763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7764_: *mut LeanObject = core::ptr::null_mut();
    v_res_7764_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_7758_, v___y_7759_, v___y_7760_, v___y_7761_, v___y_7762_);
    lean_dec(v___y_7762_);
    lean_dec_ref(v___y_7761_);
    lean_dec(v___y_7760_);
    lean_dec_ref(v___y_7759_);
    return v_res_7764_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(
    mut v_levels_7767_: *mut LeanObject,
    mut v_params_7768_: *mut LeanObject,
    mut v___y_7769_: *mut LeanObject,
    mut v_predicates_7770_: *mut LeanObject,
    mut v_as_7771_: *mut LeanObject,
    mut v_sz_7772_: usize,
    mut v_i_7773_: usize,
    mut v_b_7774_: *mut LeanObject,
    mut v___y_7775_: *mut LeanObject,
    mut v___y_7776_: *mut LeanObject,
    mut v___y_7777_: *mut LeanObject,
    mut v___y_7778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7780_: u8 = 0;
    let mut v___x_7781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_7783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_7786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: u8 = 0;
    let mut v___x_7811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: usize = 0;
    let mut v___x_7813_: usize = 0;
    let mut v_a_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7818_: u8 = 0;
    let mut v___x_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7822_: u8 = 0;
    let mut v_a_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7826_: u8 = 0;
    let mut v___x_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7830_: u8 = 0;
    let mut v_a_7831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7834_: u8 = 0;
    let mut v___x_7836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7838_: u8 = 0;
    let mut v_a_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7842_: u8 = 0;
    let mut v___x_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7780_ = lean_usize_dec_lt(v_i_7773_, v_sz_7772_);
                if v___x_7780_ == 0 {
                    lean_dec_ref(v___y_7769_);
                    lean_dec_ref(v_params_7768_);
                    lean_dec(v_levels_7767_);
                    v___x_7781_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7781_, 0, v_b_7774_);
                    return v___x_7781_;
                } else {
                    v_a_7782_ = lean_array_uget_borrowed(v_as_7771_, v_i_7773_);
                    v_toConstantVal_7783_ = lean_ctor_get(v_a_7782_, 0);
                    v_numParams_7784_ = lean_ctor_get(v_a_7782_, 1);
                    v_numIndices_7785_ = lean_ctor_get(v_a_7782_, 2);
                    v_name_7786_ = lean_ctor_get(v_toConstantVal_7783_, 0);
                    lean_inc(v_name_7786_);
                    v___x_7787_ = l_Lean_mkCasesOnName(v_name_7786_);
                    lean_inc(v___x_7787_);
                    v___x_7788_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_7787_, v___y_7775_, v___y_7776_, v___y_7777_, v___y_7778_);
                    if lean_obj_tag(v___x_7788_) == 0 {
                        v_a_7789_ = lean_ctor_get(v___x_7788_, 0);
                        lean_inc(v_a_7789_);
                        lean_dec_ref_known(v___x_7788_, 1);
                        v___x_7790_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_7787_, v___y_7775_, v___y_7776_, v___y_7777_, v___y_7778_);
                        if lean_obj_tag(v___x_7790_) == 0 {
                            v_a_7791_ = lean_ctor_get(v___x_7790_, 0);
                            lean_inc(v_a_7791_);
                            lean_dec_ref_known(v___x_7790_, 1);
                            lean_inc_ref(v_params_7768_);
                            v___x_7792_ =
                                l_Array_append___redArg(v_params_7768_, v_predicates_7770_);
                            v___x_7793_ = l_Lean_mkAppN(v_a_7791_, v___x_7792_);
                            lean_dec_ref(v___x_7792_);
                            lean_inc(v___y_7778_);
                            lean_inc_ref(v___y_7777_);
                            lean_inc(v___y_7776_);
                            lean_inc_ref(v___y_7775_);
                            lean_inc_ref(v___x_7793_);
                            v___x_7794_ = lean_infer_type(
                                v___x_7793_,
                                v___y_7775_,
                                v___y_7776_,
                                v___y_7777_,
                                v___y_7778_,
                            );
                            if lean_obj_tag(v___x_7794_) == 0 {
                                v_a_7795_ = lean_ctor_get(v___x_7794_, 0);
                                lean_inc(v_a_7795_);
                                lean_dec_ref_known(v___x_7794_, 1);
                                lean_inc(v___y_7778_);
                                lean_inc_ref(v___y_7777_);
                                lean_inc(v___y_7776_);
                                lean_inc_ref(v___y_7775_);
                                lean_inc_ref(v___x_7793_);
                                v___x_7796_ = lean_infer_type(
                                    v___x_7793_,
                                    v___y_7775_,
                                    v___y_7776_,
                                    v___y_7777_,
                                    v___y_7778_,
                                );
                                if lean_obj_tag(v___x_7796_) == 0 {
                                    v_a_7797_ = lean_ctor_get(v___x_7796_, 0);
                                    lean_inc(v_a_7797_);
                                    lean_dec_ref_known(v___x_7796_, 1);
                                    v___x_7798_ = lean_unsigned_to_nat(0);
                                    v___x_7799_ = lean_box(0);
                                    v___x_7800_ = lean_box(0);
                                    lean_inc_ref(v___y_7769_);
                                    lean_inc_ref_n(v_params_7768_, 2);
                                    lean_inc_n(v_levels_7767_, 2);
                                    lean_inc_n(v_name_7786_, 2);
                                    lean_inc(v_numParams_7784_);
                                    v___f_7801_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed as *mut core::ffi::c_void, 7, 6);
                                    lean_closure_set(v___f_7801_, 0, v_numParams_7784_);
                                    lean_closure_set(v___f_7801_, 1, v_name_7786_);
                                    lean_closure_set(v___f_7801_, 2, v_levels_7767_);
                                    lean_closure_set(v___f_7801_, 3, v_params_7768_);
                                    lean_closure_set(v___f_7801_, 4, v___y_7769_);
                                    lean_closure_set(v___f_7801_, 5, v___x_7798_);
                                    v___x_7802_ = lean_replace_expr(v___f_7801_, v_a_7795_);
                                    lean_dec(v_a_7795_);
                                    lean_dec_ref(v___f_7801_);
                                    v___x_7803_ =
                                        l_Lean_Elab_Command_removeFunctorPostfix(v_name_7786_);
                                    v___x_7804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1;
                                    lean_inc(v___x_7803_);
                                    v___x_7805_ = l_Lean_Name_append(v___x_7803_, v___x_7804_);
                                    v___x_7806_ = l_Lean_mkConst(v___x_7805_, v_levels_7767_);
                                    v___x_7807_ = lean_unsigned_to_nat(1);
                                    v___x_7808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0;
                                    lean_inc_ref(v___x_7802_);
                                    lean_inc(v_numIndices_7785_);
                                    v___f_7809_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed as *mut core::ffi::c_void, 20, 13);
                                    lean_closure_set(v___f_7809_, 0, v___x_7807_);
                                    lean_closure_set(v___f_7809_, 1, v_a_7797_);
                                    lean_closure_set(v___f_7809_, 2, v_numIndices_7785_);
                                    lean_closure_set(v___f_7809_, 3, v___x_7798_);
                                    lean_closure_set(v___f_7809_, 4, v___x_7799_);
                                    lean_closure_set(v___f_7809_, 5, v___x_7806_);
                                    lean_closure_set(v___f_7809_, 6, v___x_7793_);
                                    lean_closure_set(v___f_7809_, 7, v_params_7768_);
                                    lean_closure_set(v___f_7809_, 8, v___x_7802_);
                                    lean_closure_set(v___f_7809_, 9, v_a_7789_);
                                    lean_closure_set(v___f_7809_, 10, v___x_7803_);
                                    lean_closure_set(v___f_7809_, 11, v___x_7808_);
                                    lean_closure_set(v___f_7809_, 12, v___x_7800_);
                                    v___x_7810_ = 0;
                                    v___x_7811_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v___x_7802_, v___x_7808_, v___f_7809_, v___x_7810_, v___x_7810_, v___y_7775_, v___y_7776_, v___y_7777_, v___y_7778_);
                                    if lean_obj_tag(v___x_7811_) == 0 {
                                        lean_dec_ref_known(v___x_7811_, 1);
                                        v___x_7812_ = 1usize;
                                        v___x_7813_ = lean_usize_add(v_i_7773_, v___x_7812_);
                                        v_i_7773_ = v___x_7813_;
                                        v_b_7774_ = v___x_7800_;
                                        state = 0;
                                        continue;
                                    } else {
                                        lean_dec_ref(v___y_7769_);
                                        lean_dec_ref(v_params_7768_);
                                        lean_dec(v_levels_7767_);
                                        return v___x_7811_;
                                    }
                                } else {
                                    lean_dec(v_a_7795_);
                                    lean_dec_ref(v___x_7793_);
                                    lean_dec(v_a_7789_);
                                    lean_dec_ref(v___y_7769_);
                                    lean_dec_ref(v_params_7768_);
                                    lean_dec(v_levels_7767_);
                                    v_a_7815_ = lean_ctor_get(v___x_7796_, 0);
                                    v_isSharedCheck_7822_ = (!lean_is_exclusive(v___x_7796_)) as u8;
                                    if v_isSharedCheck_7822_ == 0 {
                                        v___x_7817_ = v___x_7796_;
                                        v_isShared_7818_ = v_isSharedCheck_7822_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7815_);
                                        lean_dec(v___x_7796_);
                                        v___x_7817_ = lean_box(0);
                                        v_isShared_7818_ = v_isSharedCheck_7822_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_7793_);
                                lean_dec(v_a_7789_);
                                lean_dec_ref(v___y_7769_);
                                lean_dec_ref(v_params_7768_);
                                lean_dec(v_levels_7767_);
                                v_a_7823_ = lean_ctor_get(v___x_7794_, 0);
                                v_isSharedCheck_7830_ = (!lean_is_exclusive(v___x_7794_)) as u8;
                                if v_isSharedCheck_7830_ == 0 {
                                    v___x_7825_ = v___x_7794_;
                                    v_isShared_7826_ = v_isSharedCheck_7830_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_7823_);
                                    lean_dec(v___x_7794_);
                                    v___x_7825_ = lean_box(0);
                                    v_isShared_7826_ = v_isSharedCheck_7830_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_7789_);
                            lean_dec_ref(v___y_7769_);
                            lean_dec_ref(v_params_7768_);
                            lean_dec(v_levels_7767_);
                            v_a_7831_ = lean_ctor_get(v___x_7790_, 0);
                            v_isSharedCheck_7838_ = (!lean_is_exclusive(v___x_7790_)) as u8;
                            if v_isSharedCheck_7838_ == 0 {
                                v___x_7833_ = v___x_7790_;
                                v_isShared_7834_ = v_isSharedCheck_7838_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_7831_);
                                lean_dec(v___x_7790_);
                                v___x_7833_ = lean_box(0);
                                v_isShared_7834_ = v_isSharedCheck_7838_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_7787_);
                        lean_dec_ref(v___y_7769_);
                        lean_dec_ref(v_params_7768_);
                        lean_dec(v_levels_7767_);
                        v_a_7839_ = lean_ctor_get(v___x_7788_, 0);
                        v_isSharedCheck_7846_ = (!lean_is_exclusive(v___x_7788_)) as u8;
                        if v_isSharedCheck_7846_ == 0 {
                            v___x_7841_ = v___x_7788_;
                            v_isShared_7842_ = v_isSharedCheck_7846_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_7839_);
                            lean_dec(v___x_7788_);
                            v___x_7841_ = lean_box(0);
                            v_isShared_7842_ = v_isSharedCheck_7846_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7818_ == 0 {
                    v___x_7820_ = v___x_7817_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7821_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7821_, 0, v_a_7815_);
                    v___x_7820_ = v_reuseFailAlloc_7821_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7820_;
            }
            3 => {
                if v_isShared_7826_ == 0 {
                    v___x_7828_ = v___x_7825_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7829_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7829_, 0, v_a_7823_);
                    v___x_7828_ = v_reuseFailAlloc_7829_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7828_;
            }
            5 => {
                if v_isShared_7834_ == 0 {
                    v___x_7836_ = v___x_7833_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7837_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7837_, 0, v_a_7831_);
                    v___x_7836_ = v_reuseFailAlloc_7837_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7836_;
            }
            7 => {
                if v_isShared_7842_ == 0 {
                    v___x_7844_ = v___x_7841_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7845_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7845_, 0, v_a_7839_);
                    v___x_7844_ = v_reuseFailAlloc_7845_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(
    mut v_levels_7847_: *mut LeanObject,
    mut v_params_7848_: *mut LeanObject,
    mut v___y_7849_: *mut LeanObject,
    mut v_predicates_7850_: *mut LeanObject,
    mut v_as_7851_: *mut LeanObject,
    mut v_sz_7852_: *mut LeanObject,
    mut v_i_7853_: *mut LeanObject,
    mut v_b_7854_: *mut LeanObject,
    mut v___y_7855_: *mut LeanObject,
    mut v___y_7856_: *mut LeanObject,
    mut v___y_7857_: *mut LeanObject,
    mut v___y_7858_: *mut LeanObject,
    mut v___y_7859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7860_: usize = 0;
    let mut v_i_boxed_7861_: usize = 0;
    let mut v_res_7862_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7860_ = lean_unbox_usize(v_sz_7852_);
    lean_dec(v_sz_7852_);
    v_i_boxed_7861_ = lean_unbox_usize(v_i_7853_);
    lean_dec(v_i_7853_);
    v_res_7862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_7847_, v_params_7848_, v___y_7849_, v_predicates_7850_, v_as_7851_, v_sz_boxed_7860_, v_i_boxed_7861_, v_b_7854_, v___y_7855_, v___y_7856_, v___y_7857_, v___y_7858_);
    lean_dec(v___y_7858_);
    lean_dec_ref(v___y_7857_);
    lean_dec(v___y_7856_);
    lean_dec_ref(v___y_7855_);
    lean_dec_ref(v_as_7851_);
    lean_dec_ref(v_predicates_7850_);
    return v_res_7862_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(
    mut v_levels_7863_: *mut LeanObject,
    mut v_sz_7864_: usize,
    mut v_i_7865_: usize,
    mut v_bs_7866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7867_: u8 = 0;
    let mut v_v_7868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_7869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_7870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7875_: usize = 0;
    let mut v___x_7876_: usize = 0;
    let mut v___x_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7867_ = lean_usize_dec_lt(v_i_7865_, v_sz_7864_);
                if v___x_7867_ == 0 {
                    lean_dec(v_levels_7863_);
                    return v_bs_7866_;
                } else {
                    v_v_7868_ = lean_array_uget_borrowed(v_bs_7866_, v_i_7865_);
                    v_toConstantVal_7869_ = lean_ctor_get(v_v_7868_, 0);
                    v_name_7870_ = lean_ctor_get(v_toConstantVal_7869_, 0);
                    lean_inc(v_name_7870_);
                    v___x_7871_ = lean_unsigned_to_nat(0);
                    v_bs_x27_7872_ = lean_array_uset(v_bs_7866_, v_i_7865_, v___x_7871_);
                    v___x_7873_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_7870_);
                    lean_inc(v_levels_7863_);
                    v___x_7874_ = l_Lean_mkConst(v___x_7873_, v_levels_7863_);
                    v___x_7875_ = 1usize;
                    v___x_7876_ = lean_usize_add(v_i_7865_, v___x_7875_);
                    v___x_7877_ = lean_array_uset(v_bs_x27_7872_, v_i_7865_, v___x_7874_);
                    v_i_7865_ = v___x_7876_;
                    v_bs_7866_ = v___x_7877_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(
    mut v_levels_7879_: *mut LeanObject,
    mut v_sz_7880_: *mut LeanObject,
    mut v_i_7881_: *mut LeanObject,
    mut v_bs_7882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7883_: usize = 0;
    let mut v_i_boxed_7884_: usize = 0;
    let mut v_res_7885_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7883_ = lean_unbox_usize(v_sz_7880_);
    lean_dec(v_sz_7880_);
    v_i_boxed_7884_ = lean_unbox_usize(v_i_7881_);
    lean_dec(v_i_7881_);
    v_res_7885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_7879_, v_sz_boxed_7883_, v_i_boxed_7884_, v_bs_7882_);
    return v_res_7885_;
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(
    mut v_infos_7886_: *mut LeanObject,
    mut v_levels_7887_: *mut LeanObject,
    mut v___y_7888_: *mut LeanObject,
    mut v_params_7889_: *mut LeanObject,
    mut v_x_7890_: *mut LeanObject,
    mut v___y_7891_: *mut LeanObject,
    mut v___y_7892_: *mut LeanObject,
    mut v___y_7893_: *mut LeanObject,
    mut v___y_7894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_7896_: usize = 0;
    let mut v___x_7897_: usize = 0;
    let mut v_predicates_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7899_: usize = 0;
    let mut v_predicates_7900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7905_: u8 = 0;
    let mut v___x_7907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7909_: u8 = 0;
    let mut v_unused_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_7896_ = lean_array_size(v_infos_7886_);
                v___x_7897_ = 0usize;
                lean_inc_ref(v_infos_7886_);
                lean_inc(v_levels_7887_);
                v_predicates_7898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_7887_, v_sz_7896_, v___x_7897_, v_infos_7886_);
                v_sz_7899_ = lean_array_size(v_predicates_7898_);
                v_predicates_7900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_7889_, v_sz_7899_, v___x_7897_, v_predicates_7898_);
                v___x_7901_ = lean_box(0);
                v___x_7902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_7887_, v_params_7889_, v___y_7888_, v_predicates_7900_, v_infos_7886_, v_sz_7896_, v___x_7897_, v___x_7901_, v___y_7891_, v___y_7892_, v___y_7893_, v___y_7894_);
                lean_dec_ref(v_infos_7886_);
                lean_dec_ref(v_predicates_7900_);
                if lean_obj_tag(v___x_7902_) == 0 {
                    v_isSharedCheck_7909_ = (!lean_is_exclusive(v___x_7902_)) as u8;
                    if v_isSharedCheck_7909_ == 0 {
                        v_unused_7910_ = lean_ctor_get(v___x_7902_, 0);
                        lean_dec(v_unused_7910_);
                        v___x_7904_ = v___x_7902_;
                        v_isShared_7905_ = v_isSharedCheck_7909_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_7902_);
                        v___x_7904_ = lean_box(0);
                        v_isShared_7905_ = v_isSharedCheck_7909_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_7902_;
                }
            }
            1 => {
                if v_isShared_7905_ == 0 {
                    lean_ctor_set(v___x_7904_, 0, v___x_7901_);
                    v___x_7907_ = v___x_7904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7908_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7908_, 0, v___x_7901_);
                    v___x_7907_ = v_reuseFailAlloc_7908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(
    mut v_infos_7911_: *mut LeanObject,
    mut v_levels_7912_: *mut LeanObject,
    mut v___y_7913_: *mut LeanObject,
    mut v_params_7914_: *mut LeanObject,
    mut v_x_7915_: *mut LeanObject,
    mut v___y_7916_: *mut LeanObject,
    mut v___y_7917_: *mut LeanObject,
    mut v___y_7918_: *mut LeanObject,
    mut v___y_7919_: *mut LeanObject,
    mut v___y_7920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7921_: *mut LeanObject = core::ptr::null_mut();
    v_res_7921_ =
        l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(
            v_infos_7911_,
            v_levels_7912_,
            v___y_7913_,
            v_params_7914_,
            v_x_7915_,
            v___y_7916_,
            v___y_7917_,
            v___y_7918_,
            v___y_7919_,
        );
    lean_dec(v___y_7919_);
    lean_dec_ref(v___y_7918_);
    lean_dec(v___y_7917_);
    lean_dec_ref(v___y_7916_);
    lean_dec_ref(v_x_7915_);
    return v_res_7921_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(
    mut v_as_7922_: *mut LeanObject,
    mut v_i_7923_: usize,
    mut v_stop_7924_: usize,
    mut v_b_7925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7926_: u8 = 0;
    let mut v___x_7927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_7928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: usize = 0;
    let mut v___x_7932_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7926_ = lean_usize_dec_eq(v_i_7923_, v_stop_7924_);
                if v___x_7926_ == 0 {
                    v___x_7927_ = lean_array_uget_borrowed(v_as_7922_, v_i_7923_);
                    v_ctors_7928_ = lean_ctor_get(v___x_7927_, 4);
                    lean_inc(v_ctors_7928_);
                    v___x_7929_ = lean_array_mk(v_ctors_7928_);
                    v___x_7930_ = l_Array_append___redArg(v_b_7925_, v___x_7929_);
                    lean_dec_ref(v___x_7929_);
                    v___x_7931_ = 1usize;
                    v___x_7932_ = lean_usize_add(v_i_7923_, v___x_7931_);
                    v_i_7923_ = v___x_7932_;
                    v_b_7925_ = v___x_7930_;
                    state = 0;
                    continue;
                } else {
                    return v_b_7925_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(
    mut v_as_7934_: *mut LeanObject,
    mut v_i_7935_: *mut LeanObject,
    mut v_stop_7936_: *mut LeanObject,
    mut v_b_7937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7938_: usize = 0;
    let mut v_stop_boxed_7939_: usize = 0;
    let mut v_res_7940_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7938_ = lean_unbox_usize(v_i_7935_);
    lean_dec(v_i_7935_);
    v_stop_boxed_7939_ = lean_unbox_usize(v_stop_7936_);
    lean_dec(v_stop_7936_);
    v_res_7940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_7934_, v_i_boxed_7938_, v_stop_boxed_7939_, v_b_7937_);
    lean_dec_ref(v_as_7934_);
    return v_res_7940_;
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(
    mut v_infos_7943_: *mut LeanObject,
    mut v_a_7944_: *mut LeanObject,
    mut v_a_7945_: *mut LeanObject,
    mut v_a_7946_: *mut LeanObject,
    mut v_a_7947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_7952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_7953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_7954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levels_7957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: u8 = 0;
    let mut v___x_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: u8 = 0;
    let mut v___x_7969_: u8 = 0;
    let mut v___x_7970_: usize = 0;
    let mut v___x_7971_: usize = 0;
    let mut v___x_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7973_: usize = 0;
    let mut v___x_7974_: usize = 0;
    let mut v___x_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7949_ = l_Lean_instInhabitedInductiveVal_default;
                v___x_7950_ = lean_unsigned_to_nat(0);
                v___x_7951_ = lean_array_get_borrowed(v___x_7949_, v_infos_7943_, v___x_7950_);
                v_toConstantVal_7952_ = lean_ctor_get(v___x_7951_, 0);
                v_numParams_7953_ = lean_ctor_get(v___x_7951_, 1);
                lean_inc(v_numParams_7953_);
                v_levelParams_7954_ = lean_ctor_get(v_toConstantVal_7952_, 1);
                v_type_7955_ = lean_ctor_get(v_toConstantVal_7952_, 2);
                lean_inc_ref(v_type_7955_);
                v___x_7956_ = lean_box(0);
                lean_inc(v_levelParams_7954_);
                v_levels_7957_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_7954_, v___x_7956_);
                v___x_7966_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0;
                v___x_7967_ = lean_array_get_size(v_infos_7943_);
                v___x_7968_ = lean_nat_dec_lt(v___x_7950_, v___x_7967_);
                if v___x_7968_ == 0 {
                    v___y_7959_ = v___x_7966_;
                    state = 1;
                    continue;
                } else {
                    v___x_7969_ = lean_nat_dec_le(v___x_7967_, v___x_7967_);
                    if v___x_7969_ == 0 {
                        if v___x_7968_ == 0 {
                            v___y_7959_ = v___x_7966_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7970_ = 0usize;
                            v___x_7971_ = lean_usize_of_nat(v___x_7967_);
                            v___x_7972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_7943_, v___x_7970_, v___x_7971_, v___x_7966_);
                            v___y_7959_ = v___x_7972_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7973_ = 0usize;
                        v___x_7974_ = lean_usize_of_nat(v___x_7967_);
                        v___x_7975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_7943_, v___x_7973_, v___x_7974_, v___x_7966_);
                        v___y_7959_ = v___x_7975_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_infos_7943_);
                v___f_7960_ = lean_alloc_closure(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_7960_, 0, v_infos_7943_);
                lean_closure_set(v___f_7960_, 1, v_levels_7957_);
                lean_closure_set(v___f_7960_, 2, v___y_7959_);
                v___x_7961_ = lean_array_get_size(v_infos_7943_);
                lean_dec_ref(v_infos_7943_);
                v___x_7962_ = lean_nat_sub(v_numParams_7953_, v___x_7961_);
                lean_dec(v_numParams_7953_);
                v___x_7963_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7963_, 0, v___x_7962_);
                v___x_7964_ = 0;
                v___x_7965_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_7955_, v___x_7963_, v___f_7960_, v___x_7964_, v___x_7964_, v_a_7944_, v_a_7945_, v_a_7946_, v_a_7947_);
                return v___x_7965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(
    mut v_infos_7976_: *mut LeanObject,
    mut v_a_7977_: *mut LeanObject,
    mut v_a_7978_: *mut LeanObject,
    mut v_a_7979_: *mut LeanObject,
    mut v_a_7980_: *mut LeanObject,
    mut v_a_7981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7982_: *mut LeanObject = core::ptr::null_mut();
    v_res_7982_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(
        v_infos_7976_,
        v_a_7977_,
        v_a_7978_,
        v_a_7979_,
        v_a_7980_,
    );
    lean_dec(v_a_7980_);
    lean_dec_ref(v_a_7979_);
    lean_dec(v_a_7978_);
    lean_dec_ref(v_a_7977_);
    return v_res_7982_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(
    mut v_00_u03b1_7983_: *mut LeanObject,
    mut v_constName_7984_: *mut LeanObject,
    mut v___y_7985_: *mut LeanObject,
    mut v___y_7986_: *mut LeanObject,
    mut v___y_7987_: *mut LeanObject,
    mut v___y_7988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7990_: *mut LeanObject = core::ptr::null_mut();
    v___x_7990_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_7984_, v___y_7985_, v___y_7986_, v___y_7987_, v___y_7988_);
    return v___x_7990_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(
    mut v_00_u03b1_7991_: *mut LeanObject,
    mut v_constName_7992_: *mut LeanObject,
    mut v___y_7993_: *mut LeanObject,
    mut v___y_7994_: *mut LeanObject,
    mut v___y_7995_: *mut LeanObject,
    mut v___y_7996_: *mut LeanObject,
    mut v___y_7997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7998_: *mut LeanObject = core::ptr::null_mut();
    v_res_7998_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_7991_, v_constName_7992_, v___y_7993_, v___y_7994_, v___y_7995_, v___y_7996_);
    lean_dec(v___y_7996_);
    lean_dec_ref(v___y_7995_);
    lean_dec(v___y_7994_);
    lean_dec_ref(v___y_7993_);
    return v_res_7998_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(
    mut v_00_u03b1_7999_: *mut LeanObject,
    mut v_ref_8000_: *mut LeanObject,
    mut v_constName_8001_: *mut LeanObject,
    mut v___y_8002_: *mut LeanObject,
    mut v___y_8003_: *mut LeanObject,
    mut v___y_8004_: *mut LeanObject,
    mut v___y_8005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8007_: *mut LeanObject = core::ptr::null_mut();
    v___x_8007_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_8000_, v_constName_8001_, v___y_8002_, v___y_8003_, v___y_8004_, v___y_8005_);
    return v___x_8007_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(
    mut v_00_u03b1_8008_: *mut LeanObject,
    mut v_ref_8009_: *mut LeanObject,
    mut v_constName_8010_: *mut LeanObject,
    mut v___y_8011_: *mut LeanObject,
    mut v___y_8012_: *mut LeanObject,
    mut v___y_8013_: *mut LeanObject,
    mut v___y_8014_: *mut LeanObject,
    mut v___y_8015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8016_: *mut LeanObject = core::ptr::null_mut();
    v_res_8016_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_8008_, v_ref_8009_, v_constName_8010_, v___y_8011_, v___y_8012_, v___y_8013_, v___y_8014_);
    lean_dec(v___y_8014_);
    lean_dec_ref(v___y_8013_);
    lean_dec(v___y_8012_);
    lean_dec_ref(v___y_8011_);
    lean_dec(v_ref_8009_);
    return v_res_8016_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(
    mut v_00_u03b1_8017_: *mut LeanObject,
    mut v_ref_8018_: *mut LeanObject,
    mut v_msg_8019_: *mut LeanObject,
    mut v_declHint_8020_: *mut LeanObject,
    mut v___y_8021_: *mut LeanObject,
    mut v___y_8022_: *mut LeanObject,
    mut v___y_8023_: *mut LeanObject,
    mut v___y_8024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8026_: *mut LeanObject = core::ptr::null_mut();
    v___x_8026_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_8018_, v_msg_8019_, v_declHint_8020_, v___y_8021_, v___y_8022_, v___y_8023_, v___y_8024_);
    return v___x_8026_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(
    mut v_00_u03b1_8027_: *mut LeanObject,
    mut v_ref_8028_: *mut LeanObject,
    mut v_msg_8029_: *mut LeanObject,
    mut v_declHint_8030_: *mut LeanObject,
    mut v___y_8031_: *mut LeanObject,
    mut v___y_8032_: *mut LeanObject,
    mut v___y_8033_: *mut LeanObject,
    mut v___y_8034_: *mut LeanObject,
    mut v___y_8035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8036_: *mut LeanObject = core::ptr::null_mut();
    v_res_8036_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_8027_, v_ref_8028_, v_msg_8029_, v_declHint_8030_, v___y_8031_, v___y_8032_, v___y_8033_, v___y_8034_);
    lean_dec(v___y_8034_);
    lean_dec_ref(v___y_8033_);
    lean_dec(v___y_8032_);
    lean_dec_ref(v___y_8031_);
    lean_dec(v_ref_8028_);
    return v_res_8036_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(
    mut v_msg_8037_: *mut LeanObject,
    mut v_declHint_8038_: *mut LeanObject,
    mut v___y_8039_: *mut LeanObject,
    mut v___y_8040_: *mut LeanObject,
    mut v___y_8041_: *mut LeanObject,
    mut v___y_8042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8044_: *mut LeanObject = core::ptr::null_mut();
    v___x_8044_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_8037_, v_declHint_8038_, v___y_8042_);
    return v___x_8044_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(
    mut v_msg_8045_: *mut LeanObject,
    mut v_declHint_8046_: *mut LeanObject,
    mut v___y_8047_: *mut LeanObject,
    mut v___y_8048_: *mut LeanObject,
    mut v___y_8049_: *mut LeanObject,
    mut v___y_8050_: *mut LeanObject,
    mut v___y_8051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8052_: *mut LeanObject = core::ptr::null_mut();
    v_res_8052_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_8045_, v_declHint_8046_, v___y_8047_, v___y_8048_, v___y_8049_, v___y_8050_);
    lean_dec(v___y_8050_);
    lean_dec_ref(v___y_8049_);
    lean_dec(v___y_8048_);
    lean_dec_ref(v___y_8047_);
    return v_res_8052_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(
    mut v_00_u03b1_8053_: *mut LeanObject,
    mut v_ref_8054_: *mut LeanObject,
    mut v_msg_8055_: *mut LeanObject,
    mut v___y_8056_: *mut LeanObject,
    mut v___y_8057_: *mut LeanObject,
    mut v___y_8058_: *mut LeanObject,
    mut v___y_8059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8061_: *mut LeanObject = core::ptr::null_mut();
    v___x_8061_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_8054_, v_msg_8055_, v___y_8056_, v___y_8057_, v___y_8058_, v___y_8059_);
    return v___x_8061_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(
    mut v_00_u03b1_8062_: *mut LeanObject,
    mut v_ref_8063_: *mut LeanObject,
    mut v_msg_8064_: *mut LeanObject,
    mut v___y_8065_: *mut LeanObject,
    mut v___y_8066_: *mut LeanObject,
    mut v___y_8067_: *mut LeanObject,
    mut v___y_8068_: *mut LeanObject,
    mut v___y_8069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8070_: *mut LeanObject = core::ptr::null_mut();
    v_res_8070_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_8062_, v_ref_8063_, v_msg_8064_, v___y_8065_, v___y_8066_, v___y_8067_, v___y_8068_);
    lean_dec(v___y_8068_);
    lean_dec_ref(v___y_8067_);
    lean_dec(v___y_8066_);
    lean_dec_ref(v___y_8065_);
    lean_dec(v_ref_8063_);
    return v_res_8070_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(
    mut v___x_8074_: *mut LeanObject,
    mut v___x_8075_: *mut LeanObject,
    mut v_params_8076_: *mut LeanObject,
    mut v_sz_8077_: usize,
    mut v_i_8078_: usize,
    mut v_bs_8079_: *mut LeanObject,
    mut v___y_8080_: *mut LeanObject,
    mut v___y_8081_: *mut LeanObject,
    mut v___y_8082_: *mut LeanObject,
    mut v___y_8083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8085_: u8 = 0;
    let mut v___x_8086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_8088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_8089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: usize = 0;
    let mut v___x_8096_: usize = 0;
    let mut v___x_8097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8102_: u8 = 0;
    let mut v___x_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8106_: u8 = 0;
    let mut v___x_8107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8112_: usize = 0;
    let mut v___x_8113_: usize = 0;
    let mut v___x_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8117_: u8 = 0;
    let mut v___x_8118_: u8 = 0;
    let mut v___x_8119_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8085_ = lean_usize_dec_lt(v_i_8078_, v_sz_8077_);
                if v___x_8085_ == 0 {
                    lean_dec_ref(v_params_8076_);
                    lean_dec_ref(v___x_8075_);
                    lean_dec(v___x_8074_);
                    v___x_8086_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8086_, 0, v_bs_8079_);
                    return v___x_8086_;
                } else {
                    v_v_8087_ = lean_array_uget_borrowed(v_bs_8079_, v_i_8078_);
                    v_toConstantVal_8088_ = lean_ctor_get(v_v_8087_, 0);
                    v_name_8089_ = lean_ctor_get(v_toConstantVal_8088_, 0);
                    lean_inc(v_name_8089_);
                    v___x_8090_ = lean_unsigned_to_nat(0);
                    v_bs_x27_8091_ = lean_array_uset(v_bs_8079_, v_i_8078_, v___x_8090_);
                    v___x_8107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1;
                    v___x_8108_ = l_Lean_Name_append(v_name_8089_, v___x_8107_);
                    lean_inc(v___x_8074_);
                    v___x_8109_ = l_Lean_mkConst(v___x_8108_, v___x_8074_);
                    v___x_8110_ = l_Lean_Meta_unfoldDefinition(
                        v___x_8109_,
                        v___y_8080_,
                        v___y_8081_,
                        v___y_8082_,
                        v___y_8083_,
                    );
                    if lean_obj_tag(v___x_8110_) == 0 {
                        v_a_8111_ = lean_ctor_get(v___x_8110_, 0);
                        lean_inc(v_a_8111_);
                        lean_dec_ref_known(v___x_8110_, 1);
                        v_sz_8112_ = lean_array_size(v___x_8075_);
                        v___x_8113_ = 0usize;
                        lean_inc_ref(v___x_8075_);
                        v___x_8114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_8076_, v_sz_8112_, v___x_8113_, v___x_8075_);
                        lean_inc_ref(v_params_8076_);
                        v___x_8115_ = l_Array_append___redArg(v_params_8076_, v___x_8114_);
                        lean_dec_ref(v___x_8114_);
                        v___x_8116_ = l_Lean_mkAppN(v_a_8111_, v___x_8115_);
                        lean_dec_ref(v___x_8115_);
                        v___x_8117_ = 0;
                        v___x_8118_ = 1;
                        v___x_8119_ = l_Lean_Meta_mkLambdaFVars(
                            v_params_8076_,
                            v___x_8116_,
                            v___x_8117_,
                            v___x_8085_,
                            v___x_8117_,
                            v___x_8085_,
                            v___x_8118_,
                            v___y_8080_,
                            v___y_8081_,
                            v___y_8082_,
                            v___y_8083_,
                        );
                        v___y_8093_ = v___x_8119_;
                        state = 1;
                        continue;
                    } else {
                        v___y_8093_ = v___x_8110_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_8093_) == 0 {
                    v_a_8094_ = lean_ctor_get(v___y_8093_, 0);
                    lean_inc(v_a_8094_);
                    lean_dec_ref_known(v___y_8093_, 1);
                    v___x_8095_ = 1usize;
                    v___x_8096_ = lean_usize_add(v_i_8078_, v___x_8095_);
                    v___x_8097_ = lean_array_uset(v_bs_x27_8091_, v_i_8078_, v_a_8094_);
                    v_i_8078_ = v___x_8096_;
                    v_bs_8079_ = v___x_8097_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_bs_x27_8091_);
                    lean_dec_ref(v_params_8076_);
                    lean_dec_ref(v___x_8075_);
                    lean_dec(v___x_8074_);
                    v_a_8099_ = lean_ctor_get(v___y_8093_, 0);
                    v_isSharedCheck_8106_ = (!lean_is_exclusive(v___y_8093_)) as u8;
                    if v_isSharedCheck_8106_ == 0 {
                        v___x_8101_ = v___y_8093_;
                        v_isShared_8102_ = v_isSharedCheck_8106_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8099_);
                        lean_dec(v___y_8093_);
                        v___x_8101_ = lean_box(0);
                        v_isShared_8102_ = v_isSharedCheck_8106_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8102_ == 0 {
                    v___x_8104_ = v___x_8101_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8105_, 0, v_a_8099_);
                    v___x_8104_ = v_reuseFailAlloc_8105_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(
    mut v___x_8120_: *mut LeanObject,
    mut v___x_8121_: *mut LeanObject,
    mut v_params_8122_: *mut LeanObject,
    mut v_sz_8123_: *mut LeanObject,
    mut v_i_8124_: *mut LeanObject,
    mut v_bs_8125_: *mut LeanObject,
    mut v___y_8126_: *mut LeanObject,
    mut v___y_8127_: *mut LeanObject,
    mut v___y_8128_: *mut LeanObject,
    mut v___y_8129_: *mut LeanObject,
    mut v___y_8130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8131_: usize = 0;
    let mut v_i_boxed_8132_: usize = 0;
    let mut v_res_8133_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8131_ = lean_unbox_usize(v_sz_8123_);
    lean_dec(v_sz_8123_);
    v_i_boxed_8132_ = lean_unbox_usize(v_i_8124_);
    lean_dec(v_i_8124_);
    v_res_8133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_8120_, v___x_8121_, v_params_8122_, v_sz_boxed_8131_, v_i_boxed_8132_, v_bs_8125_, v___y_8126_, v___y_8127_, v___y_8128_, v___y_8129_);
    lean_dec(v___y_8129_);
    lean_dec_ref(v___y_8128_);
    lean_dec(v___y_8127_);
    lean_dec_ref(v___y_8126_);
    return v_res_8133_;
}
pub unsafe fn l_Lean_Elab_Command_elabCoinductive___lam__0(
    mut v___x_8134_: *mut LeanObject,
    mut v___x_8135_: *mut LeanObject,
    mut v_sz_8136_: usize,
    mut v___x_8137_: usize,
    mut v_a_8138_: *mut LeanObject,
    mut v_params_8139_: *mut LeanObject,
    mut v_x_8140_: *mut LeanObject,
    mut v___y_8141_: *mut LeanObject,
    mut v___y_8142_: *mut LeanObject,
    mut v___y_8143_: *mut LeanObject,
    mut v___y_8144_: *mut LeanObject,
    mut v___y_8145_: *mut LeanObject,
    mut v___y_8146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8148_: *mut LeanObject = core::ptr::null_mut();
    v___x_8148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_8134_, v___x_8135_, v_params_8139_, v_sz_8136_, v___x_8137_, v_a_8138_, v___y_8143_, v___y_8144_, v___y_8145_, v___y_8146_);
    return v___x_8148_;
}
pub unsafe fn l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(
    mut v___x_8149_: *mut LeanObject,
    mut v___x_8150_: *mut LeanObject,
    mut v_sz_8151_: *mut LeanObject,
    mut v___x_8152_: *mut LeanObject,
    mut v_a_8153_: *mut LeanObject,
    mut v_params_8154_: *mut LeanObject,
    mut v_x_8155_: *mut LeanObject,
    mut v___y_8156_: *mut LeanObject,
    mut v___y_8157_: *mut LeanObject,
    mut v___y_8158_: *mut LeanObject,
    mut v___y_8159_: *mut LeanObject,
    mut v___y_8160_: *mut LeanObject,
    mut v___y_8161_: *mut LeanObject,
    mut v___y_8162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8163_: usize = 0;
    let mut v___x_5221__boxed_8164_: usize = 0;
    let mut v_res_8165_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8163_ = lean_unbox_usize(v_sz_8151_);
    lean_dec(v_sz_8151_);
    v___x_5221__boxed_8164_ = lean_unbox_usize(v___x_8152_);
    lean_dec(v___x_8152_);
    v_res_8165_ = l_Lean_Elab_Command_elabCoinductive___lam__0(
        v___x_8149_,
        v___x_8150_,
        v_sz_boxed_8163_,
        v___x_5221__boxed_8164_,
        v_a_8153_,
        v_params_8154_,
        v_x_8155_,
        v___y_8156_,
        v___y_8157_,
        v___y_8158_,
        v___y_8159_,
        v___y_8160_,
        v___y_8161_,
    );
    lean_dec(v___y_8161_);
    lean_dec_ref(v___y_8160_);
    lean_dec(v___y_8159_);
    lean_dec_ref(v___y_8158_);
    lean_dec(v___y_8157_);
    lean_dec_ref(v___y_8156_);
    lean_dec_ref(v_x_8155_);
    return v_res_8165_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_8167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8168_: *mut LeanObject = core::ptr::null_mut();
    v___x_8167_ =
        l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0;
    v___x_8168_ = l_Lean_stringToMessageData(v___x_8167_);
    return v___x_8168_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(
    mut v_constName_8169_: *mut LeanObject,
    mut v___y_8170_: *mut LeanObject,
    mut v___y_8171_: *mut LeanObject,
    mut v___y_8172_: *mut LeanObject,
    mut v___y_8173_: *mut LeanObject,
    mut v___y_8174_: *mut LeanObject,
    mut v___y_8175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_8178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8181_: u8 = 0;
    let mut v___x_8182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8190_: u8 = 0;
    let mut v___x_8192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8177_ = lean_st_ref_get(v___y_8175_);
                v_env_8178_ = lean_ctor_get(v___x_8177_, 0);
                lean_inc_ref(v_env_8178_);
                lean_dec(v___x_8177_);
                lean_inc(v_constName_8169_);
                v___x_8179_ = l_Lean_isInductiveCore_x3f(v_env_8178_, v_constName_8169_);
                if lean_obj_tag(v___x_8179_) == 0 {
                    v___x_8180_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
                    v___x_8181_ = 0;
                    v___x_8182_ = l_Lean_MessageData_ofConstName(v_constName_8169_, v___x_8181_);
                    v___x_8183_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_8183_, 0, v___x_8180_);
                    lean_ctor_set(v___x_8183_, 1, v___x_8182_);
                    v___x_8184_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1);
                    v___x_8185_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_8185_, 0, v___x_8183_);
                    lean_ctor_set(v___x_8185_, 1, v___x_8184_);
                    v___x_8186_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_8185_, v___y_8170_, v___y_8171_, v___y_8172_, v___y_8173_, v___y_8174_, v___y_8175_);
                    return v___x_8186_;
                } else {
                    lean_dec(v_constName_8169_);
                    v_val_8187_ = lean_ctor_get(v___x_8179_, 0);
                    v_isSharedCheck_8194_ = (!lean_is_exclusive(v___x_8179_)) as u8;
                    if v_isSharedCheck_8194_ == 0 {
                        v___x_8189_ = v___x_8179_;
                        v_isShared_8190_ = v_isSharedCheck_8194_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_8187_);
                        lean_dec(v___x_8179_);
                        v___x_8189_ = lean_box(0);
                        v_isShared_8190_ = v_isSharedCheck_8194_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8190_ == 0 {
                    lean_ctor_set_tag(v___x_8189_, 0);
                    v___x_8192_ = v___x_8189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8193_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8193_, 0, v_val_8187_);
                    v___x_8192_ = v_reuseFailAlloc_8193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(
    mut v_constName_8195_: *mut LeanObject,
    mut v___y_8196_: *mut LeanObject,
    mut v___y_8197_: *mut LeanObject,
    mut v___y_8198_: *mut LeanObject,
    mut v___y_8199_: *mut LeanObject,
    mut v___y_8200_: *mut LeanObject,
    mut v___y_8201_: *mut LeanObject,
    mut v___y_8202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8203_: *mut LeanObject = core::ptr::null_mut();
    v_res_8203_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(
        v_constName_8195_,
        v___y_8196_,
        v___y_8197_,
        v___y_8198_,
        v___y_8199_,
        v___y_8200_,
        v___y_8201_,
    );
    lean_dec(v___y_8201_);
    lean_dec_ref(v___y_8200_);
    lean_dec(v___y_8199_);
    lean_dec_ref(v___y_8198_);
    lean_dec(v___y_8197_);
    lean_dec_ref(v___y_8196_);
    return v_res_8203_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(
    mut v_sz_8204_: usize,
    mut v_i_8205_: usize,
    mut v_bs_8206_: *mut LeanObject,
    mut v___y_8207_: *mut LeanObject,
    mut v___y_8208_: *mut LeanObject,
    mut v___y_8209_: *mut LeanObject,
    mut v___y_8210_: *mut LeanObject,
    mut v___y_8211_: *mut LeanObject,
    mut v___y_8212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8214_: u8 = 0;
    let mut v___x_8215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_8216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_8217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8222_: usize = 0;
    let mut v___x_8223_: usize = 0;
    let mut v___x_8224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8229_: u8 = 0;
    let mut v___x_8231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8214_ = lean_usize_dec_lt(v_i_8205_, v_sz_8204_);
                if v___x_8214_ == 0 {
                    v___x_8215_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8215_, 0, v_bs_8206_);
                    return v___x_8215_;
                } else {
                    v_v_8216_ = lean_array_uget_borrowed(v_bs_8206_, v_i_8205_);
                    v_declName_8217_ = lean_ctor_get(v_v_8216_, 1);
                    lean_inc(v_declName_8217_);
                    v___x_8218_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_8217_, v___y_8207_, v___y_8208_, v___y_8209_, v___y_8210_, v___y_8211_, v___y_8212_);
                    if lean_obj_tag(v___x_8218_) == 0 {
                        v_a_8219_ = lean_ctor_get(v___x_8218_, 0);
                        lean_inc(v_a_8219_);
                        lean_dec_ref_known(v___x_8218_, 1);
                        v___x_8220_ = lean_unsigned_to_nat(0);
                        v_bs_x27_8221_ = lean_array_uset(v_bs_8206_, v_i_8205_, v___x_8220_);
                        v___x_8222_ = 1usize;
                        v___x_8223_ = lean_usize_add(v_i_8205_, v___x_8222_);
                        v___x_8224_ = lean_array_uset(v_bs_x27_8221_, v_i_8205_, v_a_8219_);
                        v_i_8205_ = v___x_8223_;
                        v_bs_8206_ = v___x_8224_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_8206_);
                        v_a_8226_ = lean_ctor_get(v___x_8218_, 0);
                        v_isSharedCheck_8233_ = (!lean_is_exclusive(v___x_8218_)) as u8;
                        if v_isSharedCheck_8233_ == 0 {
                            v___x_8228_ = v___x_8218_;
                            v_isShared_8229_ = v_isSharedCheck_8233_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8226_);
                            lean_dec(v___x_8218_);
                            v___x_8228_ = lean_box(0);
                            v_isShared_8229_ = v_isSharedCheck_8233_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8229_ == 0 {
                    v___x_8231_ = v___x_8228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8232_, 0, v_a_8226_);
                    v___x_8231_ = v_reuseFailAlloc_8232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(
    mut v_sz_8234_: *mut LeanObject,
    mut v_i_8235_: *mut LeanObject,
    mut v_bs_8236_: *mut LeanObject,
    mut v___y_8237_: *mut LeanObject,
    mut v___y_8238_: *mut LeanObject,
    mut v___y_8239_: *mut LeanObject,
    mut v___y_8240_: *mut LeanObject,
    mut v___y_8241_: *mut LeanObject,
    mut v___y_8242_: *mut LeanObject,
    mut v___y_8243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8244_: usize = 0;
    let mut v_i_boxed_8245_: usize = 0;
    let mut v_res_8246_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8244_ = lean_unbox_usize(v_sz_8234_);
    lean_dec(v_sz_8234_);
    v_i_boxed_8245_ = lean_unbox_usize(v_i_8235_);
    lean_dec(v_i_8235_);
    v_res_8246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_boxed_8244_, v_i_boxed_8245_, v_bs_8236_, v___y_8237_, v___y_8238_, v___y_8239_, v___y_8240_, v___y_8241_, v___y_8242_);
    lean_dec(v___y_8242_);
    lean_dec_ref(v___y_8241_);
    lean_dec(v___y_8240_);
    lean_dec_ref(v___y_8239_);
    lean_dec(v___y_8238_);
    lean_dec_ref(v___y_8237_);
    return v_res_8246_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8249_: *mut LeanObject = core::ptr::null_mut();
    v___x_8247_ = l_Lean_instInhabitedExpr;
    v___x_8248_ = lean_box(0);
    v___x_8249_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8249_, 0, v___x_8248_);
    lean_ctor_set(v___x_8249_, 1, v___x_8247_);
    return v___x_8249_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(
    mut v_coinductiveElabData_8250_: *mut LeanObject,
    mut v_a_8251_: *mut LeanObject,
    mut v___x_8252_: *mut LeanObject,
    mut v_as_8253_: *mut LeanObject,
    mut v_i_8254_: *mut LeanObject,
    mut v_j_8255_: *mut LeanObject,
    mut v_bs_8256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_8257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_8258_: u8 = 0;
    let mut v___x_8259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_8261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifiers_8262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isGreatest_8263_: u8 = 0;
    let mut v___x_8264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_8268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_8269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: u8 = 0;
    let mut v___x_8272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8274_: u8 = 0;
    let mut v___x_8275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8282_: u8 = 0;
    let mut v___x_8283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_8257_ = lean_unsigned_to_nat(0);
                v_isZero_8258_ = lean_nat_dec_eq(v_i_8254_, v_zero_8257_);
                if v_isZero_8258_ == 1 {
                    lean_dec(v_j_8255_);
                    lean_dec(v_i_8254_);
                    lean_dec(v___x_8252_);
                    return v_bs_8256_;
                } else {
                    v___x_8259_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
                    v___x_8260_ = lean_array_get_borrowed(
                        v___x_8259_,
                        v_coinductiveElabData_8250_,
                        v_j_8255_,
                    );
                    v_ref_8261_ = lean_ctor_get(v___x_8260_, 2);
                    v_modifiers_8262_ = lean_ctor_get(v___x_8260_, 3);
                    v_isGreatest_8263_ = lean_ctor_get_uint8(
                        v___x_8260_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v___x_8264_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
                    v___x_8265_ = lean_array_get_borrowed(v___x_8264_, v_a_8251_, v_j_8255_);
                    v_fst_8266_ = lean_ctor_get(v___x_8265_, 0);
                    v_snd_8267_ = lean_ctor_get(v___x_8265_, 1);
                    v_one_8268_ = lean_unsigned_to_nat(1);
                    v_n_8269_ = lean_nat_sub(v_i_8254_, v_one_8268_);
                    lean_dec(v_i_8254_);
                    v___x_8270_ = lean_array_fget_borrowed(v_as_8253_, v_j_8255_);
                    v___x_8271_ = 0;
                    v___x_8272_ = lean_box(0);
                    if v_isGreatest_8263_ == 0 {
                        v___x_8282_ = 2;
                        v___y_8274_ = v___x_8282_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8283_ = 1;
                        v___y_8274_ = v___x_8283_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_n(v_ref_8261_, 4);
                v___x_8275_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_8275_, 0, v_ref_8261_);
                lean_ctor_set(v___x_8275_, 1, v___x_8272_);
                lean_ctor_set_uint8(
                    v___x_8275_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_8274_,
                );
                v___x_8276_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_8276_, 0, v___x_8275_);
                v___x_8277_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_8277_, 0, v_ref_8261_);
                lean_ctor_set(v___x_8277_, 1, v___x_8272_);
                lean_ctor_set(v___x_8277_, 2, v___x_8272_);
                lean_ctor_set(v___x_8277_, 3, v___x_8276_);
                lean_ctor_set(v___x_8277_, 4, v___x_8272_);
                lean_ctor_set(v___x_8277_, 5, v_zero_8257_);
                lean_inc(v___x_8270_);
                lean_inc(v_snd_8267_);
                lean_inc(v_fst_8266_);
                lean_inc_ref(v_modifiers_8262_);
                lean_inc(v___x_8252_);
                v___x_8278_ = lean_alloc_ctor(0, 9, (1) as u32);
                lean_ctor_set(v___x_8278_, 0, v_ref_8261_);
                lean_ctor_set(v___x_8278_, 1, v___x_8252_);
                lean_ctor_set(v___x_8278_, 2, v_modifiers_8262_);
                lean_ctor_set(v___x_8278_, 3, v_fst_8266_);
                lean_ctor_set(v___x_8278_, 4, v_ref_8261_);
                lean_ctor_set(v___x_8278_, 5, v_zero_8257_);
                lean_ctor_set(v___x_8278_, 6, v_snd_8267_);
                lean_ctor_set(v___x_8278_, 7, v___x_8270_);
                lean_ctor_set(v___x_8278_, 8, v___x_8277_);
                lean_ctor_set_uint8(
                    v___x_8278_,
                    (core::mem::size_of::<*mut LeanObject>() * 9) as u32,
                    v___x_8271_,
                );
                v___x_8279_ = lean_nat_add(v_j_8255_, v_one_8268_);
                lean_dec(v_j_8255_);
                v___x_8280_ = lean_array_push(v_bs_8256_, v___x_8278_);
                v_i_8254_ = v_n_8269_;
                v_j_8255_ = v___x_8279_;
                v_bs_8256_ = v___x_8280_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(
    mut v_coinductiveElabData_8284_: *mut LeanObject,
    mut v_a_8285_: *mut LeanObject,
    mut v___x_8286_: *mut LeanObject,
    mut v_as_8287_: *mut LeanObject,
    mut v_i_8288_: *mut LeanObject,
    mut v_j_8289_: *mut LeanObject,
    mut v_bs_8290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8291_: *mut LeanObject = core::ptr::null_mut();
    v_res_8291_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(
            v_coinductiveElabData_8284_,
            v_a_8285_,
            v___x_8286_,
            v_as_8287_,
            v_i_8288_,
            v_j_8289_,
            v_bs_8290_,
        );
    lean_dec_ref(v_as_8287_);
    lean_dec_ref(v_a_8285_);
    lean_dec_ref(v_coinductiveElabData_8284_);
    return v_res_8291_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(
    mut v_a_8292_: *mut LeanObject,
    mut v_a_8293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_8295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8299_: u8 = 0;
    let mut v___x_8300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_8292_) == 0 {
                    v___x_8294_ = l_List_reverse___redArg(v_a_8293_);
                    return v___x_8294_;
                } else {
                    v_head_8295_ = lean_ctor_get(v_a_8292_, 0);
                    v_tail_8296_ = lean_ctor_get(v_a_8292_, 1);
                    v_isSharedCheck_8305_ = (!lean_is_exclusive(v_a_8292_)) as u8;
                    if v_isSharedCheck_8305_ == 0 {
                        v___x_8298_ = v_a_8292_;
                        v_isShared_8299_ = v_isSharedCheck_8305_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_8296_);
                        lean_inc(v_head_8295_);
                        lean_dec(v_a_8292_);
                        v___x_8298_ = lean_box(0);
                        v_isShared_8299_ = v_isSharedCheck_8305_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8300_ = l_Lean_MessageData_ofName(v_head_8295_);
                if v_isShared_8299_ == 0 {
                    lean_ctor_set(v___x_8298_, 1, v_a_8293_);
                    lean_ctor_set(v___x_8298_, 0, v___x_8300_);
                    v___x_8302_ = v___x_8298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8304_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8304_, 0, v___x_8300_);
                    lean_ctor_set(v_reuseFailAlloc_8304_, 1, v_a_8293_);
                    v___x_8302_ = v_reuseFailAlloc_8304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_8292_ = v_tail_8296_;
                v_a_8293_ = v___x_8302_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(
    mut v_sz_8306_: usize,
    mut v_i_8307_: usize,
    mut v_bs_8308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8309_: u8 = 0;
    let mut v_v_8310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_8311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8314_: usize = 0;
    let mut v___x_8315_: usize = 0;
    let mut v___x_8316_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8309_ = lean_usize_dec_lt(v_i_8307_, v_sz_8306_);
                if v___x_8309_ == 0 {
                    return v_bs_8308_;
                } else {
                    v_v_8310_ = lean_array_uget_borrowed(v_bs_8308_, v_i_8307_);
                    v_declName_8311_ = lean_ctor_get(v_v_8310_, 1);
                    lean_inc(v_declName_8311_);
                    v___x_8312_ = lean_unsigned_to_nat(0);
                    v_bs_x27_8313_ = lean_array_uset(v_bs_8308_, v_i_8307_, v___x_8312_);
                    v___x_8314_ = 1usize;
                    v___x_8315_ = lean_usize_add(v_i_8307_, v___x_8314_);
                    v___x_8316_ = lean_array_uset(v_bs_x27_8313_, v_i_8307_, v_declName_8311_);
                    v_i_8307_ = v___x_8315_;
                    v_bs_8308_ = v___x_8316_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6___boxed(
    mut v_sz_8318_: *mut LeanObject,
    mut v_i_8319_: *mut LeanObject,
    mut v_bs_8320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8321_: usize = 0;
    let mut v_i_boxed_8322_: usize = 0;
    let mut v_res_8323_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8321_ = lean_unbox_usize(v_sz_8318_);
    lean_dec(v_sz_8318_);
    v_i_boxed_8322_ = lean_unbox_usize(v_i_8319_);
    lean_dec(v_i_8319_);
    v_res_8323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_boxed_8321_, v_i_boxed_8322_, v_bs_8320_);
    return v_res_8323_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(
    mut v_v_8324_: *mut LeanObject,
    mut v___x_8325_: *mut LeanObject,
    mut v___x_8326_: *mut LeanObject,
    mut v___x_8327_: u8,
    mut v_args_8328_: *mut LeanObject,
    mut v_body_8329_: *mut LeanObject,
    mut v___y_8330_: *mut LeanObject,
    mut v___y_8331_: *mut LeanObject,
    mut v___y_8332_: *mut LeanObject,
    mut v___y_8333_: *mut LeanObject,
    mut v___y_8334_: *mut LeanObject,
    mut v___y_8335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_8337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8344_: u8 = 0;
    let mut v___x_8345_: u8 = 0;
    let mut v___x_8346_: *mut LeanObject = core::ptr::null_mut();
    v_numParams_8337_ = lean_ctor_get(v_v_8324_, 1);
    lean_inc(v_numParams_8337_);
    lean_dec(v_v_8324_);
    lean_inc_ref(v_args_8328_);
    v___x_8338_ = l_Array_toSubarray___redArg(v_args_8328_, v___x_8325_, v___x_8326_);
    v___x_8339_ = l_Subarray_copy___redArg(v___x_8338_);
    v___x_8340_ = lean_array_get_size(v_args_8328_);
    v___x_8341_ = l_Array_toSubarray___redArg(v_args_8328_, v_numParams_8337_, v___x_8340_);
    v___x_8342_ = l_Subarray_copy___redArg(v___x_8341_);
    v___x_8343_ = l_Array_append___redArg(v___x_8339_, v___x_8342_);
    lean_dec_ref(v___x_8342_);
    v___x_8344_ = 0;
    v___x_8345_ = 1;
    v___x_8346_ = l_Lean_Meta_mkForallFVars(
        v___x_8343_,
        v_body_8329_,
        v___x_8344_,
        v___x_8327_,
        v___x_8327_,
        v___x_8345_,
        v___y_8332_,
        v___y_8333_,
        v___y_8334_,
        v___y_8335_,
    );
    lean_dec_ref(v___x_8343_);
    return v___x_8346_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(
    mut v_v_8347_: *mut LeanObject,
    mut v___x_8348_: *mut LeanObject,
    mut v___x_8349_: *mut LeanObject,
    mut v___x_8350_: *mut LeanObject,
    mut v_args_8351_: *mut LeanObject,
    mut v_body_8352_: *mut LeanObject,
    mut v___y_8353_: *mut LeanObject,
    mut v___y_8354_: *mut LeanObject,
    mut v___y_8355_: *mut LeanObject,
    mut v___y_8356_: *mut LeanObject,
    mut v___y_8357_: *mut LeanObject,
    mut v___y_8358_: *mut LeanObject,
    mut v___y_8359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5474__boxed_8360_: u8 = 0;
    let mut v_res_8361_: *mut LeanObject = core::ptr::null_mut();
    v___x_5474__boxed_8360_ = (lean_unbox(v___x_8350_) as u8);
    v_res_8361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v_v_8347_, v___x_8348_, v___x_8349_, v___x_5474__boxed_8360_, v_args_8351_, v_body_8352_, v___y_8353_, v___y_8354_, v___y_8355_, v___y_8356_, v___y_8357_, v___y_8358_);
    lean_dec(v___y_8358_);
    lean_dec_ref(v___y_8357_);
    lean_dec(v___y_8356_);
    lean_dec_ref(v___y_8355_);
    lean_dec(v___y_8354_);
    lean_dec_ref(v___y_8353_);
    return v_res_8361_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(
    mut v___x_8362_: *mut LeanObject,
    mut v_sz_8363_: usize,
    mut v_i_8364_: usize,
    mut v_bs_8365_: *mut LeanObject,
    mut v___y_8366_: *mut LeanObject,
    mut v___y_8367_: *mut LeanObject,
    mut v___y_8368_: *mut LeanObject,
    mut v___y_8369_: *mut LeanObject,
    mut v___y_8370_: *mut LeanObject,
    mut v___y_8371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8373_: u8 = 0;
    let mut v___x_8374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_8375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_8376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_8377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8382_: u8 = 0;
    let mut v___x_8383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8388_: usize = 0;
    let mut v___x_8389_: usize = 0;
    let mut v___x_8390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8395_: u8 = 0;
    let mut v___x_8397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8373_ = lean_usize_dec_lt(v_i_8364_, v_sz_8363_);
                if v___x_8373_ == 0 {
                    lean_dec(v___x_8362_);
                    v___x_8374_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8374_, 0, v_bs_8365_);
                    return v___x_8374_;
                } else {
                    v_v_8375_ = lean_array_uget_borrowed(v_bs_8365_, v_i_8364_);
                    v_toConstantVal_8376_ = lean_ctor_get(v_v_8375_, 0);
                    v_name_8377_ = lean_ctor_get(v_toConstantVal_8376_, 0);
                    lean_inc(v_name_8377_);
                    v_type_8378_ = lean_ctor_get(v_toConstantVal_8376_, 2);
                    v___x_8379_ = lean_unsigned_to_nat(0);
                    v___x_8380_ = lean_box((v___x_8373_) as usize);
                    lean_inc(v___x_8362_);
                    lean_inc(v_v_8375_);
                    v___f_8381_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed as *mut core::ffi::c_void, 13, 4);
                    lean_closure_set(v___f_8381_, 0, v_v_8375_);
                    lean_closure_set(v___f_8381_, 1, v___x_8379_);
                    lean_closure_set(v___f_8381_, 2, v___x_8362_);
                    lean_closure_set(v___f_8381_, 3, v___x_8380_);
                    v___x_8382_ = 0;
                    lean_inc_ref(v_type_8378_);
                    v___x_8383_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_8378_, v___f_8381_, v___x_8382_, v___y_8366_, v___y_8367_, v___y_8368_, v___y_8369_, v___y_8370_, v___y_8371_);
                    if lean_obj_tag(v___x_8383_) == 0 {
                        v_a_8384_ = lean_ctor_get(v___x_8383_, 0);
                        lean_inc(v_a_8384_);
                        lean_dec_ref_known(v___x_8383_, 1);
                        v_bs_x27_8385_ = lean_array_uset(v_bs_8365_, v_i_8364_, v___x_8379_);
                        v___x_8386_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_8377_);
                        v___x_8387_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_8387_, 0, v___x_8386_);
                        lean_ctor_set(v___x_8387_, 1, v_a_8384_);
                        v___x_8388_ = 1usize;
                        v___x_8389_ = lean_usize_add(v_i_8364_, v___x_8388_);
                        v___x_8390_ = lean_array_uset(v_bs_x27_8385_, v_i_8364_, v___x_8387_);
                        v_i_8364_ = v___x_8389_;
                        v_bs_8365_ = v___x_8390_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_name_8377_);
                        lean_dec_ref(v_bs_8365_);
                        lean_dec(v___x_8362_);
                        v_a_8392_ = lean_ctor_get(v___x_8383_, 0);
                        v_isSharedCheck_8399_ = (!lean_is_exclusive(v___x_8383_)) as u8;
                        if v_isSharedCheck_8399_ == 0 {
                            v___x_8394_ = v___x_8383_;
                            v_isShared_8395_ = v_isSharedCheck_8399_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8392_);
                            lean_dec(v___x_8383_);
                            v___x_8394_ = lean_box(0);
                            v_isShared_8395_ = v_isSharedCheck_8399_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8395_ == 0 {
                    v___x_8397_ = v___x_8394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8398_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8398_, 0, v_a_8392_);
                    v___x_8397_ = v_reuseFailAlloc_8398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___boxed(
    mut v___x_8400_: *mut LeanObject,
    mut v_sz_8401_: *mut LeanObject,
    mut v_i_8402_: *mut LeanObject,
    mut v_bs_8403_: *mut LeanObject,
    mut v___y_8404_: *mut LeanObject,
    mut v___y_8405_: *mut LeanObject,
    mut v___y_8406_: *mut LeanObject,
    mut v___y_8407_: *mut LeanObject,
    mut v___y_8408_: *mut LeanObject,
    mut v___y_8409_: *mut LeanObject,
    mut v___y_8410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8411_: usize = 0;
    let mut v_i_boxed_8412_: usize = 0;
    let mut v_res_8413_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8411_ = lean_unbox_usize(v_sz_8401_);
    lean_dec(v_sz_8401_);
    v_i_boxed_8412_ = lean_unbox_usize(v_i_8402_);
    lean_dec(v_i_8402_);
    v_res_8413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_8400_, v_sz_boxed_8411_, v_i_boxed_8412_, v_bs_8403_, v___y_8404_, v___y_8405_, v___y_8406_, v___y_8407_, v___y_8408_, v___y_8409_);
    lean_dec(v___y_8409_);
    lean_dec_ref(v___y_8408_);
    lean_dec(v___y_8407_);
    lean_dec_ref(v___y_8406_);
    lean_dec(v___y_8405_);
    lean_dec_ref(v___y_8404_);
    return v_res_8413_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(
    mut v___x_8414_: *mut LeanObject,
    mut v_sz_8415_: usize,
    mut v_i_8416_: usize,
    mut v_bs_8417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8418_: u8 = 0;
    let mut v_v_8419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8424_: usize = 0;
    let mut v___x_8425_: usize = 0;
    let mut v___x_8426_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8418_ = lean_usize_dec_lt(v_i_8416_, v_sz_8415_);
                if v___x_8418_ == 0 {
                    lean_dec(v___x_8414_);
                    return v_bs_8417_;
                } else {
                    v_v_8419_ = lean_array_uget_borrowed(v_bs_8417_, v_i_8416_);
                    v_fst_8420_ = lean_ctor_get(v_v_8419_, 0);
                    lean_inc(v_fst_8420_);
                    v___x_8421_ = lean_unsigned_to_nat(0);
                    v_bs_x27_8422_ = lean_array_uset(v_bs_8417_, v_i_8416_, v___x_8421_);
                    lean_inc(v___x_8414_);
                    v___x_8423_ = l_Lean_mkConst(v_fst_8420_, v___x_8414_);
                    v___x_8424_ = 1usize;
                    v___x_8425_ = lean_usize_add(v_i_8416_, v___x_8424_);
                    v___x_8426_ = lean_array_uset(v_bs_x27_8422_, v_i_8416_, v___x_8423_);
                    v_i_8416_ = v___x_8425_;
                    v_bs_8417_ = v___x_8426_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3___boxed(
    mut v___x_8428_: *mut LeanObject,
    mut v_sz_8429_: *mut LeanObject,
    mut v_i_8430_: *mut LeanObject,
    mut v_bs_8431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8432_: usize = 0;
    let mut v_i_boxed_8433_: usize = 0;
    let mut v_res_8434_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8432_ = lean_unbox_usize(v_sz_8429_);
    lean_dec(v_sz_8429_);
    v_i_boxed_8433_ = lean_unbox_usize(v_i_8430_);
    lean_dec(v_i_8430_);
    v_res_8434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_8428_, v_sz_boxed_8432_, v_i_boxed_8433_, v_bs_8431_);
    return v_res_8434_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCoinductive___closed__1() -> *mut LeanObject {
    let mut v___x_8436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8437_: *mut LeanObject = core::ptr::null_mut();
    v___x_8436_ = l_Lean_Elab_Command_elabCoinductive___closed__0;
    v___x_8437_ = l_Lean_stringToMessageData(v___x_8436_);
    return v___x_8437_;
}
pub unsafe fn l_Lean_Elab_Command_elabCoinductive(
    mut v_coinductiveElabData_8438_: *mut LeanObject,
    mut v_a_8439_: *mut LeanObject,
    mut v_a_8440_: *mut LeanObject,
    mut v_a_8441_: *mut LeanObject,
    mut v_a_8442_: *mut LeanObject,
    mut v_a_8443_: *mut LeanObject,
    mut v_a_8444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_8446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_8447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_8448_: u8 = 0;
    let mut v___x_8449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8457_: usize = 0;
    let mut v___x_8458_: usize = 0;
    let mut v___x_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_8463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_8464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8467_: usize = 0;
    let mut v___x_8468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_8470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8474_: usize = 0;
    let mut v___x_8475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8480_: u8 = 0;
    let mut v___x_8481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_8483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_8484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8496_: u8 = 0;
    let mut v___x_8498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8500_: u8 = 0;
    let mut v_a_8501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8504_: u8 = 0;
    let mut v___x_8506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8508_: u8 = 0;
    let mut v_a_8509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8512_: u8 = 0;
    let mut v___x_8514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8516_: u8 = 0;
    let mut v_cls_8517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8519_: u8 = 0;
    let mut v___x_8520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8521_: usize = 0;
    let mut v___x_8522_: usize = 0;
    let mut v___x_8523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8529_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_8446_ = lean_ctor_get(v_a_8443_, 2);
                v_inheritedTraceOptions_8447_ = lean_ctor_get(v_a_8443_, 13);
                v_hasTrace_8448_ = lean_ctor_get_uint8(
                    v_options_8446_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_8449_ = l_Lean_instInhabitedInductiveVal_default;
                if v_hasTrace_8448_ == 0 {
                    v___y_8451_ = v_a_8439_;
                    v___y_8452_ = v_a_8440_;
                    v___y_8453_ = v_a_8441_;
                    v___y_8454_ = v_a_8442_;
                    v___y_8455_ = v_a_8443_;
                    v___y_8456_ = v_a_8444_;
                    state = 1;
                    continue;
                } else {
                    v_cls_8517_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_;
                    v___x_8518_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
                    v___x_8519_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_8447_,
                        v_options_8446_,
                        v___x_8518_,
                    );
                    if v___x_8519_ == 0 {
                        v___y_8451_ = v_a_8439_;
                        v___y_8452_ = v_a_8440_;
                        v___y_8453_ = v_a_8441_;
                        v___y_8454_ = v_a_8442_;
                        v___y_8455_ = v_a_8443_;
                        v___y_8456_ = v_a_8444_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8520_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCoinductive___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCoinductive___closed__1_once
                            ),
                            _init_l_Lean_Elab_Command_elabCoinductive___closed__1,
                        );
                        v_sz_8521_ = lean_array_size(v_coinductiveElabData_8438_);
                        v___x_8522_ = 0usize;
                        lean_inc_ref(v_coinductiveElabData_8438_);
                        v___x_8523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_8521_, v___x_8522_, v_coinductiveElabData_8438_);
                        v___x_8524_ = lean_array_to_list(v___x_8523_);
                        v___x_8525_ = lean_box(0);
                        v___x_8526_ =
                            l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(
                                v___x_8524_,
                                v___x_8525_,
                            );
                        v___x_8527_ = l_Lean_MessageData_ofList(v___x_8526_);
                        v___x_8528_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_8528_, 0, v___x_8520_);
                        lean_ctor_set(v___x_8528_, 1, v___x_8527_);
                        v___x_8529_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_8517_, v___x_8528_, v_a_8441_, v_a_8442_, v_a_8443_, v_a_8444_);
                        if lean_obj_tag(v___x_8529_) == 0 {
                            lean_dec_ref_known(v___x_8529_, 1);
                            v___y_8451_ = v_a_8439_;
                            v___y_8452_ = v_a_8440_;
                            v___y_8453_ = v_a_8441_;
                            v___y_8454_ = v_a_8442_;
                            v___y_8455_ = v_a_8443_;
                            v___y_8456_ = v_a_8444_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_coinductiveElabData_8438_);
                            return v___x_8529_;
                        }
                    }
                }
            }
            1 => {
                v_sz_8457_ = lean_array_size(v_coinductiveElabData_8438_);
                v___x_8458_ = 0usize;
                lean_inc_ref(v_coinductiveElabData_8438_);
                v___x_8459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_8457_, v___x_8458_, v_coinductiveElabData_8438_, v___y_8451_, v___y_8452_, v___y_8453_, v___y_8454_, v___y_8455_, v___y_8456_);
                if lean_obj_tag(v___x_8459_) == 0 {
                    v_a_8460_ = lean_ctor_get(v___x_8459_, 0);
                    lean_inc_n(v_a_8460_, 2);
                    lean_dec_ref_known(v___x_8459_, 1);
                    v___x_8461_ = lean_unsigned_to_nat(0);
                    v___x_8462_ = lean_array_get_borrowed(v___x_8449_, v_a_8460_, v___x_8461_);
                    v_toConstantVal_8463_ = lean_ctor_get(v___x_8462_, 0);
                    v_numParams_8464_ = lean_ctor_get(v___x_8462_, 1);
                    v___x_8465_ = lean_array_get_size(v_a_8460_);
                    v___x_8466_ = lean_nat_sub(v_numParams_8464_, v___x_8465_);
                    v_sz_8467_ = lean_array_size(v_a_8460_);
                    lean_inc(v___x_8466_);
                    v___x_8468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_8466_, v_sz_8467_, v___x_8458_, v_a_8460_, v___y_8451_, v___y_8452_, v___y_8453_, v___y_8454_, v___y_8455_, v___y_8456_);
                    if lean_obj_tag(v___x_8468_) == 0 {
                        v_a_8469_ = lean_ctor_get(v___x_8468_, 0);
                        lean_inc_n(v_a_8469_, 2);
                        lean_dec_ref_known(v___x_8468_, 1);
                        v_levelParams_8470_ = lean_ctor_get(v_toConstantVal_8463_, 1);
                        v_type_8471_ = lean_ctor_get(v_toConstantVal_8463_, 2);
                        v___x_8472_ = lean_box(0);
                        lean_inc(v_levelParams_8470_);
                        v___x_8473_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_8470_, v___x_8472_);
                        v_sz_8474_ = lean_array_size(v_a_8469_);
                        lean_inc(v___x_8473_);
                        v___x_8475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_8473_, v_sz_8474_, v___x_8458_, v_a_8469_);
                        v___x_8476_ = lean_box_usize(v_sz_8467_);
                        v___x_8477_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1;
                        lean_inc(v_a_8460_);
                        v___f_8478_ = lean_alloc_closure(
                            l_Lean_Elab_Command_elabCoinductive___lam__0___boxed
                                as *mut core::ffi::c_void,
                            14,
                            5,
                        );
                        lean_closure_set(v___f_8478_, 0, v___x_8473_);
                        lean_closure_set(v___f_8478_, 1, v___x_8475_);
                        lean_closure_set(v___f_8478_, 2, v___x_8476_);
                        lean_closure_set(v___f_8478_, 3, v___x_8477_);
                        lean_closure_set(v___f_8478_, 4, v_a_8460_);
                        lean_inc(v___x_8466_);
                        v___x_8479_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_8479_, 0, v___x_8466_);
                        v___x_8480_ = 0;
                        lean_inc_ref(v_type_8471_);
                        v___x_8481_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_8471_, v___x_8479_, v___f_8478_, v___x_8480_, v___x_8480_, v___y_8451_, v___y_8452_, v___y_8453_, v___y_8454_, v___y_8455_, v___y_8456_);
                        if lean_obj_tag(v___x_8481_) == 0 {
                            v_a_8482_ = lean_ctor_get(v___x_8481_, 0);
                            lean_inc(v_a_8482_);
                            lean_dec_ref_known(v___x_8481_, 1);
                            v_lctx_8483_ = lean_ctor_get(v___y_8453_, 2);
                            v_localInstances_8484_ = lean_ctor_get(v___y_8453_, 3);
                            v___x_8485_ = lean_array_get_size(v_a_8482_);
                            v___x_8486_ = lean_mk_empty_array_with_capacity(v___x_8485_);
                            lean_inc(v_levelParams_8470_);
                            v___x_8487_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_8438_, v_a_8469_, v_levelParams_8470_, v_a_8482_, v___x_8485_, v___x_8461_, v___x_8486_);
                            lean_dec(v_a_8482_);
                            lean_dec(v_a_8469_);
                            lean_inc_ref(v_localInstances_8484_);
                            lean_inc_ref(v_lctx_8483_);
                            v___x_8488_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_8488_, 0, v_lctx_8483_);
                            lean_ctor_set(v___x_8488_, 1, v_localInstances_8484_);
                            v___x_8489_ = l_Lean_Elab_partialFixpoint(
                                v___x_8488_,
                                v___x_8487_,
                                v___y_8451_,
                                v___y_8452_,
                                v___y_8453_,
                                v___y_8454_,
                                v___y_8455_,
                                v___y_8456_,
                            );
                            if lean_obj_tag(v___x_8489_) == 0 {
                                lean_dec_ref_known(v___x_8489_, 1);
                                lean_inc(v_a_8460_);
                                v___x_8490_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_8460_, v___y_8453_, v___y_8454_, v___y_8455_, v___y_8456_);
                                if lean_obj_tag(v___x_8490_) == 0 {
                                    lean_dec_ref_known(v___x_8490_, 1);
                                    lean_inc(v_a_8460_);
                                    v___x_8491_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_8466_, v_a_8460_, v_coinductiveElabData_8438_, v___y_8451_, v___y_8452_, v___y_8453_, v___y_8454_, v___y_8455_, v___y_8456_);
                                    if lean_obj_tag(v___x_8491_) == 0 {
                                        lean_dec_ref_known(v___x_8491_, 1);
                                        v___x_8492_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_8460_, v___y_8453_, v___y_8454_, v___y_8455_, v___y_8456_);
                                        return v___x_8492_;
                                    } else {
                                        lean_dec(v_a_8460_);
                                        return v___x_8491_;
                                    }
                                } else {
                                    lean_dec(v___x_8466_);
                                    lean_dec(v_a_8460_);
                                    lean_dec_ref(v_coinductiveElabData_8438_);
                                    return v___x_8490_;
                                }
                            } else {
                                lean_dec(v___x_8466_);
                                lean_dec(v_a_8460_);
                                lean_dec_ref(v_coinductiveElabData_8438_);
                                return v___x_8489_;
                            }
                        } else {
                            lean_dec(v_a_8469_);
                            lean_dec(v___x_8466_);
                            lean_dec(v_a_8460_);
                            lean_dec_ref(v_coinductiveElabData_8438_);
                            v_a_8493_ = lean_ctor_get(v___x_8481_, 0);
                            v_isSharedCheck_8500_ = (!lean_is_exclusive(v___x_8481_)) as u8;
                            if v_isSharedCheck_8500_ == 0 {
                                v___x_8495_ = v___x_8481_;
                                v_isShared_8496_ = v_isSharedCheck_8500_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_8493_);
                                lean_dec(v___x_8481_);
                                v___x_8495_ = lean_box(0);
                                v_isShared_8496_ = v_isSharedCheck_8500_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_8466_);
                        lean_dec(v_a_8460_);
                        lean_dec_ref(v_coinductiveElabData_8438_);
                        v_a_8501_ = lean_ctor_get(v___x_8468_, 0);
                        v_isSharedCheck_8508_ = (!lean_is_exclusive(v___x_8468_)) as u8;
                        if v_isSharedCheck_8508_ == 0 {
                            v___x_8503_ = v___x_8468_;
                            v_isShared_8504_ = v_isSharedCheck_8508_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_8501_);
                            lean_dec(v___x_8468_);
                            v___x_8503_ = lean_box(0);
                            v_isShared_8504_ = v_isSharedCheck_8508_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_coinductiveElabData_8438_);
                    v_a_8509_ = lean_ctor_get(v___x_8459_, 0);
                    v_isSharedCheck_8516_ = (!lean_is_exclusive(v___x_8459_)) as u8;
                    if v_isSharedCheck_8516_ == 0 {
                        v___x_8511_ = v___x_8459_;
                        v_isShared_8512_ = v_isSharedCheck_8516_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8509_);
                        lean_dec(v___x_8459_);
                        v___x_8511_ = lean_box(0);
                        v_isShared_8512_ = v_isSharedCheck_8516_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8496_ == 0 {
                    v___x_8498_ = v___x_8495_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8499_, 0, v_a_8493_);
                    v___x_8498_ = v_reuseFailAlloc_8499_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8498_;
            }
            4 => {
                if v_isShared_8504_ == 0 {
                    v___x_8506_ = v___x_8503_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8507_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8507_, 0, v_a_8501_);
                    v___x_8506_ = v_reuseFailAlloc_8507_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8506_;
            }
            6 => {
                if v_isShared_8512_ == 0 {
                    v___x_8514_ = v___x_8511_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8515_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8515_, 0, v_a_8509_);
                    v___x_8514_ = v_reuseFailAlloc_8515_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCoinductive___boxed(
    mut v_coinductiveElabData_8530_: *mut LeanObject,
    mut v_a_8531_: *mut LeanObject,
    mut v_a_8532_: *mut LeanObject,
    mut v_a_8533_: *mut LeanObject,
    mut v_a_8534_: *mut LeanObject,
    mut v_a_8535_: *mut LeanObject,
    mut v_a_8536_: *mut LeanObject,
    mut v_a_8537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8538_: *mut LeanObject = core::ptr::null_mut();
    v_res_8538_ = l_Lean_Elab_Command_elabCoinductive(
        v_coinductiveElabData_8530_,
        v_a_8531_,
        v_a_8532_,
        v_a_8533_,
        v_a_8534_,
        v_a_8535_,
        v_a_8536_,
    );
    lean_dec(v_a_8536_);
    lean_dec_ref(v_a_8535_);
    lean_dec(v_a_8534_);
    lean_dec_ref(v_a_8533_);
    lean_dec(v_a_8532_);
    lean_dec_ref(v_a_8531_);
    return v_res_8538_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(
    mut v___x_8539_: *mut LeanObject,
    mut v___x_8540_: *mut LeanObject,
    mut v_params_8541_: *mut LeanObject,
    mut v_sz_8542_: usize,
    mut v_i_8543_: usize,
    mut v_bs_8544_: *mut LeanObject,
    mut v___y_8545_: *mut LeanObject,
    mut v___y_8546_: *mut LeanObject,
    mut v___y_8547_: *mut LeanObject,
    mut v___y_8548_: *mut LeanObject,
    mut v___y_8549_: *mut LeanObject,
    mut v___y_8550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8552_: *mut LeanObject = core::ptr::null_mut();
    v___x_8552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_8539_, v___x_8540_, v_params_8541_, v_sz_8542_, v_i_8543_, v_bs_8544_, v___y_8547_, v___y_8548_, v___y_8549_, v___y_8550_);
    return v___x_8552_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(
    mut v___x_8553_: *mut LeanObject,
    mut v___x_8554_: *mut LeanObject,
    mut v_params_8555_: *mut LeanObject,
    mut v_sz_8556_: *mut LeanObject,
    mut v_i_8557_: *mut LeanObject,
    mut v_bs_8558_: *mut LeanObject,
    mut v___y_8559_: *mut LeanObject,
    mut v___y_8560_: *mut LeanObject,
    mut v___y_8561_: *mut LeanObject,
    mut v___y_8562_: *mut LeanObject,
    mut v___y_8563_: *mut LeanObject,
    mut v___y_8564_: *mut LeanObject,
    mut v___y_8565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8566_: usize = 0;
    let mut v_i_boxed_8567_: usize = 0;
    let mut v_res_8568_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8566_ = lean_unbox_usize(v_sz_8556_);
    lean_dec(v_sz_8556_);
    v_i_boxed_8567_ = lean_unbox_usize(v_i_8557_);
    lean_dec(v_i_8557_);
    v_res_8568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_8553_, v___x_8554_, v_params_8555_, v_sz_boxed_8566_, v_i_boxed_8567_, v_bs_8558_, v___y_8559_, v___y_8560_, v___y_8561_, v___y_8562_, v___y_8563_, v___y_8564_);
    lean_dec(v___y_8564_);
    lean_dec_ref(v___y_8563_);
    lean_dec(v___y_8562_);
    lean_dec_ref(v___y_8561_);
    lean_dec(v___y_8560_);
    lean_dec_ref(v___y_8559_);
    return v_res_8568_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(
    mut v_coinductiveElabData_8569_: *mut LeanObject,
    mut v_a_8570_: *mut LeanObject,
    mut v___x_8571_: *mut LeanObject,
    mut v_as_8572_: *mut LeanObject,
    mut v_i_8573_: *mut LeanObject,
    mut v_j_8574_: *mut LeanObject,
    mut v_inv_8575_: *mut LeanObject,
    mut v_bs_8576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8577_: *mut LeanObject = core::ptr::null_mut();
    v___x_8577_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(
            v_coinductiveElabData_8569_,
            v_a_8570_,
            v___x_8571_,
            v_as_8572_,
            v_i_8573_,
            v_j_8574_,
            v_bs_8576_,
        );
    return v___x_8577_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(
    mut v_coinductiveElabData_8578_: *mut LeanObject,
    mut v_a_8579_: *mut LeanObject,
    mut v___x_8580_: *mut LeanObject,
    mut v_as_8581_: *mut LeanObject,
    mut v_i_8582_: *mut LeanObject,
    mut v_j_8583_: *mut LeanObject,
    mut v_inv_8584_: *mut LeanObject,
    mut v_bs_8585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8586_: *mut LeanObject = core::ptr::null_mut();
    v_res_8586_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(
        v_coinductiveElabData_8578_,
        v_a_8579_,
        v___x_8580_,
        v_as_8581_,
        v_i_8582_,
        v_j_8583_,
        v_inv_8584_,
        v_bs_8585_,
    );
    lean_dec_ref(v_as_8581_);
    lean_dec_ref(v_a_8579_);
    lean_dec_ref(v_coinductiveElabData_8578_);
    return v_res_8586_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Coinductive(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_UnusedVariables(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default =
        _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default();
    lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default);
    l_Lean_Elab_Command_instInhabitedCoinductiveElabData =
        _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData();
    lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCoinductiveElabData);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Coinductive(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Coinductive(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_UnusedVariables(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Coinductive(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Coinductive(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Coinductive(builtin);
}
