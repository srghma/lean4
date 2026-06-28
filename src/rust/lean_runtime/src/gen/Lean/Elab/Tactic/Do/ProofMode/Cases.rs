// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Cases
// Imports: Lean.Elab.Tactic.Do.ProofMode.MGoal Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.Pure Lean.Elab.Tactic.Do.ProofMode.Focus Lean.Elab.Tactic.Do.ProofMode.Basic
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Name_mkStr5, l_Lean_Name_mkStr6, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_maxRecDepthErrorMessage,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
    l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
    l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal, l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd,
    l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21, l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo,
    l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo, l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp,
    l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName, l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Pure::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Pure,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_expandMacroImpl_x3f;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_betaRev,
    l_Lean_Expr_consumeMData, l_Lean_Expr_isAppOfArity, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkApp7, l_Lean_mkApp8, l_Lean_mkAppB, l_Lean_mkConst,
    l_Lean_mkSort,
};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_mkFreshExprMVar,
    l_Lean_Meta_mkFreshLevelMVar, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::r#gen::Std::Tactic::Do::Syntax::{
    initialize_Std_Tactic_Do_Syntax, l_Lean_Parser_Tactic_MCasesPat_parse___boxed,
    runtime_initialize_Std_Tactic_Do_Syntax,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_lt, lean_string_dec_eq, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,142734480563613395 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15847151208953044930 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7648019047378041818 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5867936518352330385 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5409699204079762053 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14659826576719934041 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4071431237389361899 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17634999261200945788 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,6038015573457448861 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7664676426519081512 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11290445982748949970 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16617897391613630551 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7843916627258953971 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16668816239785169145 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1276541560985212704 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4709293993499401857 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17764915872583942180 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14564946645751684478 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2613367005446990307 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14660631227684585679 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5465150556496429213 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3067006782463195778 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 723085142 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,12553131995450129664 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18336192281881472727 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6252459286569296447 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5237802591145334394 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [98, 105, 101, 110, 116, 97, 105, 108, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value:
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
    m_data: [114, 101, 102, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8550510443043304393 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value)
            as *mut crate::leanh::LeanObject,
        14477891125163417350 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [73, 115, 65, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value)
            as *mut crate::leanh::LeanObject,
        3381711156881085428 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [116, 111, 95, 97, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value)
            as *mut crate::leanh::LeanObject,
        3381711156881085428 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value)
            as *mut crate::leanh::LeanObject,
        60168100728142487 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [97, 100, 100, 95, 103, 111, 97, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7951832776404106944 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_4)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6910639143271370906 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [73, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 72, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 106, 117, 110, 99, 116, 105, 111, 110, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 120, 105, 115, 116, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5985446289347889015 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        78, 111, 116, 32, 97, 110, 32, 101, 120, 105, 115, 116, 101, 110, 116, 105, 97, 108, 32,
        113, 117, 97, 110, 116, 105, 102, 105, 101, 114, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [97, 110, 100, 95, 49, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7951832776404106944 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_4
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9067151829802160435 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 117, 114, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 104, 109, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [73, 115, 80, 117, 114, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value) as *mut crate::leanh::LeanObject,13332341187416043682 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject,18273640022974733293 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value:
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
    m_data: [112, 117, 114, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7951832776404106944 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        3096500988654044041 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 108, 101, 97, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7951832776404106944 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10222155196932631968 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [97, 110, 100, 95, 50, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7951832776404106944 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15714647072058212852 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [97, 110, 100, 95, 51, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7951832776404106944 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_4
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        4725788427437577091 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4_value:
    crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        78, 101, 105, 116, 104, 101, 114, 32, 97, 32, 99, 111, 110, 106, 117, 110, 99, 116, 105,
        111, 110, 32, 110, 111, 114, 32, 97, 110, 32, 101, 120, 105, 115, 116, 101, 110, 116, 105,
        97, 108, 32, 113, 117, 97, 110, 116, 105, 102, 105, 101, 114, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6_value:
    crate::leanh::LeanStringObject<67> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 67,
    m_capacity: 67,
    m_length: 66,
    m_data: [
        99, 97, 110, 110, 111, 116, 32, 102, 117, 114, 116, 104, 101, 114, 32, 100, 101, 115, 116,
        114, 117, 99, 116, 32, 97, 32, 116, 101, 114, 109, 32, 97, 102, 116, 101, 114, 32, 109,
        111, 118, 105, 110, 103, 32, 105, 116, 32, 116, 111, 32, 116, 104, 101, 32, 76, 101, 97,
        110, 32, 99, 111, 110, 116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [111, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        4341430929543422322 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        78, 111, 116, 32, 97, 32, 100, 105, 115, 106, 117, 110, 99, 116, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        97, 110, 100, 95, 111, 114, 95, 101, 108, 105, 109, 95, 114, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
        1847820319560413069 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 99, 97, 115, 101, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value)
            as *mut crate::leanh::LeanObject,
        1713051840268779758 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value)
            as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value) as *mut crate::leanh::LeanObject,7471086871523061247 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3432_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
    v___x_3433_ = 0;
    v___x_3434_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
    v___x_3435_ = l_Lean_registerTraceClass(v___x_3432_, v___x_3433_, v___x_3434_);
    return v___x_3435_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2____boxed(
    mut v_a_3436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3437_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
    return v_res_3437_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(
    mut v_u_3467_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_3468_: *mut crate::leanh::LeanObject,
    mut v_H_3469_: *mut crate::leanh::LeanObject,
    mut v_a_3470_: *mut crate::leanh::LeanObject,
    mut v_a_3471_: *mut crate::leanh::LeanObject,
    mut v_a_3472_: *mut crate::leanh::LeanObject,
    mut v_a_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3477_: u8 = 0;
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: u8 = 0;
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v_snd_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3494_: u8 = 0;
    let mut v_snd_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v_fst_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_unused_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3526_: u8 = 0;
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3550_: u8 = 0;
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut v_a_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3564_: u8 = 0;
    let mut v_a_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3485_ = l_Lean_Expr_consumeMData(v_H_3469_);
                v___x_3486_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v___x_3485_);
                crate::leanh::lean_dec_ref(v___x_3485_);
                if crate::leanh::lean_obj_tag(v___x_3486_) == 1 {
                    v_val_3487_ = crate::leanh::lean_ctor_get(v___x_3486_, 0);
                    v_isSharedCheck_3526_ = (!crate::leanh::lean_is_exclusive(v___x_3486_)) as u8;
                    if v_isSharedCheck_3526_ == 0 {
                        v___x_3489_ = v___x_3486_;
                        v_isShared_3490_ = v_isSharedCheck_3526_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3487_);
                        crate::leanh::lean_dec(v___x_3486_);
                        v___x_3489_ = crate::leanh::lean_box(0);
                        v_isShared_3490_ = v_isSharedCheck_3526_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3486_);
                    v___x_3527_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5;
                    v___x_3528_ = crate::leanh::lean_box(0);
                    v___x_3529_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3529_, 0, v_u_3467_);
                    crate::leanh::lean_ctor_set(v___x_3529_, 1, v___x_3528_);
                    crate::leanh::lean_inc_ref(v___x_3529_);
                    v___x_3530_ = l_Lean_mkConst(v___x_3527_, v___x_3529_);
                    crate::leanh::lean_inc_ref(v_00_u03c3s_3468_);
                    v___x_3531_ = l_Lean_Expr_app___override(v___x_3530_, v_00_u03c3s_3468_);
                    v___x_3532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3532_, 0, v___x_3531_);
                    v___x_3533_ = 0;
                    v___x_3534_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v___x_3532_);
                    v___x_3535_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_3532_,
                        v___x_3533_,
                        v___x_3534_,
                        v_a_3470_,
                        v_a_3471_,
                        v_a_3472_,
                        v_a_3473_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3535_) == 0 {
                        v_a_3536_ = crate::leanh::lean_ctor_get(v___x_3535_, 0);
                        crate::leanh::lean_inc(v_a_3536_);
                        crate::leanh::lean_dec_ref_known(v___x_3535_, 1);
                        v___x_3537_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_3532_,
                            v___x_3533_,
                            v___x_3534_,
                            v_a_3470_,
                            v_a_3471_,
                            v_a_3472_,
                            v_a_3473_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3537_) == 0 {
                            v_a_3538_ = crate::leanh::lean_ctor_get(v___x_3537_, 0);
                            v_isSharedCheck_3564_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3537_)) as u8;
                            if v_isSharedCheck_3564_ == 0 {
                                v___x_3540_ = v___x_3537_;
                                v_isShared_3541_ = v_isSharedCheck_3564_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3538_);
                                crate::leanh::lean_dec(v___x_3537_);
                                v___x_3540_ = crate::leanh::lean_box(0);
                                v_isShared_3541_ = v_isSharedCheck_3564_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3536_);
                            crate::leanh::lean_dec_ref_known(v___x_3529_, 2);
                            crate::leanh::lean_dec_ref(v_H_3469_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_3468_);
                            v_a_3565_ = crate::leanh::lean_ctor_get(v___x_3537_, 0);
                            crate::leanh::lean_inc(v_a_3565_);
                            crate::leanh::lean_dec_ref_known(v___x_3537_, 1);
                            v_a_3482_ = v_a_3565_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_3532_, 1);
                        crate::leanh::lean_dec_ref_known(v___x_3529_, 2);
                        crate::leanh::lean_dec_ref(v_H_3469_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_3468_);
                        v_a_3566_ = crate::leanh::lean_ctor_get(v___x_3535_, 0);
                        crate::leanh::lean_inc(v_a_3566_);
                        crate::leanh::lean_dec_ref_known(v___x_3535_, 1);
                        v_a_3482_ = v_a_3566_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3477_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3476_);
                    v___x_3478_ = crate::leanh::lean_box(0);
                    v___x_3479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3479_, 0, v___x_3478_);
                    return v___x_3479_;
                } else {
                    v___x_3480_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3480_, 0, v___y_3476_);
                    return v___x_3480_;
                }
            }
            2 => {
                v___x_3483_ = l_Lean_Exception_isInterrupt(v_a_3482_);
                if v___x_3483_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3482_);
                    v___x_3484_ = l_Lean_Exception_isRuntime(v_a_3482_);
                    v___y_3476_ = v_a_3482_;
                    v___y_3477_ = v___x_3484_;
                    state = 1;
                    continue;
                } else {
                    v___y_3476_ = v_a_3482_;
                    v___y_3477_ = v___x_3483_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_snd_3491_ = crate::leanh::lean_ctor_get(v_val_3487_, 1);
                v_isSharedCheck_3524_ = (!crate::leanh::lean_is_exclusive(v_val_3487_)) as u8;
                if v_isSharedCheck_3524_ == 0 {
                    v_unused_3525_ = crate::leanh::lean_ctor_get(v_val_3487_, 0);
                    crate::leanh::lean_dec(v_unused_3525_);
                    v___x_3493_ = v_val_3487_;
                    v_isShared_3494_ = v_isSharedCheck_3524_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3491_);
                    crate::leanh::lean_dec(v_val_3487_);
                    v___x_3493_ = crate::leanh::lean_box(0);
                    v_isShared_3494_ = v_isSharedCheck_3524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_snd_3495_ = crate::leanh::lean_ctor_get(v_snd_3491_, 1);
                v_isSharedCheck_3522_ = (!crate::leanh::lean_is_exclusive(v_snd_3491_)) as u8;
                if v_isSharedCheck_3522_ == 0 {
                    v_unused_3523_ = crate::leanh::lean_ctor_get(v_snd_3491_, 0);
                    crate::leanh::lean_dec(v_unused_3523_);
                    v___x_3497_ = v_snd_3491_;
                    v_isShared_3498_ = v_isSharedCheck_3522_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3495_);
                    crate::leanh::lean_dec(v_snd_3491_);
                    v___x_3497_ = crate::leanh::lean_box(0);
                    v_isShared_3498_ = v_isSharedCheck_3522_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_3499_ = crate::leanh::lean_ctor_get(v_snd_3495_, 0);
                v_snd_3500_ = crate::leanh::lean_ctor_get(v_snd_3495_, 1);
                v_isSharedCheck_3521_ = (!crate::leanh::lean_is_exclusive(v_snd_3495_)) as u8;
                if v_isSharedCheck_3521_ == 0 {
                    v___x_3502_ = v_snd_3495_;
                    v_isShared_3503_ = v_isSharedCheck_3521_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3500_);
                    crate::leanh::lean_inc(v_fst_3499_);
                    crate::leanh::lean_dec(v_snd_3495_);
                    v___x_3502_ = crate::leanh::lean_box(0);
                    v_isShared_3503_ = v_isSharedCheck_3521_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3504_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4;
                v___x_3505_ = crate::leanh::lean_box(0);
                if v_isShared_3494_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3493_, 1);
                    crate::leanh::lean_ctor_set(v___x_3493_, 1, v___x_3505_);
                    crate::leanh::lean_ctor_set(v___x_3493_, 0, v_u_3467_);
                    v___x_3507_ = v___x_3493_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_u_3467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3520_, 1, v___x_3505_);
                    v___x_3507_ = v_reuseFailAlloc_3520_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3508_ = l_Lean_mkConst(v___x_3504_, v___x_3507_);
                v___x_3509_ = l_Lean_mkAppB(v___x_3508_, v_00_u03c3s_3468_, v_H_3469_);
                if v_isShared_3503_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3502_, 1, v___x_3509_);
                    crate::leanh::lean_ctor_set(v___x_3502_, 0, v_snd_3500_);
                    v___x_3511_ = v___x_3502_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_snd_3500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 1, v___x_3509_);
                    v___x_3511_ = v_reuseFailAlloc_3519_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3497_, 1, v___x_3511_);
                    crate::leanh::lean_ctor_set(v___x_3497_, 0, v_fst_3499_);
                    v___x_3513_ = v___x_3497_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3518_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_fst_3499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___x_3511_);
                    v___x_3513_ = v_reuseFailAlloc_3518_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3490_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3489_, 0, v___x_3513_);
                    v___x_3515_ = v___x_3489_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3513_);
                    v___x_3515_ = v_reuseFailAlloc_3517_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3516_, 0, v___x_3515_);
                return v___x_3516_;
            }
            11 => {
                v___x_3542_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7;
                crate::leanh::lean_inc_ref(v___x_3529_);
                v___x_3543_ = l_Lean_mkConst(v___x_3542_, v___x_3529_);
                crate::leanh::lean_inc(v_a_3538_);
                crate::leanh::lean_inc(v_a_3536_);
                crate::leanh::lean_inc_ref(v_H_3469_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_3468_);
                v___x_3544_ = l_Lean_mkApp4(
                    v___x_3543_,
                    v_00_u03c3s_3468_,
                    v_H_3469_,
                    v_a_3536_,
                    v_a_3538_,
                );
                v___x_3545_ = crate::leanh::lean_box(0);
                v___x_3546_ = l_Lean_Meta_synthInstance(
                    v___x_3544_,
                    v___x_3545_,
                    v_a_3470_,
                    v_a_3471_,
                    v_a_3472_,
                    v_a_3473_,
                );
                if crate::leanh::lean_obj_tag(v___x_3546_) == 0 {
                    v_a_3547_ = crate::leanh::lean_ctor_get(v___x_3546_, 0);
                    v_isSharedCheck_3562_ = (!crate::leanh::lean_is_exclusive(v___x_3546_)) as u8;
                    if v_isSharedCheck_3562_ == 0 {
                        v___x_3549_ = v___x_3546_;
                        v_isShared_3550_ = v_isSharedCheck_3562_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3547_);
                        crate::leanh::lean_dec(v___x_3546_);
                        v___x_3549_ = crate::leanh::lean_box(0);
                        v_isShared_3550_ = v_isSharedCheck_3562_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3540_);
                    crate::leanh::lean_dec(v_a_3538_);
                    crate::leanh::lean_dec(v_a_3536_);
                    crate::leanh::lean_dec_ref_known(v___x_3529_, 2);
                    crate::leanh::lean_dec_ref(v_H_3469_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_3468_);
                    v_a_3563_ = crate::leanh::lean_ctor_get(v___x_3546_, 0);
                    crate::leanh::lean_inc(v_a_3563_);
                    crate::leanh::lean_dec_ref_known(v___x_3546_, 1);
                    v_a_3482_ = v_a_3563_;
                    state = 2;
                    continue;
                }
            }
            12 => {
                v___x_3551_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9;
                v___x_3552_ = l_Lean_mkConst(v___x_3551_, v___x_3529_);
                crate::leanh::lean_inc(v_a_3538_);
                crate::leanh::lean_inc(v_a_3536_);
                v___x_3553_ = l_Lean_mkApp5(
                    v___x_3552_,
                    v_00_u03c3s_3468_,
                    v_H_3469_,
                    v_a_3536_,
                    v_a_3538_,
                    v_a_3547_,
                );
                v___x_3554_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3554_, 0, v_a_3538_);
                crate::leanh::lean_ctor_set(v___x_3554_, 1, v___x_3553_);
                v___x_3555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3555_, 0, v_a_3536_);
                crate::leanh::lean_ctor_set(v___x_3555_, 1, v___x_3554_);
                if v_isShared_3541_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3540_, 1);
                    crate::leanh::lean_ctor_set(v___x_3540_, 0, v___x_3555_);
                    v___x_3557_ = v___x_3540_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3555_);
                    v___x_3557_ = v_reuseFailAlloc_3561_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3550_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3549_, 0, v___x_3557_);
                    v___x_3559_ = v___x_3549_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3560_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
                    v___x_3559_ = v_reuseFailAlloc_3560_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___boxed(
    mut v_u_3567_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_3568_: *mut crate::leanh::LeanObject,
    mut v_H_3569_: *mut crate::leanh::LeanObject,
    mut v_a_3570_: *mut crate::leanh::LeanObject,
    mut v_a_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3575_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(
        v_u_3567_,
        v_00_u03c3s_3568_,
        v_H_3569_,
        v_a_3570_,
        v_a_3571_,
        v_a_3572_,
        v_a_3573_,
    );
    crate::leanh::lean_dec(v_a_3573_);
    crate::leanh::lean_dec_ref(v_a_3572_);
    crate::leanh::lean_dec(v_a_3571_);
    crate::leanh::lean_dec_ref(v_a_3570_);
    return v_res_3575_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(
    mut v_u_3584_: *mut crate::leanh::LeanObject,
    mut v_goals_3585_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_3586_: *mut crate::leanh::LeanObject,
    mut v_T_3587_: *mut crate::leanh::LeanObject,
    mut v_Q_3588_: *mut crate::leanh::LeanObject,
    mut v_H_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
    mut v_a_3591_: *mut crate::leanh::LeanObject,
    mut v_a_3592_: *mut crate::leanh::LeanObject,
    mut v_a_3593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3600_: u8 = 0;
    let mut v_goal_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3608_: u8 = 0;
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v_a_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3636_: u8 = 0;
    let mut v_isSharedCheck_3637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_H_3589_);
                crate::leanh::lean_inc_ref(v_Q_3588_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_3586_);
                crate::leanh::lean_inc(v_u_3584_);
                v___x_3595_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_u_3584_,
                    v_00_u03c3s_3586_,
                    v_Q_3588_,
                    v_H_3589_,
                );
                v_fst_3596_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                v_snd_3597_ = crate::leanh::lean_ctor_get(v___x_3595_, 1);
                v_isSharedCheck_3637_ = (!crate::leanh::lean_is_exclusive(v___x_3595_)) as u8;
                if v_isSharedCheck_3637_ == 0 {
                    v___x_3599_ = v___x_3595_;
                    v_isShared_3600_ = v_isSharedCheck_3637_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3597_);
                    crate::leanh::lean_inc(v_fst_3596_);
                    crate::leanh::lean_dec(v___x_3595_);
                    v___x_3599_ = crate::leanh::lean_box(0);
                    v_isShared_3600_ = v_isSharedCheck_3637_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_T_3587_);
                crate::leanh::lean_inc(v_fst_3596_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_3586_);
                crate::leanh::lean_inc(v_u_3584_);
                v_goal_3601_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v_goal_3601_, 0, v_u_3584_);
                crate::leanh::lean_ctor_set(v_goal_3601_, 1, v_00_u03c3s_3586_);
                crate::leanh::lean_ctor_set(v_goal_3601_, 2, v_fst_3596_);
                crate::leanh::lean_ctor_set(v_goal_3601_, 3, v_T_3587_);
                v___x_3602_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_3601_);
                v___x_3603_ = crate::leanh::lean_box(0);
                v___x_3604_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_3602_,
                    v___x_3603_,
                    v_a_3590_,
                    v_a_3591_,
                    v_a_3592_,
                    v_a_3593_,
                );
                if crate::leanh::lean_obj_tag(v___x_3604_) == 0 {
                    v_a_3605_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
                    v_isSharedCheck_3628_ = (!crate::leanh::lean_is_exclusive(v___x_3604_)) as u8;
                    if v_isSharedCheck_3628_ == 0 {
                        v___x_3607_ = v___x_3604_;
                        v_isShared_3608_ = v_isSharedCheck_3628_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3605_);
                        crate::leanh::lean_dec(v___x_3604_);
                        v___x_3607_ = crate::leanh::lean_box(0);
                        v_isShared_3608_ = v_isSharedCheck_3628_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3599_);
                    crate::leanh::lean_dec(v_snd_3597_);
                    crate::leanh::lean_dec(v_fst_3596_);
                    crate::leanh::lean_dec_ref(v_H_3589_);
                    crate::leanh::lean_dec_ref(v_Q_3588_);
                    crate::leanh::lean_dec_ref(v_T_3587_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_3586_);
                    crate::leanh::lean_dec(v_u_3584_);
                    v_a_3629_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
                    v_isSharedCheck_3636_ = (!crate::leanh::lean_is_exclusive(v___x_3604_)) as u8;
                    if v_isSharedCheck_3636_ == 0 {
                        v___x_3631_ = v___x_3604_;
                        v_isShared_3632_ = v_isSharedCheck_3636_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3629_);
                        crate::leanh::lean_dec(v___x_3604_);
                        v___x_3631_ = crate::leanh::lean_box(0);
                        v_isShared_3632_ = v_isSharedCheck_3636_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3609_ = lean_st_ref_take(v_goals_3585_);
                v___x_3610_ = l_Lean_Expr_mvarId_x21(v_a_3605_);
                v___x_3611_ = lean_array_push(v___x_3609_, v___x_3610_);
                v___x_3612_ = lean_st_ref_set(v_goals_3585_, v___x_3611_);
                v___x_3613_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1;
                v___x_3614_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_u_3584_, 2);
                v___x_3615_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3615_, 0, v_u_3584_);
                crate::leanh::lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                v___x_3616_ = l_Lean_mkConst(v___x_3613_, v___x_3615_);
                crate::leanh::lean_inc_ref(v_T_3587_);
                crate::leanh::lean_inc_ref(v_H_3589_);
                crate::leanh::lean_inc_ref(v_Q_3588_);
                crate::leanh::lean_inc_ref_n(v_00_u03c3s_3586_, 2);
                v___x_3617_ = l_Lean_mkApp7(
                    v___x_3616_,
                    v_00_u03c3s_3586_,
                    v_fst_3596_,
                    v_Q_3588_,
                    v_H_3589_,
                    v_T_3587_,
                    v_snd_3597_,
                    v_a_3605_,
                );
                v___x_3618_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_3584_,
                    v_00_u03c3s_3586_,
                    v_Q_3588_,
                    v_H_3589_,
                );
                v___x_3619_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3619_, 0, v_u_3584_);
                crate::leanh::lean_ctor_set(v___x_3619_, 1, v_00_u03c3s_3586_);
                crate::leanh::lean_ctor_set(v___x_3619_, 2, v___x_3618_);
                crate::leanh::lean_ctor_set(v___x_3619_, 3, v_T_3587_);
                v___x_3620_ = crate::leanh::lean_box(0);
                if v_isShared_3600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3599_, 1, v___x_3617_);
                    crate::leanh::lean_ctor_set(v___x_3599_, 0, v___x_3619_);
                    v___x_3622_ = v___x_3599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___x_3617_);
                    v___x_3622_ = v_reuseFailAlloc_3627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3623_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3623_, 0, v___x_3620_);
                crate::leanh::lean_ctor_set(v___x_3623_, 1, v___x_3622_);
                if v_isShared_3608_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3607_, 0, v___x_3623_);
                    v___x_3625_ = v___x_3607_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
                    v___x_3625_ = v_reuseFailAlloc_3626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3625_;
            }
            5 => {
                if v_isShared_3632_ == 0 {
                    v___x_3634_ = v___x_3631_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
                    v___x_3634_ = v_reuseFailAlloc_3635_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed(
    mut v_u_3638_: *mut crate::leanh::LeanObject,
    mut v_goals_3639_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_3640_: *mut crate::leanh::LeanObject,
    mut v_T_3641_: *mut crate::leanh::LeanObject,
    mut v_Q_3642_: *mut crate::leanh::LeanObject,
    mut v_H_3643_: *mut crate::leanh::LeanObject,
    mut v_a_3644_: *mut crate::leanh::LeanObject,
    mut v_a_3645_: *mut crate::leanh::LeanObject,
    mut v_a_3646_: *mut crate::leanh::LeanObject,
    mut v_a_3647_: *mut crate::leanh::LeanObject,
    mut v_a_3648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3649_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(
        v_u_3638_,
        v_goals_3639_,
        v_00_u03c3s_3640_,
        v_T_3641_,
        v_Q_3642_,
        v_H_3643_,
        v_a_3644_,
        v_a_3645_,
        v_a_3646_,
        v_a_3647_,
    );
    crate::leanh::lean_dec(v_a_3647_);
    crate::leanh::lean_dec_ref(v_a_3646_);
    crate::leanh::lean_dec(v_a_3645_);
    crate::leanh::lean_dec_ref(v_a_3644_);
    crate::leanh::lean_dec(v_goals_3639_);
    return v_res_3649_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(
    mut v_msgData_3650_: *mut crate::leanh::LeanObject,
    mut v___y_3651_: *mut crate::leanh::LeanObject,
    mut v___y_3652_: *mut crate::leanh::LeanObject,
    mut v___y_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3656_ = lean_st_ref_get(v___y_3654_);
    v_env_3657_ = crate::leanh::lean_ctor_get(v___x_3656_, 0);
    crate::leanh::lean_inc_ref(v_env_3657_);
    crate::leanh::lean_dec(v___x_3656_);
    v___x_3658_ = lean_st_ref_get(v___y_3652_);
    v_mctx_3659_ = crate::leanh::lean_ctor_get(v___x_3658_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3659_);
    crate::leanh::lean_dec(v___x_3658_);
    v_lctx_3660_ = crate::leanh::lean_ctor_get(v___y_3651_, 2);
    v_options_3661_ = crate::leanh::lean_ctor_get(v___y_3653_, 2);
    crate::leanh::lean_inc_ref(v_options_3661_);
    crate::leanh::lean_inc_ref(v_lctx_3660_);
    v___x_3662_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3662_, 0, v_env_3657_);
    crate::leanh::lean_ctor_set(v___x_3662_, 1, v_mctx_3659_);
    crate::leanh::lean_ctor_set(v___x_3662_, 2, v_lctx_3660_);
    crate::leanh::lean_ctor_set(v___x_3662_, 3, v_options_3661_);
    v___x_3663_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3663_, 0, v___x_3662_);
    crate::leanh::lean_ctor_set(v___x_3663_, 1, v_msgData_3650_);
    v___x_3664_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3664_, 0, v___x_3663_);
    return v___x_3664_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0___boxed(
    mut v_msgData_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msgData_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
    crate::leanh::lean_dec(v___y_3669_);
    crate::leanh::lean_dec_ref(v___y_3668_);
    crate::leanh::lean_dec(v___y_3667_);
    crate::leanh::lean_dec_ref(v___y_3666_);
    return v_res_3671_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(
    mut v_msg_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
    mut v___y_3674_: *mut crate::leanh::LeanObject,
    mut v___y_3675_: *mut crate::leanh::LeanObject,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3683_: u8 = 0;
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3678_ = crate::leanh::lean_ctor_get(v___y_3675_, 5);
                v___x_3679_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
                v_a_3680_ = crate::leanh::lean_ctor_get(v___x_3679_, 0);
                v_isSharedCheck_3688_ = (!crate::leanh::lean_is_exclusive(v___x_3679_)) as u8;
                if v_isSharedCheck_3688_ == 0 {
                    v___x_3682_ = v___x_3679_;
                    v_isShared_3683_ = v_isSharedCheck_3688_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3680_);
                    crate::leanh::lean_dec(v___x_3679_);
                    v___x_3682_ = crate::leanh::lean_box(0);
                    v_isShared_3683_ = v_isSharedCheck_3688_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3678_);
                v___x_3684_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3684_, 0, v_ref_3678_);
                crate::leanh::lean_ctor_set(v___x_3684_, 1, v_a_3680_);
                if v_isShared_3683_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3682_, 1);
                    crate::leanh::lean_ctor_set(v___x_3682_, 0, v___x_3684_);
                    v___x_3686_ = v___x_3682_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
                    v___x_3686_ = v_reuseFailAlloc_3687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg___boxed(
    mut v_msg_3689_: *mut crate::leanh::LeanObject,
    mut v___y_3690_: *mut crate::leanh::LeanObject,
    mut v___y_3691_: *mut crate::leanh::LeanObject,
    mut v___y_3692_: *mut crate::leanh::LeanObject,
    mut v___y_3693_: *mut crate::leanh::LeanObject,
    mut v___y_3694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3695_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
    crate::leanh::lean_dec(v___y_3693_);
    crate::leanh::lean_dec_ref(v___y_3692_);
    crate::leanh::lean_dec(v___y_3691_);
    crate::leanh::lean_dec_ref(v___y_3690_);
    return v_res_3695_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(
    mut v_goal_3699_: *mut crate::leanh::LeanObject,
    mut v_a_3700_: *mut crate::leanh::LeanObject,
    mut v_a_3701_: *mut crate::leanh::LeanObject,
    mut v_a_3702_: *mut crate::leanh::LeanObject,
    mut v_a_3703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hyps_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v_snd_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hyps_3705_ = crate::leanh::lean_ctor_get(v_goal_3699_, 2);
                crate::leanh::lean_inc_ref(v_hyps_3705_);
                crate::leanh::lean_dec_ref(v_goal_3699_);
                v___x_3706_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_hyps_3705_);
                if crate::leanh::lean_obj_tag(v___x_3706_) == 1 {
                    crate::leanh::lean_dec_ref(v_hyps_3705_);
                    v_val_3707_ = crate::leanh::lean_ctor_get(v___x_3706_, 0);
                    v_isSharedCheck_3716_ = (!crate::leanh::lean_is_exclusive(v___x_3706_)) as u8;
                    if v_isSharedCheck_3716_ == 0 {
                        v___x_3709_ = v___x_3706_;
                        v_isShared_3710_ = v_isSharedCheck_3716_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3707_);
                        crate::leanh::lean_dec(v___x_3706_);
                        v___x_3709_ = crate::leanh::lean_box(0);
                        v_isShared_3710_ = v_isSharedCheck_3716_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3706_);
                    v___x_3717_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1);
                    v___x_3718_ = l_Lean_MessageData_ofExpr(v_hyps_3705_);
                    v___x_3719_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3719_, 0, v___x_3717_);
                    crate::leanh::lean_ctor_set(v___x_3719_, 1, v___x_3718_);
                    v___x_3720_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_3719_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
                    return v___x_3720_;
                }
            }
            1 => {
                v_snd_3711_ = crate::leanh::lean_ctor_get(v_val_3707_, 1);
                crate::leanh::lean_inc(v_snd_3711_);
                crate::leanh::lean_dec(v_val_3707_);
                v_snd_3712_ = crate::leanh::lean_ctor_get(v_snd_3711_, 1);
                crate::leanh::lean_inc(v_snd_3712_);
                crate::leanh::lean_dec(v_snd_3711_);
                if v_isShared_3710_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3709_, 0);
                    crate::leanh::lean_ctor_set(v___x_3709_, 0, v_snd_3712_);
                    v___x_3714_ = v___x_3709_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_snd_3712_);
                    v___x_3714_ = v_reuseFailAlloc_3715_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___boxed(
    mut v_goal_3721_: *mut crate::leanh::LeanObject,
    mut v_a_3722_: *mut crate::leanh::LeanObject,
    mut v_a_3723_: *mut crate::leanh::LeanObject,
    mut v_a_3724_: *mut crate::leanh::LeanObject,
    mut v_a_3725_: *mut crate::leanh::LeanObject,
    mut v_a_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3727_ =
        l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(
            v_goal_3721_,
            v_a_3722_,
            v_a_3723_,
            v_a_3724_,
            v_a_3725_,
        );
    crate::leanh::lean_dec(v_a_3725_);
    crate::leanh::lean_dec_ref(v_a_3724_);
    crate::leanh::lean_dec(v_a_3723_);
    crate::leanh::lean_dec_ref(v_a_3722_);
    return v_res_3727_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(
    mut v_00_u03b1_3728_: *mut crate::leanh::LeanObject,
    mut v_msg_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
    return v___x_3735_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___boxed(
    mut v_00_u03b1_3736_: *mut crate::leanh::LeanObject,
    mut v_msg_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
    mut v___y_3741_: *mut crate::leanh::LeanObject,
    mut v___y_3742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3743_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(v_00_u03b1_3736_, v_msg_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
    crate::leanh::lean_dec(v___y_3741_);
    crate::leanh::lean_dec_ref(v___y_3740_);
    crate::leanh::lean_dec(v___y_3739_);
    crate::leanh::lean_dec_ref(v___y_3738_);
    return v_res_3743_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(
    mut v___x_3744_: *mut crate::leanh::LeanObject,
    mut v_snd_3745_: *mut crate::leanh::LeanObject,
    mut v_k_3746_: *mut crate::leanh::LeanObject,
    mut v___x_3747_: u8,
    mut v___x_3748_: *mut crate::leanh::LeanObject,
    mut v___x_3749_: *mut crate::leanh::LeanObject,
    mut v___x_3750_: *mut crate::leanh::LeanObject,
    mut v___x_3751_: *mut crate::leanh::LeanObject,
    mut v___x_3752_: *mut crate::leanh::LeanObject,
    mut v___x_3753_: *mut crate::leanh::LeanObject,
    mut v_H_3754_: *mut crate::leanh::LeanObject,
    mut v_x_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: u8 = 0;
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v_fst_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3776_: u8 = 0;
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3793_: u8 = 0;
    let mut v_u_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3799_: u8 = 0;
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v_unused_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3825_: u8 = 0;
    let mut v_a_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3829_: u8 = 0;
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_a_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3837_: u8 = 0;
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3841_: u8 = 0;
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v_unused_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v_isSharedCheck_3853_: u8 = 0;
    let mut v_a_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_3761_ = crate::leanh::lean_ctor_get(v___y_3756_, 2);
                crate::leanh::lean_inc_ref(v___x_3744_);
                v___x_3762_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3762_, 0, v___x_3744_);
                v___x_3763_ = 0;
                crate::leanh::lean_inc_ref(v_x_3755_);
                crate::leanh::lean_inc_ref(v_lctx_3761_);
                v___x_3764_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(
                    v_snd_3745_,
                    v_lctx_3761_,
                    v_x_3755_,
                    v___x_3762_,
                    v___x_3763_,
                    v___y_3756_,
                    v___y_3757_,
                    v___y_3758_,
                    v___y_3759_,
                );
                if crate::leanh::lean_obj_tag(v___x_3764_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3764_, 1);
                    crate::leanh::lean_inc(v___y_3759_);
                    crate::leanh::lean_inc_ref(v___y_3758_);
                    crate::leanh::lean_inc(v___y_3757_);
                    crate::leanh::lean_inc_ref(v___y_3756_);
                    crate::leanh::lean_inc_ref(v_x_3755_);
                    v___x_3765_ = crate::leanh::lean_apply_6(
                        v_k_3746_,
                        v_x_3755_,
                        v___y_3756_,
                        v___y_3757_,
                        v___y_3758_,
                        v___y_3759_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3765_) == 0 {
                        v_a_3766_ = crate::leanh::lean_ctor_get(v___x_3765_, 0);
                        crate::leanh::lean_inc(v_a_3766_);
                        crate::leanh::lean_dec_ref_known(v___x_3765_, 1);
                        v_snd_3767_ = crate::leanh::lean_ctor_get(v_a_3766_, 1);
                        v_fst_3768_ = crate::leanh::lean_ctor_get(v_a_3766_, 0);
                        v_isSharedCheck_3853_ = (!crate::leanh::lean_is_exclusive(v_a_3766_)) as u8;
                        if v_isSharedCheck_3853_ == 0 {
                            v___x_3770_ = v_a_3766_;
                            v_isShared_3771_ = v_isSharedCheck_3853_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3767_);
                            crate::leanh::lean_inc(v_fst_3768_);
                            crate::leanh::lean_dec(v_a_3766_);
                            v___x_3770_ = crate::leanh::lean_box(0);
                            v_isShared_3771_ = v_isSharedCheck_3853_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3755_);
                        crate::leanh::lean_dec_ref(v_H_3754_);
                        crate::leanh::lean_dec_ref(v___x_3753_);
                        crate::leanh::lean_dec_ref(v___x_3752_);
                        crate::leanh::lean_dec_ref(v___x_3751_);
                        crate::leanh::lean_dec_ref(v___x_3750_);
                        crate::leanh::lean_dec_ref(v___x_3749_);
                        crate::leanh::lean_dec_ref(v___x_3748_);
                        crate::leanh::lean_dec_ref(v___x_3744_);
                        return v___x_3765_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3755_);
                    crate::leanh::lean_dec_ref(v_H_3754_);
                    crate::leanh::lean_dec_ref(v___x_3753_);
                    crate::leanh::lean_dec_ref(v___x_3752_);
                    crate::leanh::lean_dec_ref(v___x_3751_);
                    crate::leanh::lean_dec_ref(v___x_3750_);
                    crate::leanh::lean_dec_ref(v___x_3749_);
                    crate::leanh::lean_dec_ref(v___x_3748_);
                    crate::leanh::lean_dec_ref(v_k_3746_);
                    crate::leanh::lean_dec_ref(v___x_3744_);
                    v_a_3854_ = crate::leanh::lean_ctor_get(v___x_3764_, 0);
                    v_isSharedCheck_3861_ = (!crate::leanh::lean_is_exclusive(v___x_3764_)) as u8;
                    if v_isSharedCheck_3861_ == 0 {
                        v___x_3856_ = v___x_3764_;
                        v_isShared_3857_ = v_isSharedCheck_3861_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3854_);
                        crate::leanh::lean_dec(v___x_3764_);
                        v___x_3856_ = crate::leanh::lean_box(0);
                        v_isShared_3857_ = v_isSharedCheck_3861_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3772_ = crate::leanh::lean_ctor_get(v_snd_3767_, 0);
                v_snd_3773_ = crate::leanh::lean_ctor_get(v_snd_3767_, 1);
                v_isSharedCheck_3852_ = (!crate::leanh::lean_is_exclusive(v_snd_3767_)) as u8;
                if v_isSharedCheck_3852_ == 0 {
                    v___x_3775_ = v_snd_3767_;
                    v_isShared_3776_ = v_isSharedCheck_3852_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3773_);
                    crate::leanh::lean_inc(v_fst_3772_);
                    crate::leanh::lean_dec(v_snd_3767_);
                    v___x_3775_ = crate::leanh::lean_box(0);
                    v_isShared_3776_ = v_isSharedCheck_3852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_fst_3772_);
                v___x_3777_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_3772_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
                if crate::leanh::lean_obj_tag(v___x_3777_) == 0 {
                    v_a_3778_ = crate::leanh::lean_ctor_get(v___x_3777_, 0);
                    crate::leanh::lean_inc(v_a_3778_);
                    crate::leanh::lean_dec_ref_known(v___x_3777_, 1);
                    v_fst_3779_ = crate::leanh::lean_ctor_get(v_a_3778_, 0);
                    v_isSharedCheck_3842_ = (!crate::leanh::lean_is_exclusive(v_a_3778_)) as u8;
                    if v_isSharedCheck_3842_ == 0 {
                        v_unused_3843_ = crate::leanh::lean_ctor_get(v_a_3778_, 1);
                        crate::leanh::lean_dec(v_unused_3843_);
                        v___x_3781_ = v_a_3778_;
                        v_isShared_3782_ = v_isSharedCheck_3842_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3779_);
                        crate::leanh::lean_dec(v_a_3778_);
                        v___x_3781_ = crate::leanh::lean_box(0);
                        v_isShared_3782_ = v_isSharedCheck_3842_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3775_);
                    crate::leanh::lean_dec(v_snd_3773_);
                    crate::leanh::lean_dec(v_fst_3772_);
                    crate::leanh::lean_del_object(v___x_3770_);
                    crate::leanh::lean_dec(v_fst_3768_);
                    crate::leanh::lean_dec_ref(v_x_3755_);
                    crate::leanh::lean_dec_ref(v_H_3754_);
                    crate::leanh::lean_dec_ref(v___x_3753_);
                    crate::leanh::lean_dec_ref(v___x_3752_);
                    crate::leanh::lean_dec_ref(v___x_3751_);
                    crate::leanh::lean_dec_ref(v___x_3750_);
                    crate::leanh::lean_dec_ref(v___x_3749_);
                    crate::leanh::lean_dec_ref(v___x_3748_);
                    crate::leanh::lean_dec_ref(v___x_3744_);
                    v_a_3844_ = crate::leanh::lean_ctor_get(v___x_3777_, 0);
                    v_isSharedCheck_3851_ = (!crate::leanh::lean_is_exclusive(v___x_3777_)) as u8;
                    if v_isSharedCheck_3851_ == 0 {
                        v___x_3846_ = v___x_3777_;
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3844_);
                        crate::leanh::lean_dec(v___x_3777_);
                        v___x_3846_ = crate::leanh::lean_box(0);
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 15;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3744_);
                v___x_3783_ = l_Lean_Meta_getLevel(
                    v___x_3744_,
                    v___y_3756_,
                    v___y_3757_,
                    v___y_3758_,
                    v___y_3759_,
                );
                if crate::leanh::lean_obj_tag(v___x_3783_) == 0 {
                    v_a_3784_ = crate::leanh::lean_ctor_get(v___x_3783_, 0);
                    crate::leanh::lean_inc(v_a_3784_);
                    crate::leanh::lean_dec_ref_known(v___x_3783_, 1);
                    v___x_3785_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3786_ = lean_mk_empty_array_with_capacity(v___x_3785_);
                    v___x_3787_ = lean_array_push(v___x_3786_, v_x_3755_);
                    v___x_3788_ = 1;
                    v___x_3789_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_3787_,
                        v_snd_3773_,
                        v___x_3763_,
                        v___x_3747_,
                        v___x_3763_,
                        v___x_3747_,
                        v___x_3788_,
                        v___y_3756_,
                        v___y_3757_,
                        v___y_3758_,
                        v___y_3759_,
                    );
                    crate::leanh::lean_dec_ref(v___x_3787_);
                    if crate::leanh::lean_obj_tag(v___x_3789_) == 0 {
                        v_a_3790_ = crate::leanh::lean_ctor_get(v___x_3789_, 0);
                        v_isSharedCheck_3825_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3789_)) as u8;
                        if v_isSharedCheck_3825_ == 0 {
                            v___x_3792_ = v___x_3789_;
                            v_isShared_3793_ = v_isSharedCheck_3825_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3790_);
                            crate::leanh::lean_dec(v___x_3789_);
                            v___x_3792_ = crate::leanh::lean_box(0);
                            v_isShared_3793_ = v_isSharedCheck_3825_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3784_);
                        crate::leanh::lean_del_object(v___x_3781_);
                        crate::leanh::lean_dec(v_fst_3779_);
                        crate::leanh::lean_del_object(v___x_3775_);
                        crate::leanh::lean_dec(v_fst_3772_);
                        crate::leanh::lean_del_object(v___x_3770_);
                        crate::leanh::lean_dec(v_fst_3768_);
                        crate::leanh::lean_dec_ref(v_H_3754_);
                        crate::leanh::lean_dec_ref(v___x_3753_);
                        crate::leanh::lean_dec_ref(v___x_3752_);
                        crate::leanh::lean_dec_ref(v___x_3751_);
                        crate::leanh::lean_dec_ref(v___x_3750_);
                        crate::leanh::lean_dec_ref(v___x_3749_);
                        crate::leanh::lean_dec_ref(v___x_3748_);
                        crate::leanh::lean_dec_ref(v___x_3744_);
                        v_a_3826_ = crate::leanh::lean_ctor_get(v___x_3789_, 0);
                        v_isSharedCheck_3833_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3789_)) as u8;
                        if v_isSharedCheck_3833_ == 0 {
                            v___x_3828_ = v___x_3789_;
                            v_isShared_3829_ = v_isSharedCheck_3833_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3826_);
                            crate::leanh::lean_dec(v___x_3789_);
                            v___x_3828_ = crate::leanh::lean_box(0);
                            v_isShared_3829_ = v_isSharedCheck_3833_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3781_);
                    crate::leanh::lean_dec(v_fst_3779_);
                    crate::leanh::lean_del_object(v___x_3775_);
                    crate::leanh::lean_dec(v_snd_3773_);
                    crate::leanh::lean_dec(v_fst_3772_);
                    crate::leanh::lean_del_object(v___x_3770_);
                    crate::leanh::lean_dec(v_fst_3768_);
                    crate::leanh::lean_dec_ref(v_x_3755_);
                    crate::leanh::lean_dec_ref(v_H_3754_);
                    crate::leanh::lean_dec_ref(v___x_3753_);
                    crate::leanh::lean_dec_ref(v___x_3752_);
                    crate::leanh::lean_dec_ref(v___x_3751_);
                    crate::leanh::lean_dec_ref(v___x_3750_);
                    crate::leanh::lean_dec_ref(v___x_3749_);
                    crate::leanh::lean_dec_ref(v___x_3748_);
                    crate::leanh::lean_dec_ref(v___x_3744_);
                    v_a_3834_ = crate::leanh::lean_ctor_get(v___x_3783_, 0);
                    v_isSharedCheck_3841_ = (!crate::leanh::lean_is_exclusive(v___x_3783_)) as u8;
                    if v_isSharedCheck_3841_ == 0 {
                        v___x_3836_ = v___x_3783_;
                        v_isShared_3837_ = v_isSharedCheck_3841_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3834_);
                        crate::leanh::lean_dec(v___x_3783_);
                        v___x_3836_ = crate::leanh::lean_box(0);
                        v_isShared_3837_ = v_isSharedCheck_3841_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_u_3794_ = crate::leanh::lean_ctor_get(v_fst_3772_, 0);
                v_00_u03c3s_3795_ = crate::leanh::lean_ctor_get(v_fst_3772_, 1);
                v_target_3796_ = crate::leanh::lean_ctor_get(v_fst_3772_, 3);
                v_isSharedCheck_3823_ = (!crate::leanh::lean_is_exclusive(v_fst_3772_)) as u8;
                if v_isSharedCheck_3823_ == 0 {
                    v_unused_3824_ = crate::leanh::lean_ctor_get(v_fst_3772_, 2);
                    crate::leanh::lean_dec(v_unused_3824_);
                    v___x_3798_ = v_fst_3772_;
                    v_isShared_3799_ = v_isSharedCheck_3823_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_3796_);
                    crate::leanh::lean_inc(v_00_u03c3s_3795_);
                    crate::leanh::lean_inc(v_u_3794_);
                    crate::leanh::lean_dec(v_fst_3772_);
                    v___x_3798_ = crate::leanh::lean_box(0);
                    v_isShared_3799_ = v_isSharedCheck_3823_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3800_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
                v___x_3801_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
                v___x_3802_ = l_Lean_Name_mkStr6(
                    v___x_3748_,
                    v___x_3749_,
                    v___x_3750_,
                    v___x_3800_,
                    v___x_3801_,
                    v___x_3751_,
                );
                v___x_3803_ = crate::leanh::lean_box(0);
                if v_isShared_3771_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3770_, 1);
                    crate::leanh::lean_ctor_set(v___x_3770_, 1, v___x_3803_);
                    crate::leanh::lean_ctor_set(v___x_3770_, 0, v_a_3784_);
                    v___x_3805_ = v___x_3770_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3822_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3803_);
                    v___x_3805_ = v_reuseFailAlloc_3822_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_n(v_u_3794_, 2);
                v___x_3806_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3806_, 0, v_u_3794_);
                crate::leanh::lean_ctor_set(v___x_3806_, 1, v___x_3805_);
                v___x_3807_ = l_Lean_mkConst(v___x_3802_, v___x_3806_);
                crate::leanh::lean_inc_ref(v_target_3796_);
                crate::leanh::lean_inc(v_fst_3779_);
                crate::leanh::lean_inc_ref(v___x_3752_);
                v___x_3808_ = l_Lean_mkApp6(
                    v___x_3807_,
                    v___x_3752_,
                    v___x_3744_,
                    v_fst_3779_,
                    v___x_3753_,
                    v_target_3796_,
                    v_a_3790_,
                );
                v___x_3809_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_3794_,
                    v___x_3752_,
                    v_fst_3779_,
                    v_H_3754_,
                );
                if v_isShared_3799_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3798_, 2, v___x_3809_);
                    v___x_3811_ = v___x_3798_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3821_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_u_3794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_00_u03c3s_3795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 2, v___x_3809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 3, v_target_3796_);
                    v___x_3811_ = v_reuseFailAlloc_3821_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3781_, 1, v___x_3808_);
                    crate::leanh::lean_ctor_set(v___x_3781_, 0, v___x_3811_);
                    v___x_3813_ = v___x_3781_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3808_);
                    v___x_3813_ = v_reuseFailAlloc_3820_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3776_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3775_, 1, v___x_3813_);
                    crate::leanh::lean_ctor_set(v___x_3775_, 0, v_fst_3768_);
                    v___x_3815_ = v___x_3775_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_fst_3768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3819_, 1, v___x_3813_);
                    v___x_3815_ = v_reuseFailAlloc_3819_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3793_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3792_, 0, v___x_3815_);
                    v___x_3817_ = v___x_3792_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
                    v___x_3817_ = v_reuseFailAlloc_3818_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3817_;
            }
            11 => {
                if v_isShared_3829_ == 0 {
                    v___x_3831_ = v___x_3828_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
                    v___x_3831_ = v_reuseFailAlloc_3832_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3831_;
            }
            13 => {
                if v_isShared_3837_ == 0 {
                    v___x_3839_ = v___x_3836_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
                    v___x_3839_ = v_reuseFailAlloc_3840_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3839_;
            }
            15 => {
                if v_isShared_3847_ == 0 {
                    v___x_3849_ = v___x_3846_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3850_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
                    v___x_3849_ = v_reuseFailAlloc_3850_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3849_;
            }
            17 => {
                if v_isShared_3857_ == 0 {
                    v___x_3859_ = v___x_3856_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3862_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_snd_3863_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_3864_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3865_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3866_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_3867_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3868_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3869_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_3870_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_3871_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_H_3872_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_x_3873_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3874_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3875_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3876_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3877_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3878_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_2315__boxed_3879_: u8 = 0;
    let mut v_res_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2315__boxed_3879_ = (crate::leanh::lean_unbox(v___x_3865_) as u8);
    v_res_3880_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(
        v___x_3862_,
        v_snd_3863_,
        v_k_3864_,
        v___x_2315__boxed_3879_,
        v___x_3866_,
        v___x_3867_,
        v___x_3868_,
        v___x_3869_,
        v___x_3870_,
        v___x_3871_,
        v_H_3872_,
        v_x_3873_,
        v___y_3874_,
        v___y_3875_,
        v___y_3876_,
        v___y_3877_,
    );
    crate::leanh::lean_dec(v___y_3877_);
    crate::leanh::lean_dec_ref(v___y_3876_);
    crate::leanh::lean_dec(v___y_3875_);
    crate::leanh::lean_dec_ref(v___y_3874_);
    return v_res_3880_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(
    mut v_k_3881_: *mut crate::leanh::LeanObject,
    mut v_b_3882_: *mut crate::leanh::LeanObject,
    mut v___y_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
    mut v___y_3885_: *mut crate::leanh::LeanObject,
    mut v___y_3886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3886_);
    crate::leanh::lean_inc_ref(v___y_3885_);
    crate::leanh::lean_inc(v___y_3884_);
    crate::leanh::lean_inc_ref(v___y_3883_);
    v___x_3888_ = crate::leanh::lean_apply_6(
        v_k_3881_,
        v_b_3882_,
        v___y_3883_,
        v___y_3884_,
        v___y_3885_,
        v___y_3886_,
        crate::leanh::lean_box(0),
    );
    return v___x_3888_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_3889_: *mut crate::leanh::LeanObject,
    mut v_b_3890_: *mut crate::leanh::LeanObject,
    mut v___y_3891_: *mut crate::leanh::LeanObject,
    mut v___y_3892_: *mut crate::leanh::LeanObject,
    mut v___y_3893_: *mut crate::leanh::LeanObject,
    mut v___y_3894_: *mut crate::leanh::LeanObject,
    mut v___y_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3896_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(v_k_3889_, v_b_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
    crate::leanh::lean_dec(v___y_3894_);
    crate::leanh::lean_dec_ref(v___y_3893_);
    crate::leanh::lean_dec(v___y_3892_);
    crate::leanh::lean_dec_ref(v___y_3891_);
    return v_res_3896_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(
    mut v_name_3897_: *mut crate::leanh::LeanObject,
    mut v_bi_3898_: u8,
    mut v_type_3899_: *mut crate::leanh::LeanObject,
    mut v_k_3900_: *mut crate::leanh::LeanObject,
    mut v_kind_3901_: u8,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
    mut v___y_3903_: *mut crate::leanh::LeanObject,
    mut v___y_3904_: *mut crate::leanh::LeanObject,
    mut v___y_3905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut v_a_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3907_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_3907_, 0, v_k_3900_);
                v___x_3908_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3897_,
                    v_bi_3898_,
                    v_type_3899_,
                    v___f_3907_,
                    v_kind_3901_,
                    v___y_3902_,
                    v___y_3903_,
                    v___y_3904_,
                    v___y_3905_,
                );
                if crate::leanh::lean_obj_tag(v___x_3908_) == 0 {
                    v_a_3909_ = crate::leanh::lean_ctor_get(v___x_3908_, 0);
                    v_isSharedCheck_3916_ = (!crate::leanh::lean_is_exclusive(v___x_3908_)) as u8;
                    if v_isSharedCheck_3916_ == 0 {
                        v___x_3911_ = v___x_3908_;
                        v_isShared_3912_ = v_isSharedCheck_3916_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3909_);
                        crate::leanh::lean_dec(v___x_3908_);
                        v___x_3911_ = crate::leanh::lean_box(0);
                        v_isShared_3912_ = v_isSharedCheck_3916_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3917_ = crate::leanh::lean_ctor_get(v___x_3908_, 0);
                    v_isSharedCheck_3924_ = (!crate::leanh::lean_is_exclusive(v___x_3908_)) as u8;
                    if v_isSharedCheck_3924_ == 0 {
                        v___x_3919_ = v___x_3908_;
                        v_isShared_3920_ = v_isSharedCheck_3924_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3917_);
                        crate::leanh::lean_dec(v___x_3908_);
                        v___x_3919_ = crate::leanh::lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3924_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3912_ == 0 {
                    v___x_3914_ = v___x_3911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
                    v___x_3914_ = v_reuseFailAlloc_3915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3914_;
            }
            3 => {
                if v_isShared_3920_ == 0 {
                    v___x_3922_ = v___x_3919_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
                    v___x_3922_ = v_reuseFailAlloc_3923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___boxed(
    mut v_name_3925_: *mut crate::leanh::LeanObject,
    mut v_bi_3926_: *mut crate::leanh::LeanObject,
    mut v_type_3927_: *mut crate::leanh::LeanObject,
    mut v_k_3928_: *mut crate::leanh::LeanObject,
    mut v_kind_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
    mut v___y_3932_: *mut crate::leanh::LeanObject,
    mut v___y_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3935_: u8 = 0;
    let mut v_kind_boxed_3936_: u8 = 0;
    let mut v_res_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3935_ = (crate::leanh::lean_unbox(v_bi_3926_) as u8);
    v_kind_boxed_3936_ = (crate::leanh::lean_unbox(v_kind_3929_) as u8);
    v_res_3937_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_3925_, v_bi_boxed_3935_, v_type_3927_, v_k_3928_, v_kind_boxed_3936_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
    crate::leanh::lean_dec(v___y_3933_);
    crate::leanh::lean_dec_ref(v___y_3932_);
    crate::leanh::lean_dec(v___y_3931_);
    crate::leanh::lean_dec_ref(v___y_3930_);
    return v_res_3937_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(
    mut v_name_3938_: *mut crate::leanh::LeanObject,
    mut v_type_3939_: *mut crate::leanh::LeanObject,
    mut v_k_3940_: *mut crate::leanh::LeanObject,
    mut v___y_3941_: *mut crate::leanh::LeanObject,
    mut v___y_3942_: *mut crate::leanh::LeanObject,
    mut v___y_3943_: *mut crate::leanh::LeanObject,
    mut v___y_3944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3946_: u8 = 0;
    let mut v___x_3947_: u8 = 0;
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3946_ = 0;
    v___x_3947_ = 0;
    v___x_3948_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_3938_, v___x_3946_, v_type_3939_, v_k_3940_, v___x_3947_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
    return v___x_3948_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg___boxed(
    mut v_name_3949_: *mut crate::leanh::LeanObject,
    mut v_type_3950_: *mut crate::leanh::LeanObject,
    mut v_k_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_3949_, v_type_3950_, v_k_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    crate::leanh::lean_dec(v___y_3955_);
    crate::leanh::lean_dec_ref(v___y_3954_);
    crate::leanh::lean_dec(v___y_3953_);
    crate::leanh::lean_dec_ref(v___y_3952_);
    return v_res_3957_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3965_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2;
    v___x_3966_ = l_Lean_stringToMessageData(v___x_3965_);
    return v___x_3966_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(
    mut v_H_3967_: *mut crate::leanh::LeanObject,
    mut v_name_3968_: *mut crate::leanh::LeanObject,
    mut v_k_3969_: *mut crate::leanh::LeanObject,
    mut v_a_3970_: *mut crate::leanh::LeanObject,
    mut v_a_3971_: *mut crate::leanh::LeanObject,
    mut v_a_3972_: *mut crate::leanh::LeanObject,
    mut v_a_3973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: u8 = 0;
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4002_: u8 = 0;
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3975_ = l_Lean_Expr_consumeMData(v_H_3967_);
                v___x_3976_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0;
                v___x_3977_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
                v___x_3978_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1;
                v___x_3979_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0;
                v___x_3980_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1;
                v___x_3981_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3982_ = l_Lean_Expr_isAppOfArity(v___x_3975_, v___x_3980_, v___x_3981_);
                if v___x_3982_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3975_);
                    crate::leanh::lean_dec_ref(v_k_3969_);
                    crate::leanh::lean_dec(v_name_3968_);
                    v___x_3983_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3,
                    );
                    v___x_3984_ = l_Lean_MessageData_ofExpr(v_H_3967_);
                    v___x_3985_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3985_, 0, v___x_3983_);
                    crate::leanh::lean_ctor_set(v___x_3985_, 1, v___x_3984_);
                    v___x_3986_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_3985_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
                    return v___x_3986_;
                } else {
                    v___x_3987_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
                        v_name_3968_,
                        v_a_3972_,
                        v_a_3973_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3987_) == 0 {
                        v_a_3988_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                        crate::leanh::lean_inc(v_a_3988_);
                        crate::leanh::lean_dec_ref_known(v___x_3987_, 1);
                        v_fst_3989_ = crate::leanh::lean_ctor_get(v_a_3988_, 0);
                        crate::leanh::lean_inc(v_fst_3989_);
                        v_snd_3990_ = crate::leanh::lean_ctor_get(v_a_3988_, 1);
                        crate::leanh::lean_inc(v_snd_3990_);
                        crate::leanh::lean_dec(v_a_3988_);
                        v___x_3991_ = l_Lean_Expr_appFn_x21(v___x_3975_);
                        v___x_3992_ = l_Lean_Expr_appFn_x21(v___x_3991_);
                        v___x_3993_ = l_Lean_Expr_appArg_x21(v___x_3992_);
                        crate::leanh::lean_dec_ref(v___x_3992_);
                        v___x_3994_ = l_Lean_Expr_appArg_x21(v___x_3991_);
                        crate::leanh::lean_dec_ref(v___x_3991_);
                        v___x_3995_ = l_Lean_Expr_appArg_x21(v___x_3975_);
                        crate::leanh::lean_dec_ref(v___x_3975_);
                        v___x_3996_ = crate::leanh::lean_box((v___x_3982_) as usize);
                        crate::leanh::lean_inc_ref(v___x_3993_);
                        v___f_3997_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            17,
                            11,
                        );
                        crate::leanh::lean_closure_set(v___f_3997_, 0, v___x_3993_);
                        crate::leanh::lean_closure_set(v___f_3997_, 1, v_snd_3990_);
                        crate::leanh::lean_closure_set(v___f_3997_, 2, v_k_3969_);
                        crate::leanh::lean_closure_set(v___f_3997_, 3, v___x_3996_);
                        crate::leanh::lean_closure_set(v___f_3997_, 4, v___x_3976_);
                        crate::leanh::lean_closure_set(v___f_3997_, 5, v___x_3977_);
                        crate::leanh::lean_closure_set(v___f_3997_, 6, v___x_3978_);
                        crate::leanh::lean_closure_set(v___f_3997_, 7, v___x_3979_);
                        crate::leanh::lean_closure_set(v___f_3997_, 8, v___x_3994_);
                        crate::leanh::lean_closure_set(v___f_3997_, 9, v___x_3995_);
                        crate::leanh::lean_closure_set(v___f_3997_, 10, v_H_3967_);
                        v___x_3998_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_3989_, v___x_3993_, v___f_3997_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
                        return v___x_3998_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3975_);
                        crate::leanh::lean_dec_ref(v_k_3969_);
                        crate::leanh::lean_dec_ref(v_H_3967_);
                        v_a_3999_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                        v_isSharedCheck_4006_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3987_)) as u8;
                        if v_isSharedCheck_4006_ == 0 {
                            v___x_4001_ = v___x_3987_;
                            v_isShared_4002_ = v_isSharedCheck_4006_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3999_);
                            crate::leanh::lean_dec(v___x_3987_);
                            v___x_4001_ = crate::leanh::lean_box(0);
                            v_isShared_4002_ = v_isSharedCheck_4006_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4002_ == 0 {
                    v___x_4004_ = v___x_4001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4005_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
                    v___x_4004_ = v_reuseFailAlloc_4005_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___boxed(
    mut v_H_4007_: *mut crate::leanh::LeanObject,
    mut v_name_4008_: *mut crate::leanh::LeanObject,
    mut v_k_4009_: *mut crate::leanh::LeanObject,
    mut v_a_4010_: *mut crate::leanh::LeanObject,
    mut v_a_4011_: *mut crate::leanh::LeanObject,
    mut v_a_4012_: *mut crate::leanh::LeanObject,
    mut v_a_4013_: *mut crate::leanh::LeanObject,
    mut v_a_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(
        v_H_4007_,
        v_name_4008_,
        v_k_4009_,
        v_a_4010_,
        v_a_4011_,
        v_a_4012_,
        v_a_4013_,
    );
    crate::leanh::lean_dec(v_a_4013_);
    crate::leanh::lean_dec_ref(v_a_4012_);
    crate::leanh::lean_dec(v_a_4011_);
    crate::leanh::lean_dec_ref(v_a_4010_);
    return v_res_4015_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(
    mut v_00_u03b1_4016_: *mut crate::leanh::LeanObject,
    mut v_H_4017_: *mut crate::leanh::LeanObject,
    mut v_name_4018_: *mut crate::leanh::LeanObject,
    mut v_k_4019_: *mut crate::leanh::LeanObject,
    mut v_a_4020_: *mut crate::leanh::LeanObject,
    mut v_a_4021_: *mut crate::leanh::LeanObject,
    mut v_a_4022_: *mut crate::leanh::LeanObject,
    mut v_a_4023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4025_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(
        v_H_4017_,
        v_name_4018_,
        v_k_4019_,
        v_a_4020_,
        v_a_4021_,
        v_a_4022_,
        v_a_4023_,
    );
    return v___x_4025_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___boxed(
    mut v_00_u03b1_4026_: *mut crate::leanh::LeanObject,
    mut v_H_4027_: *mut crate::leanh::LeanObject,
    mut v_name_4028_: *mut crate::leanh::LeanObject,
    mut v_k_4029_: *mut crate::leanh::LeanObject,
    mut v_a_4030_: *mut crate::leanh::LeanObject,
    mut v_a_4031_: *mut crate::leanh::LeanObject,
    mut v_a_4032_: *mut crate::leanh::LeanObject,
    mut v_a_4033_: *mut crate::leanh::LeanObject,
    mut v_a_4034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4035_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(
        v_00_u03b1_4026_,
        v_H_4027_,
        v_name_4028_,
        v_k_4029_,
        v_a_4030_,
        v_a_4031_,
        v_a_4032_,
        v_a_4033_,
    );
    crate::leanh::lean_dec(v_a_4033_);
    crate::leanh::lean_dec_ref(v_a_4032_);
    crate::leanh::lean_dec(v_a_4031_);
    crate::leanh::lean_dec_ref(v_a_4030_);
    return v_res_4035_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(
    mut v_00_u03b1_4036_: *mut crate::leanh::LeanObject,
    mut v_name_4037_: *mut crate::leanh::LeanObject,
    mut v_bi_4038_: u8,
    mut v_type_4039_: *mut crate::leanh::LeanObject,
    mut v_k_4040_: *mut crate::leanh::LeanObject,
    mut v_kind_4041_: u8,
    mut v___y_4042_: *mut crate::leanh::LeanObject,
    mut v___y_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4047_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_4037_, v_bi_4038_, v_type_4039_, v_k_4040_, v_kind_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
    return v___x_4047_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___boxed(
    mut v_00_u03b1_4048_: *mut crate::leanh::LeanObject,
    mut v_name_4049_: *mut crate::leanh::LeanObject,
    mut v_bi_4050_: *mut crate::leanh::LeanObject,
    mut v_type_4051_: *mut crate::leanh::LeanObject,
    mut v_k_4052_: *mut crate::leanh::LeanObject,
    mut v_kind_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
    mut v___y_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4059_: u8 = 0;
    let mut v_kind_boxed_4060_: u8 = 0;
    let mut v_res_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4059_ = (crate::leanh::lean_unbox(v_bi_4050_) as u8);
    v_kind_boxed_4060_ = (crate::leanh::lean_unbox(v_kind_4053_) as u8);
    v_res_4061_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(v_00_u03b1_4048_, v_name_4049_, v_bi_boxed_4059_, v_type_4051_, v_k_4052_, v_kind_boxed_4060_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
    crate::leanh::lean_dec(v___y_4057_);
    crate::leanh::lean_dec_ref(v___y_4056_);
    crate::leanh::lean_dec(v___y_4055_);
    crate::leanh::lean_dec_ref(v___y_4054_);
    return v_res_4061_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(
    mut v_00_u03b1_4062_: *mut crate::leanh::LeanObject,
    mut v_name_4063_: *mut crate::leanh::LeanObject,
    mut v_type_4064_: *mut crate::leanh::LeanObject,
    mut v_k_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
    mut v___y_4067_: *mut crate::leanh::LeanObject,
    mut v___y_4068_: *mut crate::leanh::LeanObject,
    mut v___y_4069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4071_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_4063_, v_type_4064_, v_k_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
    return v___x_4071_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___boxed(
    mut v_00_u03b1_4072_: *mut crate::leanh::LeanObject,
    mut v_name_4073_: *mut crate::leanh::LeanObject,
    mut v_type_4074_: *mut crate::leanh::LeanObject,
    mut v_k_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
    mut v___y_4080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4081_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(
            v_00_u03b1_4072_,
            v_name_4073_,
            v_type_4074_,
            v_k_4075_,
            v___y_4076_,
            v___y_4077_,
            v___y_4078_,
            v___y_4079_,
        );
    crate::leanh::lean_dec(v___y_4079_);
    crate::leanh::lean_dec_ref(v___y_4078_);
    crate::leanh::lean_dec(v___y_4077_);
    crate::leanh::lean_dec_ref(v___y_4076_);
    return v_res_4081_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4082_ = crate::leanh::lean_box(0);
    v___x_4083_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4084_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4084_, 0, v___x_4083_);
    crate::leanh::lean_ctor_set(v___x_4084_, 1, v___x_4082_);
    return v___x_4084_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4086_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
    v___x_4087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4087_, 0, v___x_4086_);
    return v___x_4087_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___boxed(
    mut v___y_4088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4089_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
    return v_res_4089_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(
    mut v_00_u03b1_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4096_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
    return v___x_4096_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___boxed(
    mut v_00_u03b1_4097_: *mut crate::leanh::LeanObject,
    mut v___y_4098_: *mut crate::leanh::LeanObject,
    mut v___y_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(v_00_u03b1_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
    crate::leanh::lean_dec(v___y_4101_);
    crate::leanh::lean_dec_ref(v___y_4100_);
    crate::leanh::lean_dec(v___y_4099_);
    crate::leanh::lean_dec_ref(v___y_4098_);
    return v_res_4103_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(
    mut v___y_4104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v_r_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4136_: u8 = 0;
    let mut v_unused_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4106_ = lean_st_ref_get(v___y_4104_);
                v_ngen_4107_ = crate::leanh::lean_ctor_get(v___x_4106_, 2);
                crate::leanh::lean_inc_ref(v_ngen_4107_);
                crate::leanh::lean_dec(v___x_4106_);
                v_namePrefix_4108_ = crate::leanh::lean_ctor_get(v_ngen_4107_, 0);
                v_idx_4109_ = crate::leanh::lean_ctor_get(v_ngen_4107_, 1);
                v_isSharedCheck_4138_ = (!crate::leanh::lean_is_exclusive(v_ngen_4107_)) as u8;
                if v_isSharedCheck_4138_ == 0 {
                    v___x_4111_ = v_ngen_4107_;
                    v_isShared_4112_ = v_isSharedCheck_4138_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_4109_);
                    crate::leanh::lean_inc(v_namePrefix_4108_);
                    crate::leanh::lean_dec(v_ngen_4107_);
                    v___x_4111_ = crate::leanh::lean_box(0);
                    v_isShared_4112_ = v_isSharedCheck_4138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4113_ = lean_st_ref_take(v___y_4104_);
                v_env_4114_ = crate::leanh::lean_ctor_get(v___x_4113_, 0);
                v_nextMacroScope_4115_ = crate::leanh::lean_ctor_get(v___x_4113_, 1);
                v_auxDeclNGen_4116_ = crate::leanh::lean_ctor_get(v___x_4113_, 3);
                v_traceState_4117_ = crate::leanh::lean_ctor_get(v___x_4113_, 4);
                v_cache_4118_ = crate::leanh::lean_ctor_get(v___x_4113_, 5);
                v_messages_4119_ = crate::leanh::lean_ctor_get(v___x_4113_, 6);
                v_infoState_4120_ = crate::leanh::lean_ctor_get(v___x_4113_, 7);
                v_snapshotTasks_4121_ = crate::leanh::lean_ctor_get(v___x_4113_, 8);
                v_isSharedCheck_4136_ = (!crate::leanh::lean_is_exclusive(v___x_4113_)) as u8;
                if v_isSharedCheck_4136_ == 0 {
                    v_unused_4137_ = crate::leanh::lean_ctor_get(v___x_4113_, 2);
                    crate::leanh::lean_dec(v_unused_4137_);
                    v___x_4123_ = v___x_4113_;
                    v_isShared_4124_ = v_isSharedCheck_4136_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4121_);
                    crate::leanh::lean_inc(v_infoState_4120_);
                    crate::leanh::lean_inc(v_messages_4119_);
                    crate::leanh::lean_inc(v_cache_4118_);
                    crate::leanh::lean_inc(v_traceState_4117_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4116_);
                    crate::leanh::lean_inc(v_nextMacroScope_4115_);
                    crate::leanh::lean_inc(v_env_4114_);
                    crate::leanh::lean_dec(v___x_4113_);
                    v___x_4123_ = crate::leanh::lean_box(0);
                    v_isShared_4124_ = v_isSharedCheck_4136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_4109_);
                crate::leanh::lean_inc(v_namePrefix_4108_);
                v_r_4125_ = l_Lean_Name_num___override(v_namePrefix_4108_, v_idx_4109_);
                v___x_4126_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4127_ = lean_nat_add(v_idx_4109_, v___x_4126_);
                crate::leanh::lean_dec(v_idx_4109_);
                if v_isShared_4112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4111_, 1, v___x_4127_);
                    v___x_4129_ = v___x_4111_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_namePrefix_4108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4135_, 1, v___x_4127_);
                    v___x_4129_ = v_reuseFailAlloc_4135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4124_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4123_, 2, v___x_4129_);
                    v___x_4131_ = v___x_4123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4134_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_env_4114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_nextMacroScope_4115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 2, v___x_4129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 3, v_auxDeclNGen_4116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 4, v_traceState_4117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 5, v_cache_4118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 6, v_messages_4119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 7, v_infoState_4120_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 8, v_snapshotTasks_4121_);
                    v___x_4131_ = v_reuseFailAlloc_4134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4132_ = lean_st_ref_set(v___y_4104_, v___x_4131_);
                v___x_4133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4133_, 0, v_r_4125_);
                return v___x_4133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(
    mut v___y_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4141_ =
        l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(
            v___y_4139_,
        );
    crate::leanh::lean_dec(v___y_4139_);
    return v_res_4141_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4147_ =
        l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(
            v___y_4145_,
        );
    return v___x_4147_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4153_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(
        v___y_4148_,
        v___y_4149_,
        v___y_4150_,
        v___y_4151_,
    );
    crate::leanh::lean_dec(v___y_4151_);
    crate::leanh::lean_dec_ref(v___y_4150_);
    crate::leanh::lean_dec(v___y_4149_);
    crate::leanh::lean_dec_ref(v___y_4148_);
    return v_res_4153_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(
    mut v_u_4162_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4163_: *mut crate::leanh::LeanObject,
    mut v_H_u2081_x27_4164_: *mut crate::leanh::LeanObject,
    mut v_k_4165_: *mut crate::leanh::LeanObject,
    mut v_H_u2082_x27_4166_: *mut crate::leanh::LeanObject,
    mut v___y_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4184_: u8 = 0;
    let mut v_fst_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4194_: u8 = 0;
    let mut v_fst_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4198_: u8 = 0;
    let mut v_u_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_unused_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4231_: u8 = 0;
    let mut v_unused_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_a_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4237_: u8 = 0;
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v_isSharedCheck_4242_: u8 = 0;
    let mut v_isSharedCheck_4243_: u8 = 0;
    let mut v_a_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_isSharedCheck_4252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_H_u2082_x27_4166_);
                crate::leanh::lean_inc_ref(v_H_u2081_x27_4164_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_4163_);
                crate::leanh::lean_inc(v_u_4162_);
                v___x_4172_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_u_4162_,
                    v_00_u03c3s_4163_,
                    v_H_u2081_x27_4164_,
                    v_H_u2082_x27_4166_,
                );
                v_fst_4173_ = crate::leanh::lean_ctor_get(v___x_4172_, 0);
                v_snd_4174_ = crate::leanh::lean_ctor_get(v___x_4172_, 1);
                v_isSharedCheck_4252_ = (!crate::leanh::lean_is_exclusive(v___x_4172_)) as u8;
                if v_isSharedCheck_4252_ == 0 {
                    v___x_4176_ = v___x_4172_;
                    v_isShared_4177_ = v_isSharedCheck_4252_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4174_);
                    crate::leanh::lean_inc(v_fst_4173_);
                    crate::leanh::lean_dec(v___x_4172_);
                    v___x_4176_ = crate::leanh::lean_box(0);
                    v_isShared_4177_ = v_isSharedCheck_4252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_4170_);
                crate::leanh::lean_inc_ref(v___y_4169_);
                crate::leanh::lean_inc(v___y_4168_);
                crate::leanh::lean_inc_ref(v___y_4167_);
                crate::leanh::lean_inc(v_fst_4173_);
                v___x_4178_ = crate::leanh::lean_apply_6(
                    v_k_4165_,
                    v_fst_4173_,
                    v___y_4167_,
                    v___y_4168_,
                    v___y_4169_,
                    v___y_4170_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4178_) == 0 {
                    v_a_4179_ = crate::leanh::lean_ctor_get(v___x_4178_, 0);
                    crate::leanh::lean_inc(v_a_4179_);
                    crate::leanh::lean_dec_ref_known(v___x_4178_, 1);
                    v_snd_4180_ = crate::leanh::lean_ctor_get(v_a_4179_, 1);
                    v_fst_4181_ = crate::leanh::lean_ctor_get(v_a_4179_, 0);
                    v_isSharedCheck_4243_ = (!crate::leanh::lean_is_exclusive(v_a_4179_)) as u8;
                    if v_isSharedCheck_4243_ == 0 {
                        v___x_4183_ = v_a_4179_;
                        v_isShared_4184_ = v_isSharedCheck_4243_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4180_);
                        crate::leanh::lean_inc(v_fst_4181_);
                        crate::leanh::lean_dec(v_a_4179_);
                        v___x_4183_ = crate::leanh::lean_box(0);
                        v_isShared_4184_ = v_isSharedCheck_4243_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4176_);
                    crate::leanh::lean_dec(v_snd_4174_);
                    crate::leanh::lean_dec(v_fst_4173_);
                    crate::leanh::lean_dec_ref(v_H_u2082_x27_4166_);
                    crate::leanh::lean_dec_ref(v_H_u2081_x27_4164_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4163_);
                    crate::leanh::lean_dec(v_u_4162_);
                    v_a_4244_ = crate::leanh::lean_ctor_get(v___x_4178_, 0);
                    v_isSharedCheck_4251_ = (!crate::leanh::lean_is_exclusive(v___x_4178_)) as u8;
                    if v_isSharedCheck_4251_ == 0 {
                        v___x_4246_ = v___x_4178_;
                        v_isShared_4247_ = v_isSharedCheck_4251_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4244_);
                        crate::leanh::lean_dec(v___x_4178_);
                        v___x_4246_ = crate::leanh::lean_box(0);
                        v_isShared_4247_ = v_isSharedCheck_4251_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_4185_ = crate::leanh::lean_ctor_get(v_snd_4180_, 0);
                v_snd_4186_ = crate::leanh::lean_ctor_get(v_snd_4180_, 1);
                v_isSharedCheck_4242_ = (!crate::leanh::lean_is_exclusive(v_snd_4180_)) as u8;
                if v_isSharedCheck_4242_ == 0 {
                    v___x_4188_ = v_snd_4180_;
                    v_isShared_4189_ = v_isSharedCheck_4242_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4186_);
                    crate::leanh::lean_inc(v_fst_4185_);
                    crate::leanh::lean_dec(v_snd_4180_);
                    v___x_4188_ = crate::leanh::lean_box(0);
                    v_isShared_4189_ = v_isSharedCheck_4242_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_fst_4185_);
                v___x_4190_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_4185_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
                if crate::leanh::lean_obj_tag(v___x_4190_) == 0 {
                    v_a_4191_ = crate::leanh::lean_ctor_get(v___x_4190_, 0);
                    v_isSharedCheck_4233_ = (!crate::leanh::lean_is_exclusive(v___x_4190_)) as u8;
                    if v_isSharedCheck_4233_ == 0 {
                        v___x_4193_ = v___x_4190_;
                        v_isShared_4194_ = v_isSharedCheck_4233_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4191_);
                        crate::leanh::lean_dec(v___x_4190_);
                        v___x_4193_ = crate::leanh::lean_box(0);
                        v_isShared_4194_ = v_isSharedCheck_4233_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4188_);
                    crate::leanh::lean_dec(v_snd_4186_);
                    crate::leanh::lean_dec(v_fst_4185_);
                    crate::leanh::lean_del_object(v___x_4183_);
                    crate::leanh::lean_dec(v_fst_4181_);
                    crate::leanh::lean_del_object(v___x_4176_);
                    crate::leanh::lean_dec(v_snd_4174_);
                    crate::leanh::lean_dec(v_fst_4173_);
                    crate::leanh::lean_dec_ref(v_H_u2082_x27_4166_);
                    crate::leanh::lean_dec_ref(v_H_u2081_x27_4164_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4163_);
                    crate::leanh::lean_dec(v_u_4162_);
                    v_a_4234_ = crate::leanh::lean_ctor_get(v___x_4190_, 0);
                    v_isSharedCheck_4241_ = (!crate::leanh::lean_is_exclusive(v___x_4190_)) as u8;
                    if v_isSharedCheck_4241_ == 0 {
                        v___x_4236_ = v___x_4190_;
                        v_isShared_4237_ = v_isSharedCheck_4241_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4234_);
                        crate::leanh::lean_dec(v___x_4190_);
                        v___x_4236_ = crate::leanh::lean_box(0);
                        v_isShared_4237_ = v_isSharedCheck_4241_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_4195_ = crate::leanh::lean_ctor_get(v_a_4191_, 0);
                v_isSharedCheck_4231_ = (!crate::leanh::lean_is_exclusive(v_a_4191_)) as u8;
                if v_isSharedCheck_4231_ == 0 {
                    v_unused_4232_ = crate::leanh::lean_ctor_get(v_a_4191_, 1);
                    crate::leanh::lean_dec(v_unused_4232_);
                    v___x_4197_ = v_a_4191_;
                    v_isShared_4198_ = v_isSharedCheck_4231_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4195_);
                    crate::leanh::lean_dec(v_a_4191_);
                    v___x_4197_ = crate::leanh::lean_box(0);
                    v_isShared_4198_ = v_isSharedCheck_4231_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_u_4199_ = crate::leanh::lean_ctor_get(v_fst_4185_, 0);
                v_00_u03c3s_4200_ = crate::leanh::lean_ctor_get(v_fst_4185_, 1);
                v_target_4201_ = crate::leanh::lean_ctor_get(v_fst_4185_, 3);
                v_isSharedCheck_4229_ = (!crate::leanh::lean_is_exclusive(v_fst_4185_)) as u8;
                if v_isSharedCheck_4229_ == 0 {
                    v_unused_4230_ = crate::leanh::lean_ctor_get(v_fst_4185_, 2);
                    crate::leanh::lean_dec(v_unused_4230_);
                    v___x_4203_ = v_fst_4185_;
                    v_isShared_4204_ = v_isSharedCheck_4229_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_4201_);
                    crate::leanh::lean_inc(v_00_u03c3s_4200_);
                    crate::leanh::lean_inc(v_u_4199_);
                    crate::leanh::lean_dec(v_fst_4185_);
                    v___x_4203_ = crate::leanh::lean_box(0);
                    v_isShared_4204_ = v_isSharedCheck_4229_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4205_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1;
                v___x_4206_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_4162_);
                if v_isShared_4177_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4176_, 1);
                    crate::leanh::lean_ctor_set(v___x_4176_, 1, v___x_4206_);
                    crate::leanh::lean_ctor_set(v___x_4176_, 0, v_u_4162_);
                    v___x_4208_ = v___x_4176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_u_4162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 1, v___x_4206_);
                    v___x_4208_ = v_reuseFailAlloc_4228_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4209_ = l_Lean_mkConst(v___x_4205_, v___x_4208_);
                crate::leanh::lean_inc_ref(v_target_4201_);
                crate::leanh::lean_inc_ref(v_H_u2082_x27_4166_);
                crate::leanh::lean_inc_ref(v_H_u2081_x27_4164_);
                crate::leanh::lean_inc_n(v_fst_4195_, 2);
                crate::leanh::lean_inc_ref_n(v_00_u03c3s_4163_, 2);
                v___x_4210_ = l_Lean_mkApp8(
                    v___x_4209_,
                    v_00_u03c3s_4163_,
                    v_fst_4195_,
                    v_H_u2081_x27_4164_,
                    v_H_u2082_x27_4166_,
                    v_fst_4173_,
                    v_target_4201_,
                    v_snd_4174_,
                    v_snd_4186_,
                );
                crate::leanh::lean_inc(v_u_4162_);
                v___x_4211_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_4162_,
                    v_00_u03c3s_4163_,
                    v_fst_4195_,
                    v_H_u2081_x27_4164_,
                );
                v___x_4212_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_4162_,
                    v_00_u03c3s_4163_,
                    v___x_4211_,
                    v_H_u2082_x27_4166_,
                );
                if v_isShared_4204_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4203_, 2, v___x_4212_);
                    v___x_4214_ = v___x_4203_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4227_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_u_4199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_00_u03c3s_4200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 2, v___x_4212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 3, v_target_4201_);
                    v___x_4214_ = v_reuseFailAlloc_4227_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4197_, 1, v_fst_4195_);
                    crate::leanh::lean_ctor_set(v___x_4197_, 0, v_fst_4181_);
                    v___x_4216_ = v___x_4197_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_fst_4181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_fst_4195_);
                    v___x_4216_ = v_reuseFailAlloc_4226_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4188_, 1, v___x_4210_);
                    crate::leanh::lean_ctor_set(v___x_4188_, 0, v___x_4214_);
                    v___x_4218_ = v___x_4188_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 1, v___x_4210_);
                    v___x_4218_ = v_reuseFailAlloc_4225_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4183_, 1, v___x_4218_);
                    crate::leanh::lean_ctor_set(v___x_4183_, 0, v___x_4216_);
                    v___x_4220_ = v___x_4183_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 1, v___x_4218_);
                    v___x_4220_ = v_reuseFailAlloc_4224_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4194_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4193_, 0, v___x_4220_);
                    v___x_4222_ = v___x_4193_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
                    v___x_4222_ = v_reuseFailAlloc_4223_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4222_;
            }
            13 => {
                if v_isShared_4237_ == 0 {
                    v___x_4239_ = v___x_4236_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4240_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
                    v___x_4239_ = v_reuseFailAlloc_4240_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4239_;
            }
            15 => {
                if v_isShared_4247_ == 0 {
                    v___x_4249_ = v___x_4246_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
                    v___x_4249_ = v_reuseFailAlloc_4250_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed(
    mut v_u_4253_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4254_: *mut crate::leanh::LeanObject,
    mut v_H_u2081_x27_4255_: *mut crate::leanh::LeanObject,
    mut v_k_4256_: *mut crate::leanh::LeanObject,
    mut v_H_u2082_x27_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
    mut v___y_4259_: *mut crate::leanh::LeanObject,
    mut v___y_4260_: *mut crate::leanh::LeanObject,
    mut v___y_4261_: *mut crate::leanh::LeanObject,
    mut v___y_4262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4263_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(
        v_u_4253_,
        v_00_u03c3s_4254_,
        v_H_u2081_x27_4255_,
        v_k_4256_,
        v_H_u2082_x27_4257_,
        v___y_4258_,
        v___y_4259_,
        v___y_4260_,
        v___y_4261_,
    );
    crate::leanh::lean_dec(v___y_4261_);
    crate::leanh::lean_dec_ref(v___y_4260_);
    crate::leanh::lean_dec(v___y_4259_);
    crate::leanh::lean_dec_ref(v___y_4258_);
    return v_res_4263_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_snd_4267_: *mut crate::leanh::LeanObject,
    mut v_k_4268_: *mut crate::leanh::LeanObject,
    mut v___x_4269_: *mut crate::leanh::LeanObject,
    mut v___x_4270_: *mut crate::leanh::LeanObject,
    mut v___x_4271_: *mut crate::leanh::LeanObject,
    mut v___x_4272_: *mut crate::leanh::LeanObject,
    mut v___x_4273_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4274_: *mut crate::leanh::LeanObject,
    mut v_hyp_4275_: *mut crate::leanh::LeanObject,
    mut v_a_4276_: *mut crate::leanh::LeanObject,
    mut v_a_4277_: *mut crate::leanh::LeanObject,
    mut v_h_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
    mut v___y_4280_: *mut crate::leanh::LeanObject,
    mut v___y_4281_: *mut crate::leanh::LeanObject,
    mut v___y_4282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: u8 = 0;
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4294_: u8 = 0;
    let mut v_fst_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4299_: u8 = 0;
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: u8 = 0;
    let mut v___x_4304_: u8 = 0;
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4309_: u8 = 0;
    let mut v_u_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4335_: u8 = 0;
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut v_a_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4340_: u8 = 0;
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4344_: u8 = 0;
    let mut v_isSharedCheck_4345_: u8 = 0;
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
                v_lctx_4284_ = crate::leanh::lean_ctor_get(v___y_4279_, 2);
                crate::leanh::lean_inc_ref(v_a_4266_);
                v___x_4285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4285_, 0, v_a_4266_);
                v___x_4286_ = 0;
                crate::leanh::lean_inc_ref(v_h_4278_);
                crate::leanh::lean_inc_ref(v_lctx_4284_);
                v___x_4287_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(
                    v_snd_4267_,
                    v_lctx_4284_,
                    v_h_4278_,
                    v___x_4285_,
                    v___x_4286_,
                    v___y_4279_,
                    v___y_4280_,
                    v___y_4281_,
                    v___y_4282_,
                );
                if crate::leanh::lean_obj_tag(v___x_4287_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4287_, 1);
                    crate::leanh::lean_inc(v___y_4282_);
                    crate::leanh::lean_inc_ref(v___y_4281_);
                    crate::leanh::lean_inc(v___y_4280_);
                    crate::leanh::lean_inc_ref(v___y_4279_);
                    crate::leanh::lean_inc_ref(v_h_4278_);
                    crate::leanh::lean_inc_ref(v_a_4266_);
                    v___x_4288_ = crate::leanh::lean_apply_7(
                        v_k_4268_,
                        v_a_4266_,
                        v_h_4278_,
                        v___y_4279_,
                        v___y_4280_,
                        v___y_4281_,
                        v___y_4282_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4288_) == 0 {
                        v_a_4289_ = crate::leanh::lean_ctor_get(v___x_4288_, 0);
                        crate::leanh::lean_inc(v_a_4289_);
                        crate::leanh::lean_dec_ref_known(v___x_4288_, 1);
                        v_snd_4290_ = crate::leanh::lean_ctor_get(v_a_4289_, 1);
                        v_fst_4291_ = crate::leanh::lean_ctor_get(v_a_4289_, 0);
                        v_isSharedCheck_4346_ = (!crate::leanh::lean_is_exclusive(v_a_4289_)) as u8;
                        if v_isSharedCheck_4346_ == 0 {
                            v___x_4293_ = v_a_4289_;
                            v_isShared_4294_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_4290_);
                            crate::leanh::lean_inc(v_fst_4291_);
                            crate::leanh::lean_dec(v_a_4289_);
                            v___x_4293_ = crate::leanh::lean_box(0);
                            v_isShared_4294_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_h_4278_);
                        crate::leanh::lean_dec(v_a_4277_);
                        crate::leanh::lean_dec_ref(v_a_4276_);
                        crate::leanh::lean_dec_ref(v_hyp_4275_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4274_);
                        crate::leanh::lean_dec(v___x_4273_);
                        crate::leanh::lean_dec_ref(v___x_4272_);
                        crate::leanh::lean_dec_ref(v___x_4271_);
                        crate::leanh::lean_dec_ref(v___x_4270_);
                        crate::leanh::lean_dec_ref(v___x_4269_);
                        crate::leanh::lean_dec_ref(v_a_4266_);
                        return v___x_4288_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_4278_);
                    crate::leanh::lean_dec(v_a_4277_);
                    crate::leanh::lean_dec_ref(v_a_4276_);
                    crate::leanh::lean_dec_ref(v_hyp_4275_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4274_);
                    crate::leanh::lean_dec(v___x_4273_);
                    crate::leanh::lean_dec_ref(v___x_4272_);
                    crate::leanh::lean_dec_ref(v___x_4271_);
                    crate::leanh::lean_dec_ref(v___x_4270_);
                    crate::leanh::lean_dec_ref(v___x_4269_);
                    crate::leanh::lean_dec_ref(v_k_4268_);
                    crate::leanh::lean_dec_ref(v_a_4266_);
                    v_a_4347_ = crate::leanh::lean_ctor_get(v___x_4287_, 0);
                    v_isSharedCheck_4354_ = (!crate::leanh::lean_is_exclusive(v___x_4287_)) as u8;
                    if v_isSharedCheck_4354_ == 0 {
                        v___x_4349_ = v___x_4287_;
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4347_);
                        crate::leanh::lean_dec(v___x_4287_);
                        v___x_4349_ = crate::leanh::lean_box(0);
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4295_ = crate::leanh::lean_ctor_get(v_snd_4290_, 0);
                v_snd_4296_ = crate::leanh::lean_ctor_get(v_snd_4290_, 1);
                v_isSharedCheck_4345_ = (!crate::leanh::lean_is_exclusive(v_snd_4290_)) as u8;
                if v_isSharedCheck_4345_ == 0 {
                    v___x_4298_ = v_snd_4290_;
                    v_isShared_4299_ = v_isSharedCheck_4345_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4296_);
                    crate::leanh::lean_inc(v_fst_4295_);
                    crate::leanh::lean_dec(v_snd_4290_);
                    v___x_4298_ = crate::leanh::lean_box(0);
                    v_isShared_4299_ = v_isSharedCheck_4345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4300_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4301_ = lean_mk_empty_array_with_capacity(v___x_4300_);
                v___x_4302_ = lean_array_push(v___x_4301_, v_h_4278_);
                v___x_4303_ = 1;
                v___x_4304_ = 1;
                v___x_4305_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_4302_,
                    v_snd_4296_,
                    v___x_4286_,
                    v___x_4303_,
                    v___x_4286_,
                    v___x_4303_,
                    v___x_4304_,
                    v___y_4279_,
                    v___y_4280_,
                    v___y_4281_,
                    v___y_4282_,
                );
                crate::leanh::lean_dec_ref(v___x_4302_);
                if crate::leanh::lean_obj_tag(v___x_4305_) == 0 {
                    v_a_4306_ = crate::leanh::lean_ctor_get(v___x_4305_, 0);
                    v_isSharedCheck_4336_ = (!crate::leanh::lean_is_exclusive(v___x_4305_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v___x_4308_ = v___x_4305_;
                        v_isShared_4309_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4306_);
                        crate::leanh::lean_dec(v___x_4305_);
                        v___x_4308_ = crate::leanh::lean_box(0);
                        v_isShared_4309_ = v_isSharedCheck_4336_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4298_);
                    crate::leanh::lean_dec(v_fst_4295_);
                    crate::leanh::lean_del_object(v___x_4293_);
                    crate::leanh::lean_dec(v_fst_4291_);
                    crate::leanh::lean_dec(v_a_4277_);
                    crate::leanh::lean_dec_ref(v_a_4276_);
                    crate::leanh::lean_dec_ref(v_hyp_4275_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4274_);
                    crate::leanh::lean_dec(v___x_4273_);
                    crate::leanh::lean_dec_ref(v___x_4272_);
                    crate::leanh::lean_dec_ref(v___x_4271_);
                    crate::leanh::lean_dec_ref(v___x_4270_);
                    crate::leanh::lean_dec_ref(v___x_4269_);
                    crate::leanh::lean_dec_ref(v_a_4266_);
                    v_a_4337_ = crate::leanh::lean_ctor_get(v___x_4305_, 0);
                    v_isSharedCheck_4344_ = (!crate::leanh::lean_is_exclusive(v___x_4305_)) as u8;
                    if v_isSharedCheck_4344_ == 0 {
                        v___x_4339_ = v___x_4305_;
                        v_isShared_4340_ = v_isSharedCheck_4344_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4337_);
                        crate::leanh::lean_dec(v___x_4305_);
                        v___x_4339_ = crate::leanh::lean_box(0);
                        v_isShared_4340_ = v_isSharedCheck_4344_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v_u_4310_ = crate::leanh::lean_ctor_get(v_fst_4295_, 0);
                v_00_u03c3s_4311_ = crate::leanh::lean_ctor_get(v_fst_4295_, 1);
                v_hyps_4312_ = crate::leanh::lean_ctor_get(v_fst_4295_, 2);
                v_target_4313_ = crate::leanh::lean_ctor_get(v_fst_4295_, 3);
                v_isSharedCheck_4335_ = (!crate::leanh::lean_is_exclusive(v_fst_4295_)) as u8;
                if v_isSharedCheck_4335_ == 0 {
                    v___x_4315_ = v_fst_4295_;
                    v_isShared_4316_ = v_isSharedCheck_4335_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_4313_);
                    crate::leanh::lean_inc(v_hyps_4312_);
                    crate::leanh::lean_inc(v_00_u03c3s_4311_);
                    crate::leanh::lean_inc(v_u_4310_);
                    crate::leanh::lean_dec(v_fst_4295_);
                    v___x_4315_ = crate::leanh::lean_box(0);
                    v_isShared_4316_ = v_isSharedCheck_4335_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4317_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0;
                v___x_4318_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1;
                v___x_4319_ = l_Lean_Name_mkStr6(
                    v___x_4269_,
                    v___x_4270_,
                    v___x_4271_,
                    v___x_4272_,
                    v___x_4317_,
                    v___x_4318_,
                );
                v___x_4320_ = l_Lean_mkConst(v___x_4319_, v___x_4273_);
                crate::leanh::lean_inc_ref(v_target_4313_);
                crate::leanh::lean_inc_ref(v_hyp_4275_);
                crate::leanh::lean_inc_ref(v_hyps_4312_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_4274_);
                v_prf_4321_ = l_Lean_mkApp7(
                    v___x_4320_,
                    v_00_u03c3s_4274_,
                    v_hyps_4312_,
                    v_hyp_4275_,
                    v_target_4313_,
                    v_a_4266_,
                    v_a_4276_,
                    v_a_4306_,
                );
                v___x_4322_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_a_4277_,
                    v_00_u03c3s_4274_,
                    v_hyps_4312_,
                    v_hyp_4275_,
                );
                if v_isShared_4316_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4315_, 2, v___x_4322_);
                    v_goal_4324_ = v___x_4315_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4334_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_u_4310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_00_u03c3s_4311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 2, v___x_4322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 3, v_target_4313_);
                    v_goal_4324_ = v_reuseFailAlloc_4334_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4299_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4298_, 1, v_prf_4321_);
                    crate::leanh::lean_ctor_set(v___x_4298_, 0, v_goal_4324_);
                    v___x_4326_ = v___x_4298_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4333_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_goal_4324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4333_, 1, v_prf_4321_);
                    v___x_4326_ = v_reuseFailAlloc_4333_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4294_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4293_, 1, v___x_4326_);
                    v___x_4328_ = v___x_4293_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4332_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_fst_4291_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4332_, 1, v___x_4326_);
                    v___x_4328_ = v_reuseFailAlloc_4332_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4309_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4328_);
                    v___x_4330_ = v___x_4308_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4331_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
                    v___x_4330_ = v_reuseFailAlloc_4331_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4330_;
            }
            9 => {
                if v_isShared_4340_ == 0 {
                    v___x_4342_ = v___x_4339_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4343_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
                    v___x_4342_ = v_reuseFailAlloc_4343_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4342_;
            }
            11 => {
                if v_isShared_4350_ == 0 {
                    v___x_4352_ = v___x_4349_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
                    v___x_4352_ = v_reuseFailAlloc_4353_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4355_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_snd_4356_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_4357_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_4358_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_4359_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_4360_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_4361_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_4362_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_00_u03c3s_4363_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_hyp_4364_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_4365_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_4366_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_h_4367_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4368_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4369_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4370_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4371_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4372_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4373_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(v_a_4355_, v_snd_4356_, v_k_4357_, v___x_4358_, v___x_4359_, v___x_4360_, v___x_4361_, v___x_4362_, v_00_u03c3s_4363_, v_hyp_4364_, v_a_4365_, v_a_4366_, v_h_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
    crate::leanh::lean_dec(v___y_4371_);
    crate::leanh::lean_dec_ref(v___y_4370_);
    crate::leanh::lean_dec(v___y_4369_);
    crate::leanh::lean_dec_ref(v___y_4368_);
    return v_res_4373_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4374_ = crate::leanh::lean_box(0);
    v___x_4375_ = l_Lean_mkSort(v___x_4374_);
    return v___x_4375_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4376_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0);
    v___x_4377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4377_, 0, v___x_4376_);
    return v___x_4377_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(
    mut v_00_u03c3s_4385_: *mut crate::leanh::LeanObject,
    mut v_hyp_4386_: *mut crate::leanh::LeanObject,
    mut v_name_4387_: *mut crate::leanh::LeanObject,
    mut v_k_4388_: *mut crate::leanh::LeanObject,
    mut v___y_4389_: *mut crate::leanh::LeanObject,
    mut v___y_4390_: *mut crate::leanh::LeanObject,
    mut v___y_4391_: *mut crate::leanh::LeanObject,
    mut v___y_4392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v_a_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4430_: u8 = 0;
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4434_: u8 = 0;
    let mut v_a_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4438_: u8 = 0;
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4442_: u8 = 0;
    let mut v_a_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4394_ = l_Lean_Meta_mkFreshLevelMVar(
                    v___y_4389_,
                    v___y_4390_,
                    v___y_4391_,
                    v___y_4392_,
                );
                if crate::leanh::lean_obj_tag(v___x_4394_) == 0 {
                    v_a_4395_ = crate::leanh::lean_ctor_get(v___x_4394_, 0);
                    crate::leanh::lean_inc(v_a_4395_);
                    crate::leanh::lean_dec_ref_known(v___x_4394_, 1);
                    v___x_4396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
                    v___x_4397_ = 0;
                    v___x_4398_ = crate::leanh::lean_box(0);
                    v___x_4399_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_4396_,
                        v___x_4397_,
                        v___x_4398_,
                        v___y_4389_,
                        v___y_4390_,
                        v___y_4391_,
                        v___y_4392_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4399_) == 0 {
                        v_a_4400_ = crate::leanh::lean_ctor_get(v___x_4399_, 0);
                        crate::leanh::lean_inc_n(v_a_4400_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4399_, 1);
                        v___x_4401_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0;
                        v___x_4402_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
                        v___x_4403_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1;
                        v___x_4404_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_;
                        v___x_4405_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3;
                        v___x_4406_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_a_4395_);
                        v___x_4407_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4407_, 0, v_a_4395_);
                        crate::leanh::lean_ctor_set(v___x_4407_, 1, v___x_4406_);
                        crate::leanh::lean_inc_ref(v___x_4407_);
                        v___x_4408_ = l_Lean_mkConst(v___x_4405_, v___x_4407_);
                        crate::leanh::lean_inc_ref(v_hyp_4386_);
                        crate::leanh::lean_inc_ref(v_00_u03c3s_4385_);
                        v___x_4409_ =
                            l_Lean_mkApp3(v___x_4408_, v_00_u03c3s_4385_, v_hyp_4386_, v_a_4400_);
                        v___x_4410_ = crate::leanh::lean_box(0);
                        v___x_4411_ = l_Lean_Meta_synthInstance(
                            v___x_4409_,
                            v___x_4410_,
                            v___y_4389_,
                            v___y_4390_,
                            v___y_4391_,
                            v___y_4392_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4411_) == 0 {
                            v_a_4412_ = crate::leanh::lean_ctor_get(v___x_4411_, 0);
                            crate::leanh::lean_inc(v_a_4412_);
                            crate::leanh::lean_dec_ref_known(v___x_4411_, 1);
                            v___x_4413_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
                                v_name_4387_,
                                v___y_4391_,
                                v___y_4392_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4413_) == 0 {
                                v_a_4414_ = crate::leanh::lean_ctor_get(v___x_4413_, 0);
                                crate::leanh::lean_inc(v_a_4414_);
                                crate::leanh::lean_dec_ref_known(v___x_4413_, 1);
                                v_fst_4415_ = crate::leanh::lean_ctor_get(v_a_4414_, 0);
                                crate::leanh::lean_inc(v_fst_4415_);
                                v_snd_4416_ = crate::leanh::lean_ctor_get(v_a_4414_, 1);
                                crate::leanh::lean_inc(v_snd_4416_);
                                crate::leanh::lean_dec(v_a_4414_);
                                crate::leanh::lean_inc(v_a_4400_);
                                v___f_4417_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 18, 12);
                                crate::leanh::lean_closure_set(v___f_4417_, 0, v_a_4400_);
                                crate::leanh::lean_closure_set(v___f_4417_, 1, v_snd_4416_);
                                crate::leanh::lean_closure_set(v___f_4417_, 2, v_k_4388_);
                                crate::leanh::lean_closure_set(v___f_4417_, 3, v___x_4401_);
                                crate::leanh::lean_closure_set(v___f_4417_, 4, v___x_4402_);
                                crate::leanh::lean_closure_set(v___f_4417_, 5, v___x_4403_);
                                crate::leanh::lean_closure_set(v___f_4417_, 6, v___x_4404_);
                                crate::leanh::lean_closure_set(v___f_4417_, 7, v___x_4407_);
                                crate::leanh::lean_closure_set(v___f_4417_, 8, v_00_u03c3s_4385_);
                                crate::leanh::lean_closure_set(v___f_4417_, 9, v_hyp_4386_);
                                crate::leanh::lean_closure_set(v___f_4417_, 10, v_a_4412_);
                                crate::leanh::lean_closure_set(v___f_4417_, 11, v_a_4395_);
                                v___x_4418_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_4415_, v_a_4400_, v___f_4417_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
                                return v___x_4418_;
                            } else {
                                crate::leanh::lean_dec(v_a_4412_);
                                crate::leanh::lean_dec_ref_known(v___x_4407_, 2);
                                crate::leanh::lean_dec(v_a_4400_);
                                crate::leanh::lean_dec(v_a_4395_);
                                crate::leanh::lean_dec_ref(v_k_4388_);
                                crate::leanh::lean_dec_ref(v_hyp_4386_);
                                crate::leanh::lean_dec_ref(v_00_u03c3s_4385_);
                                v_a_4419_ = crate::leanh::lean_ctor_get(v___x_4413_, 0);
                                v_isSharedCheck_4426_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4413_)) as u8;
                                if v_isSharedCheck_4426_ == 0 {
                                    v___x_4421_ = v___x_4413_;
                                    v_isShared_4422_ = v_isSharedCheck_4426_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4419_);
                                    crate::leanh::lean_dec(v___x_4413_);
                                    v___x_4421_ = crate::leanh::lean_box(0);
                                    v_isShared_4422_ = v_isSharedCheck_4426_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4407_, 2);
                            crate::leanh::lean_dec(v_a_4400_);
                            crate::leanh::lean_dec(v_a_4395_);
                            crate::leanh::lean_dec_ref(v_k_4388_);
                            crate::leanh::lean_dec(v_name_4387_);
                            crate::leanh::lean_dec_ref(v_hyp_4386_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_4385_);
                            v_a_4427_ = crate::leanh::lean_ctor_get(v___x_4411_, 0);
                            v_isSharedCheck_4434_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4411_)) as u8;
                            if v_isSharedCheck_4434_ == 0 {
                                v___x_4429_ = v___x_4411_;
                                v_isShared_4430_ = v_isSharedCheck_4434_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4427_);
                                crate::leanh::lean_dec(v___x_4411_);
                                v___x_4429_ = crate::leanh::lean_box(0);
                                v_isShared_4430_ = v_isSharedCheck_4434_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4395_);
                        crate::leanh::lean_dec_ref(v_k_4388_);
                        crate::leanh::lean_dec(v_name_4387_);
                        crate::leanh::lean_dec_ref(v_hyp_4386_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4385_);
                        v_a_4435_ = crate::leanh::lean_ctor_get(v___x_4399_, 0);
                        v_isSharedCheck_4442_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4399_)) as u8;
                        if v_isSharedCheck_4442_ == 0 {
                            v___x_4437_ = v___x_4399_;
                            v_isShared_4438_ = v_isSharedCheck_4442_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4435_);
                            crate::leanh::lean_dec(v___x_4399_);
                            v___x_4437_ = crate::leanh::lean_box(0);
                            v_isShared_4438_ = v_isSharedCheck_4442_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_4388_);
                    crate::leanh::lean_dec(v_name_4387_);
                    crate::leanh::lean_dec_ref(v_hyp_4386_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4385_);
                    v_a_4443_ = crate::leanh::lean_ctor_get(v___x_4394_, 0);
                    v_isSharedCheck_4450_ = (!crate::leanh::lean_is_exclusive(v___x_4394_)) as u8;
                    if v_isSharedCheck_4450_ == 0 {
                        v___x_4445_ = v___x_4394_;
                        v_isShared_4446_ = v_isSharedCheck_4450_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4443_);
                        crate::leanh::lean_dec(v___x_4394_);
                        v___x_4445_ = crate::leanh::lean_box(0);
                        v_isShared_4446_ = v_isSharedCheck_4450_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4422_ == 0 {
                    v___x_4424_ = v___x_4421_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
                    v___x_4424_ = v_reuseFailAlloc_4425_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4424_;
            }
            3 => {
                if v_isShared_4430_ == 0 {
                    v___x_4432_ = v___x_4429_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
                    v___x_4432_ = v_reuseFailAlloc_4433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4432_;
            }
            5 => {
                if v_isShared_4438_ == 0 {
                    v___x_4440_ = v___x_4437_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4441_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
                    v___x_4440_ = v_reuseFailAlloc_4441_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4440_;
            }
            7 => {
                if v_isShared_4446_ == 0 {
                    v___x_4448_ = v___x_4445_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
                    v___x_4448_ = v_reuseFailAlloc_4449_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(
    mut v_00_u03c3s_4451_: *mut crate::leanh::LeanObject,
    mut v_hyp_4452_: *mut crate::leanh::LeanObject,
    mut v_name_4453_: *mut crate::leanh::LeanObject,
    mut v_k_4454_: *mut crate::leanh::LeanObject,
    mut v___y_4455_: *mut crate::leanh::LeanObject,
    mut v___y_4456_: *mut crate::leanh::LeanObject,
    mut v___y_4457_: *mut crate::leanh::LeanObject,
    mut v___y_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4460_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_4451_, v_hyp_4452_, v_name_4453_, v_k_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
    crate::leanh::lean_dec(v___y_4458_);
    crate::leanh::lean_dec_ref(v___y_4457_);
    crate::leanh::lean_dec(v___y_4456_);
    crate::leanh::lean_dec_ref(v___y_4455_);
    return v_res_4460_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(
    mut v_u_4469_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4470_: *mut crate::leanh::LeanObject,
    mut v_k_4471_: *mut crate::leanh::LeanObject,
    mut v_x_4472_: *mut crate::leanh::LeanObject,
    mut v___h_u03c6_4473_: *mut crate::leanh::LeanObject,
    mut v___y_4474_: *mut crate::leanh::LeanObject,
    mut v___y_4475_: *mut crate::leanh::LeanObject,
    mut v___y_4476_: *mut crate::leanh::LeanObject,
    mut v___y_4477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_H_x27_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4486_: u8 = 0;
    let mut v_fst_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v_fst_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v_u_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4526_: u8 = 0;
    let mut v_unused_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut v_unused_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_a_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_isSharedCheck_4539_: u8 = 0;
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_00_u03c3s_4470_);
                crate::leanh::lean_inc(v_u_4469_);
                v_H_x27_4479_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_4469_, v_00_u03c3s_4470_);
                crate::leanh::lean_inc(v___y_4477_);
                crate::leanh::lean_inc_ref(v___y_4476_);
                crate::leanh::lean_inc(v___y_4475_);
                crate::leanh::lean_inc_ref(v___y_4474_);
                v___x_4480_ = crate::leanh::lean_apply_6(
                    v_k_4471_,
                    v_H_x27_4479_,
                    v___y_4474_,
                    v___y_4475_,
                    v___y_4476_,
                    v___y_4477_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4480_) == 0 {
                    v_a_4481_ = crate::leanh::lean_ctor_get(v___x_4480_, 0);
                    crate::leanh::lean_inc(v_a_4481_);
                    crate::leanh::lean_dec_ref_known(v___x_4480_, 1);
                    v_snd_4482_ = crate::leanh::lean_ctor_get(v_a_4481_, 1);
                    v_fst_4483_ = crate::leanh::lean_ctor_get(v_a_4481_, 0);
                    v_isSharedCheck_4540_ = (!crate::leanh::lean_is_exclusive(v_a_4481_)) as u8;
                    if v_isSharedCheck_4540_ == 0 {
                        v___x_4485_ = v_a_4481_;
                        v_isShared_4486_ = v_isSharedCheck_4540_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4482_);
                        crate::leanh::lean_inc(v_fst_4483_);
                        crate::leanh::lean_dec(v_a_4481_);
                        v___x_4485_ = crate::leanh::lean_box(0);
                        v_isShared_4486_ = v_isSharedCheck_4540_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4470_);
                    crate::leanh::lean_dec(v_u_4469_);
                    return v___x_4480_;
                }
            }
            1 => {
                v_fst_4487_ = crate::leanh::lean_ctor_get(v_snd_4482_, 0);
                v_snd_4488_ = crate::leanh::lean_ctor_get(v_snd_4482_, 1);
                v_isSharedCheck_4539_ = (!crate::leanh::lean_is_exclusive(v_snd_4482_)) as u8;
                if v_isSharedCheck_4539_ == 0 {
                    v___x_4490_ = v_snd_4482_;
                    v_isShared_4491_ = v_isSharedCheck_4539_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4488_);
                    crate::leanh::lean_inc(v_fst_4487_);
                    crate::leanh::lean_dec(v_snd_4482_);
                    v___x_4490_ = crate::leanh::lean_box(0);
                    v_isShared_4491_ = v_isSharedCheck_4539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_fst_4487_);
                v___x_4492_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_4487_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
                if crate::leanh::lean_obj_tag(v___x_4492_) == 0 {
                    v_a_4493_ = crate::leanh::lean_ctor_get(v___x_4492_, 0);
                    v_isSharedCheck_4530_ = (!crate::leanh::lean_is_exclusive(v___x_4492_)) as u8;
                    if v_isSharedCheck_4530_ == 0 {
                        v___x_4495_ = v___x_4492_;
                        v_isShared_4496_ = v_isSharedCheck_4530_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4493_);
                        crate::leanh::lean_dec(v___x_4492_);
                        v___x_4495_ = crate::leanh::lean_box(0);
                        v_isShared_4496_ = v_isSharedCheck_4530_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4490_);
                    crate::leanh::lean_dec(v_snd_4488_);
                    crate::leanh::lean_dec(v_fst_4487_);
                    crate::leanh::lean_del_object(v___x_4485_);
                    crate::leanh::lean_dec(v_fst_4483_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4470_);
                    crate::leanh::lean_dec(v_u_4469_);
                    v_a_4531_ = crate::leanh::lean_ctor_get(v___x_4492_, 0);
                    v_isSharedCheck_4538_ = (!crate::leanh::lean_is_exclusive(v___x_4492_)) as u8;
                    if v_isSharedCheck_4538_ == 0 {
                        v___x_4533_ = v___x_4492_;
                        v_isShared_4534_ = v_isSharedCheck_4538_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4531_);
                        crate::leanh::lean_dec(v___x_4492_);
                        v___x_4533_ = crate::leanh::lean_box(0);
                        v_isShared_4534_ = v_isSharedCheck_4538_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_4497_ = crate::leanh::lean_ctor_get(v_a_4493_, 0);
                v_isSharedCheck_4528_ = (!crate::leanh::lean_is_exclusive(v_a_4493_)) as u8;
                if v_isSharedCheck_4528_ == 0 {
                    v_unused_4529_ = crate::leanh::lean_ctor_get(v_a_4493_, 1);
                    crate::leanh::lean_dec(v_unused_4529_);
                    v___x_4499_ = v_a_4493_;
                    v_isShared_4500_ = v_isSharedCheck_4528_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4497_);
                    crate::leanh::lean_dec(v_a_4493_);
                    v___x_4499_ = crate::leanh::lean_box(0);
                    v_isShared_4500_ = v_isSharedCheck_4528_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_u_4501_ = crate::leanh::lean_ctor_get(v_fst_4487_, 0);
                v_00_u03c3s_4502_ = crate::leanh::lean_ctor_get(v_fst_4487_, 1);
                v_target_4503_ = crate::leanh::lean_ctor_get(v_fst_4487_, 3);
                v_isSharedCheck_4526_ = (!crate::leanh::lean_is_exclusive(v_fst_4487_)) as u8;
                if v_isSharedCheck_4526_ == 0 {
                    v_unused_4527_ = crate::leanh::lean_ctor_get(v_fst_4487_, 2);
                    crate::leanh::lean_dec(v_unused_4527_);
                    v___x_4505_ = v_fst_4487_;
                    v_isShared_4506_ = v_isSharedCheck_4526_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_4503_);
                    crate::leanh::lean_inc(v_00_u03c3s_4502_);
                    crate::leanh::lean_inc(v_u_4501_);
                    crate::leanh::lean_dec(v_fst_4487_);
                    v___x_4505_ = crate::leanh::lean_box(0);
                    v_isShared_4506_ = v_isSharedCheck_4526_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4507_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1;
                v___x_4508_ = crate::leanh::lean_box(0);
                if v_isShared_4486_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4485_, 1);
                    crate::leanh::lean_ctor_set(v___x_4485_, 1, v___x_4508_);
                    crate::leanh::lean_ctor_set(v___x_4485_, 0, v_u_4469_);
                    v___x_4510_ = v___x_4485_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4525_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_u_4469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 1, v___x_4508_);
                    v___x_4510_ = v_reuseFailAlloc_4525_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4511_ = l_Lean_mkConst(v___x_4507_, v___x_4510_);
                crate::leanh::lean_inc_ref(v_target_4503_);
                crate::leanh::lean_inc(v_fst_4497_);
                v___x_4512_ = l_Lean_mkApp4(
                    v___x_4511_,
                    v_00_u03c3s_4470_,
                    v_fst_4497_,
                    v_target_4503_,
                    v_snd_4488_,
                );
                if v_isShared_4506_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4505_, 2, v_fst_4497_);
                    v___x_4514_ = v___x_4505_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4524_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_u_4501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4524_, 1, v_00_u03c3s_4502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4524_, 2, v_fst_4497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4524_, 3, v_target_4503_);
                    v___x_4514_ = v_reuseFailAlloc_4524_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4499_, 1, v___x_4512_);
                    crate::leanh::lean_ctor_set(v___x_4499_, 0, v___x_4514_);
                    v___x_4516_ = v___x_4499_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4523_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 1, v___x_4512_);
                    v___x_4516_ = v_reuseFailAlloc_4523_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4491_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4490_, 1, v___x_4516_);
                    crate::leanh::lean_ctor_set(v___x_4490_, 0, v_fst_4483_);
                    v___x_4518_ = v___x_4490_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4522_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_fst_4483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 1, v___x_4516_);
                    v___x_4518_ = v_reuseFailAlloc_4522_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4496_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4495_, 0, v___x_4518_);
                    v___x_4520_ = v___x_4495_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
                    v___x_4520_ = v_reuseFailAlloc_4521_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4520_;
            }
            11 => {
                if v_isShared_4534_ == 0 {
                    v___x_4536_ = v___x_4533_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
                    v___x_4536_ = v_reuseFailAlloc_4537_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(
    mut v_u_4541_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4542_: *mut crate::leanh::LeanObject,
    mut v_k_4543_: *mut crate::leanh::LeanObject,
    mut v_x_4544_: *mut crate::leanh::LeanObject,
    mut v___h_u03c6_4545_: *mut crate::leanh::LeanObject,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
    mut v___y_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4551_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(
        v_u_4541_,
        v_00_u03c3s_4542_,
        v_k_4543_,
        v_x_4544_,
        v___h_u03c6_4545_,
        v___y_4546_,
        v___y_4547_,
        v___y_4548_,
        v___y_4549_,
    );
    crate::leanh::lean_dec(v___y_4549_);
    crate::leanh::lean_dec_ref(v___y_4548_);
    crate::leanh::lean_dec(v___y_4547_);
    crate::leanh::lean_dec_ref(v___y_4546_);
    crate::leanh::lean_dec_ref(v___h_u03c6_4545_);
    crate::leanh::lean_dec_ref(v_x_4544_);
    return v_res_4551_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(
    mut v_u_4568_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4569_: *mut crate::leanh::LeanObject,
    mut v_k_4570_: *mut crate::leanh::LeanObject,
    mut v_tail_4571_: *mut crate::leanh::LeanObject,
    mut v_fst_4572_: *mut crate::leanh::LeanObject,
    mut v_H_u2081_x27_4573_: *mut crate::leanh::LeanObject,
    mut v___y_4574_: *mut crate::leanh::LeanObject,
    mut v___y_4575_: *mut crate::leanh::LeanObject,
    mut v___y_4576_: *mut crate::leanh::LeanObject,
    mut v___y_4577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4585_: u8 = 0;
    let mut v_fst_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4590_: u8 = 0;
    let mut v_fst_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4596_: u8 = 0;
    let mut v_u_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4622_: u8 = 0;
    let mut v_unused_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4624_: u8 = 0;
    let mut v_unused_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v_isSharedCheck_4627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_H_u2081_x27_4573_);
                crate::leanh::lean_inc_ref_n(v_00_u03c3s_4569_, 2);
                crate::leanh::lean_inc_n(v_u_4568_, 2);
                v___f_4579_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    10,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_4579_, 0, v_u_4568_);
                crate::leanh::lean_closure_set(v___f_4579_, 1, v_00_u03c3s_4569_);
                crate::leanh::lean_closure_set(v___f_4579_, 2, v_H_u2081_x27_4573_);
                crate::leanh::lean_closure_set(v___f_4579_, 3, v_k_4570_);
                v___x_4580_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4580_, 0, v_tail_4571_);
                crate::leanh::lean_inc_ref(v_fst_4572_);
                v___x_4581_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
                    v_u_4568_,
                    v_00_u03c3s_4569_,
                    v_fst_4572_,
                    v___x_4580_,
                    v___f_4579_,
                    v___y_4574_,
                    v___y_4575_,
                    v___y_4576_,
                    v___y_4577_,
                );
                if crate::leanh::lean_obj_tag(v___x_4581_) == 0 {
                    v_a_4582_ = crate::leanh::lean_ctor_get(v___x_4581_, 0);
                    v_isSharedCheck_4627_ = (!crate::leanh::lean_is_exclusive(v___x_4581_)) as u8;
                    if v_isSharedCheck_4627_ == 0 {
                        v___x_4584_ = v___x_4581_;
                        v_isShared_4585_ = v_isSharedCheck_4627_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4582_);
                        crate::leanh::lean_dec(v___x_4581_);
                        v___x_4584_ = crate::leanh::lean_box(0);
                        v_isShared_4585_ = v_isSharedCheck_4627_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_H_u2081_x27_4573_);
                    crate::leanh::lean_dec_ref(v_fst_4572_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4569_);
                    crate::leanh::lean_dec(v_u_4568_);
                    return v___x_4581_;
                }
            }
            1 => {
                v_fst_4586_ = crate::leanh::lean_ctor_get(v_a_4582_, 0);
                v_snd_4587_ = crate::leanh::lean_ctor_get(v_a_4582_, 1);
                v_isSharedCheck_4626_ = (!crate::leanh::lean_is_exclusive(v_a_4582_)) as u8;
                if v_isSharedCheck_4626_ == 0 {
                    v___x_4589_ = v_a_4582_;
                    v_isShared_4590_ = v_isSharedCheck_4626_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4587_);
                    crate::leanh::lean_inc(v_fst_4586_);
                    crate::leanh::lean_dec(v_a_4582_);
                    v___x_4589_ = crate::leanh::lean_box(0);
                    v_isShared_4590_ = v_isSharedCheck_4626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_4591_ = crate::leanh::lean_ctor_get(v_snd_4587_, 0);
                crate::leanh::lean_inc(v_fst_4591_);
                v_snd_4592_ = crate::leanh::lean_ctor_get(v_fst_4586_, 1);
                v_snd_4593_ = crate::leanh::lean_ctor_get(v_snd_4587_, 1);
                v_isSharedCheck_4624_ = (!crate::leanh::lean_is_exclusive(v_snd_4587_)) as u8;
                if v_isSharedCheck_4624_ == 0 {
                    v_unused_4625_ = crate::leanh::lean_ctor_get(v_snd_4587_, 0);
                    crate::leanh::lean_dec(v_unused_4625_);
                    v___x_4595_ = v_snd_4587_;
                    v_isShared_4596_ = v_isSharedCheck_4624_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4593_);
                    crate::leanh::lean_dec(v_snd_4587_);
                    v___x_4595_ = crate::leanh::lean_box(0);
                    v_isShared_4596_ = v_isSharedCheck_4624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_u_4597_ = crate::leanh::lean_ctor_get(v_fst_4591_, 0);
                v_00_u03c3s_4598_ = crate::leanh::lean_ctor_get(v_fst_4591_, 1);
                v_target_4599_ = crate::leanh::lean_ctor_get(v_fst_4591_, 3);
                v_isSharedCheck_4622_ = (!crate::leanh::lean_is_exclusive(v_fst_4591_)) as u8;
                if v_isSharedCheck_4622_ == 0 {
                    v_unused_4623_ = crate::leanh::lean_ctor_get(v_fst_4591_, 2);
                    crate::leanh::lean_dec(v_unused_4623_);
                    v___x_4601_ = v_fst_4591_;
                    v_isShared_4602_ = v_isSharedCheck_4622_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_4599_);
                    crate::leanh::lean_inc(v_00_u03c3s_4598_);
                    crate::leanh::lean_inc(v_u_4597_);
                    crate::leanh::lean_dec(v_fst_4591_);
                    v___x_4601_ = crate::leanh::lean_box(0);
                    v_isShared_4602_ = v_isSharedCheck_4622_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4603_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1;
                v___x_4604_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_u_4568_, 2);
                v___x_4605_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4605_, 0, v_u_4568_);
                crate::leanh::lean_ctor_set(v___x_4605_, 1, v___x_4604_);
                v___x_4606_ = l_Lean_mkConst(v___x_4603_, v___x_4605_);
                crate::leanh::lean_inc_ref(v_target_4599_);
                crate::leanh::lean_inc_ref(v_fst_4572_);
                crate::leanh::lean_inc_ref(v_H_u2081_x27_4573_);
                crate::leanh::lean_inc_n(v_snd_4592_, 2);
                crate::leanh::lean_inc_ref_n(v_00_u03c3s_4569_, 2);
                v___x_4607_ = l_Lean_mkApp6(
                    v___x_4606_,
                    v_00_u03c3s_4569_,
                    v_snd_4592_,
                    v_H_u2081_x27_4573_,
                    v_fst_4572_,
                    v_target_4599_,
                    v_snd_4593_,
                );
                v___x_4608_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_4568_,
                    v_00_u03c3s_4569_,
                    v_snd_4592_,
                    v_fst_4572_,
                );
                v___x_4609_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_4568_,
                    v_00_u03c3s_4569_,
                    v___x_4608_,
                    v_H_u2081_x27_4573_,
                );
                if v_isShared_4602_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4601_, 2, v___x_4609_);
                    v___x_4611_ = v___x_4601_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4621_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_u_4597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_00_u03c3s_4598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4621_, 2, v___x_4609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4621_, 3, v_target_4599_);
                    v___x_4611_ = v_reuseFailAlloc_4621_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4596_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4595_, 1, v___x_4607_);
                    crate::leanh::lean_ctor_set(v___x_4595_, 0, v___x_4611_);
                    v___x_4613_ = v___x_4595_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4620_, 1, v___x_4607_);
                    v___x_4613_ = v_reuseFailAlloc_4620_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4590_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4589_, 1, v___x_4613_);
                    v___x_4615_ = v___x_4589_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4619_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_fst_4586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 1, v___x_4613_);
                    v___x_4615_ = v_reuseFailAlloc_4619_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4585_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4584_, 0, v___x_4615_);
                    v___x_4617_ = v___x_4584_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
                    v___x_4617_ = v_reuseFailAlloc_4618_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(
    mut v_u_4628_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4629_: *mut crate::leanh::LeanObject,
    mut v_k_4630_: *mut crate::leanh::LeanObject,
    mut v_tail_4631_: *mut crate::leanh::LeanObject,
    mut v_fst_4632_: *mut crate::leanh::LeanObject,
    mut v_H_u2081_x27_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4639_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(
        v_u_4628_,
        v_00_u03c3s_4629_,
        v_k_4630_,
        v_tail_4631_,
        v_fst_4632_,
        v_H_u2081_x27_4633_,
        v___y_4634_,
        v___y_4635_,
        v___y_4636_,
        v___y_4637_,
    );
    crate::leanh::lean_dec(v___y_4637_);
    crate::leanh::lean_dec_ref(v___y_4636_);
    crate::leanh::lean_dec(v___y_4635_);
    crate::leanh::lean_dec_ref(v___y_4634_);
    return v_res_4639_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4649_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4;
    v___x_4650_ = l_Lean_stringToMessageData(v___x_4649_);
    return v___x_4650_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(
    mut v___x_4651_: *mut crate::leanh::LeanObject,
    mut v_tail_4652_: *mut crate::leanh::LeanObject,
    mut v_u_4653_: *mut crate::leanh::LeanObject,
    mut v___x_4654_: *mut crate::leanh::LeanObject,
    mut v_k_4655_: *mut crate::leanh::LeanObject,
    mut v_x_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(
        v___x_4651_,
        v_tail_4652_,
        v_u_4653_,
        v___x_4654_,
        v_k_4655_,
        v_x_4656_,
        v___y_4657_,
        v___y_4658_,
        v___y_4659_,
        v___y_4660_,
    );
    crate::leanh::lean_dec(v___y_4660_);
    crate::leanh::lean_dec_ref(v___y_4659_);
    crate::leanh::lean_dec(v___y_4658_);
    crate::leanh::lean_dec_ref(v___y_4657_);
    return v_res_4662_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4664_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6;
    v___x_4665_ = l_Lean_stringToMessageData(v___x_4664_);
    return v___x_4665_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4673_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10;
    v___x_4674_ = l_Lean_stringToMessageData(v___x_4673_);
    return v___x_4674_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
    mut v_u_4681_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_4682_: *mut crate::leanh::LeanObject,
    mut v_H_4683_: *mut crate::leanh::LeanObject,
    mut v_pat_4684_: *mut crate::leanh::LeanObject,
    mut v_k_4685_: *mut crate::leanh::LeanObject,
    mut v_a_4686_: *mut crate::leanh::LeanObject,
    mut v_a_4687_: *mut crate::leanh::LeanObject,
    mut v_a_4688_: *mut crate::leanh::LeanObject,
    mut v_a_4689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4694_: u8 = 0;
    let mut v___y_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4697_: u8 = 0;
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: u8 = 0;
    let mut v___x_4706_: u8 = 0;
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: u8 = 0;
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4729_: u8 = 0;
    let mut v_a_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v_isSharedCheck_4738_: u8 = 0;
    let mut v_H_x27_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4746_: u8 = 0;
    let mut v_fst_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4751_: u8 = 0;
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4756_: u8 = 0;
    let mut v_fst_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4760_: u8 = 0;
    let mut v_u_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4766_: u8 = 0;
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v_unused_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4789_: u8 = 0;
    let mut v_unused_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4791_: u8 = 0;
    let mut v_a_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4795_: u8 = 0;
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4799_: u8 = 0;
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut v_isSharedCheck_4801_: u8 = 0;
    let mut v_args_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4811_: u8 = 0;
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4824_: u8 = 0;
    let mut v_fst_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4832_: u8 = 0;
    let mut v_snd_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v_u_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4863_: u8 = 0;
    let mut v_unused_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4865_: u8 = 0;
    let mut v_unused_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4867_: u8 = 0;
    let mut v_isSharedCheck_4868_: u8 = 0;
    let mut v_a_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4876_: u8 = 0;
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: u8 = 0;
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4896_: u8 = 0;
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4900_: u8 = 0;
    let mut v_isSharedCheck_4901_: u8 = 0;
    let mut v_unused_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4906_: u8 = 0;
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4914_: u8 = 0;
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: u8 = 0;
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4947_: u8 = 0;
    let mut v_fst_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4951_: u8 = 0;
    let mut v_u_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4957_: u8 = 0;
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4980_: u8 = 0;
    let mut v_unused_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4982_: u8 = 0;
    let mut v_unused_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4984_: u8 = 0;
    let mut v_a_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4988_: u8 = 0;
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut v_isSharedCheck_4993_: u8 = 0;
    let mut v_unused_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4996_: u8 = 0;
    let mut v_unused_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4998_: u8 = 0;
    let mut v_h_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: u8 = 0;
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5018_: u8 = 0;
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5022_: u8 = 0;
    let mut v_a_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5026_: u8 = 0;
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5030_: u8 = 0;
    let mut v_a_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5034_: u8 = 0;
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_pat_4684_) {
                0 => {
                    v_name_4691_ = crate::leanh::lean_ctor_get(v_pat_4684_, 0);
                    v_isSharedCheck_4738_ = (!crate::leanh::lean_is_exclusive(v_pat_4684_)) as u8;
                    if v_isSharedCheck_4738_ == 0 {
                        v___x_4693_ = v_pat_4684_;
                        v_isShared_4694_ = v_isSharedCheck_4738_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_name_4691_);
                        crate::leanh::lean_dec(v_pat_4684_);
                        v___x_4693_ = crate::leanh::lean_box(0);
                        v_isShared_4694_ = v_isSharedCheck_4738_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_inc_ref(v_00_u03c3s_4682_);
                    crate::leanh::lean_inc(v_u_4681_);
                    v_H_x27_4739_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_4681_, v_00_u03c3s_4682_);
                    crate::leanh::lean_inc(v_a_4689_);
                    crate::leanh::lean_inc_ref(v_a_4688_);
                    crate::leanh::lean_inc(v_a_4687_);
                    crate::leanh::lean_inc_ref(v_a_4686_);
                    v___x_4740_ = crate::leanh::lean_apply_6(
                        v_k_4685_,
                        v_H_x27_4739_,
                        v_a_4686_,
                        v_a_4687_,
                        v_a_4688_,
                        v_a_4689_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4740_) == 0 {
                        v_a_4741_ = crate::leanh::lean_ctor_get(v___x_4740_, 0);
                        crate::leanh::lean_inc(v_a_4741_);
                        crate::leanh::lean_dec_ref_known(v___x_4740_, 1);
                        v_snd_4742_ = crate::leanh::lean_ctor_get(v_a_4741_, 1);
                        v_fst_4743_ = crate::leanh::lean_ctor_get(v_a_4741_, 0);
                        v_isSharedCheck_4801_ = (!crate::leanh::lean_is_exclusive(v_a_4741_)) as u8;
                        if v_isSharedCheck_4801_ == 0 {
                            v___x_4745_ = v_a_4741_;
                            v_isShared_4746_ = v_isSharedCheck_4801_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_4742_);
                            crate::leanh::lean_inc(v_fst_4743_);
                            crate::leanh::lean_dec(v_a_4741_);
                            v___x_4745_ = crate::leanh::lean_box(0);
                            v_isShared_4746_ = v_isSharedCheck_4801_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_H_4683_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                        crate::leanh::lean_dec(v_u_4681_);
                        return v___x_4740_;
                    }
                }
                2 => {
                    v_args_4802_ = crate::leanh::lean_ctor_get(v_pat_4684_, 0);
                    crate::leanh::lean_inc(v_args_4802_);
                    crate::leanh::lean_dec_ref_known(v_pat_4684_, 1);
                    if crate::leanh::lean_obj_tag(v_args_4802_) == 0 {
                        v___x_4803_ = crate::leanh::lean_box(1);
                        v_pat_4684_ = v___x_4803_;
                        state = 0;
                        continue;
                    } else {
                        v_tail_4805_ = crate::leanh::lean_ctor_get(v_args_4802_, 1);
                        if crate::leanh::lean_obj_tag(v_tail_4805_) == 0 {
                            v_head_4806_ = crate::leanh::lean_ctor_get(v_args_4802_, 0);
                            crate::leanh::lean_inc(v_head_4806_);
                            crate::leanh::lean_dec_ref_known(v_args_4802_, 2);
                            v_pat_4684_ = v_head_4806_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_4805_);
                            v_head_4808_ = crate::leanh::lean_ctor_get(v_args_4802_, 0);
                            v_isSharedCheck_4901_ =
                                (!crate::leanh::lean_is_exclusive(v_args_4802_)) as u8;
                            if v_isSharedCheck_4901_ == 0 {
                                v_unused_4902_ = crate::leanh::lean_ctor_get(v_args_4802_, 1);
                                crate::leanh::lean_dec(v_unused_4902_);
                                v___x_4810_ = v_args_4802_;
                                v_isShared_4811_ = v_isSharedCheck_4901_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_head_4808_);
                                crate::leanh::lean_dec(v_args_4802_);
                                v___x_4810_ = crate::leanh::lean_box(0);
                                v_isShared_4811_ = v_isSharedCheck_4901_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                }
                3 => {
                    v_args_4903_ = crate::leanh::lean_ctor_get(v_pat_4684_, 0);
                    v_isSharedCheck_4998_ = (!crate::leanh::lean_is_exclusive(v_pat_4684_)) as u8;
                    if v_isSharedCheck_4998_ == 0 {
                        v___x_4905_ = v_pat_4684_;
                        v_isShared_4906_ = v_isSharedCheck_4998_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_4903_);
                        crate::leanh::lean_dec(v_pat_4684_);
                        v___x_4905_ = crate::leanh::lean_box(0);
                        v_isShared_4906_ = v_isSharedCheck_4998_;
                        state = 35;
                        continue;
                    }
                }
                4 => {
                    v_h_4999_ = crate::leanh::lean_ctor_get(v_pat_4684_, 0);
                    crate::leanh::lean_inc(v_h_4999_);
                    crate::leanh::lean_dec_ref_known(v_pat_4684_, 1);
                    crate::leanh::lean_inc_ref(v_00_u03c3s_4682_);
                    v___f_5000_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed
                            as *mut core::ffi::c_void,
                        10,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_5000_, 0, v_u_4681_);
                    crate::leanh::lean_closure_set(v___f_5000_, 1, v_00_u03c3s_4682_);
                    crate::leanh::lean_closure_set(v___f_5000_, 2, v_k_4685_);
                    v___x_5001_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_4682_, v_H_4683_, v_h_4999_, v___f_5000_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                    return v___x_5001_;
                }
                _ => {
                    crate::leanh::lean_dec(v_u_4681_);
                    v_h_5002_ = crate::leanh::lean_ctor_get(v_pat_4684_, 0);
                    crate::leanh::lean_inc(v_h_5002_);
                    crate::leanh::lean_dec_ref_known(v_pat_4684_, 1);
                    v___x_5003_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
                        v_h_5002_, v_a_4688_, v_a_4689_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5003_) == 0 {
                        v_a_5004_ = crate::leanh::lean_ctor_get(v___x_5003_, 0);
                        crate::leanh::lean_inc(v_a_5004_);
                        crate::leanh::lean_dec_ref_known(v___x_5003_, 1);
                        v_fst_5005_ = crate::leanh::lean_ctor_get(v_a_5004_, 0);
                        crate::leanh::lean_inc(v_fst_5005_);
                        v_snd_5006_ = crate::leanh::lean_ctor_get(v_a_5004_, 1);
                        crate::leanh::lean_inc(v_snd_5006_);
                        crate::leanh::lean_dec(v_a_5004_);
                        v___x_5007_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v_a_4689_);
                        if crate::leanh::lean_obj_tag(v___x_5007_) == 0 {
                            v_a_5008_ = crate::leanh::lean_ctor_get(v___x_5007_, 0);
                            crate::leanh::lean_inc(v_a_5008_);
                            crate::leanh::lean_dec_ref_known(v___x_5007_, 1);
                            v___x_5009_ = l_Lean_Expr_consumeMData(v_H_4683_);
                            crate::leanh::lean_dec_ref(v_H_4683_);
                            v___x_5010_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5010_, 0, v_fst_5005_);
                            crate::leanh::lean_ctor_set(v___x_5010_, 1, v_a_5008_);
                            crate::leanh::lean_ctor_set(v___x_5010_, 2, v___x_5009_);
                            v___x_5011_ = 1;
                            crate::leanh::lean_inc_ref(v___x_5010_);
                            v___x_5012_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                                v_snd_5006_,
                                v_00_u03c3s_4682_,
                                v___x_5010_,
                                v___x_5011_,
                                v_a_4686_,
                                v_a_4687_,
                                v_a_4688_,
                                v_a_4689_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5012_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5012_, 1);
                                v___x_5013_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_5010_);
                                crate::leanh::lean_inc(v_a_4689_);
                                crate::leanh::lean_inc_ref(v_a_4688_);
                                crate::leanh::lean_inc(v_a_4687_);
                                crate::leanh::lean_inc_ref(v_a_4686_);
                                v___x_5014_ = crate::leanh::lean_apply_6(
                                    v_k_4685_,
                                    v___x_5013_,
                                    v_a_4686_,
                                    v_a_4687_,
                                    v_a_4688_,
                                    v_a_4689_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_5014_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_5010_, 3);
                                crate::leanh::lean_dec_ref(v_k_4685_);
                                v_a_5015_ = crate::leanh::lean_ctor_get(v___x_5012_, 0);
                                v_isSharedCheck_5022_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5012_)) as u8;
                                if v_isSharedCheck_5022_ == 0 {
                                    v___x_5017_ = v___x_5012_;
                                    v_isShared_5018_ = v_isSharedCheck_5022_;
                                    state = 49;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5015_);
                                    crate::leanh::lean_dec(v___x_5012_);
                                    v___x_5017_ = crate::leanh::lean_box(0);
                                    v_isShared_5018_ = v_isSharedCheck_5022_;
                                    state = 49;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_snd_5006_);
                            crate::leanh::lean_dec(v_fst_5005_);
                            crate::leanh::lean_dec_ref(v_k_4685_);
                            crate::leanh::lean_dec_ref(v_H_4683_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                            v_a_5023_ = crate::leanh::lean_ctor_get(v___x_5007_, 0);
                            v_isSharedCheck_5030_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5007_)) as u8;
                            if v_isSharedCheck_5030_ == 0 {
                                v___x_5025_ = v___x_5007_;
                                v_isShared_5026_ = v_isSharedCheck_5030_;
                                state = 51;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5023_);
                                crate::leanh::lean_dec(v___x_5007_);
                                v___x_5025_ = crate::leanh::lean_box(0);
                                v_isShared_5026_ = v_isSharedCheck_5030_;
                                state = 51;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_4685_);
                        crate::leanh::lean_dec_ref(v_H_4683_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                        v_a_5031_ = crate::leanh::lean_ctor_get(v___x_5003_, 0);
                        v_isSharedCheck_5038_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5003_)) as u8;
                        if v_isSharedCheck_5038_ == 0 {
                            v___x_5033_ = v___x_5003_;
                            v_isShared_5034_ = v_isSharedCheck_5038_;
                            state = 53;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5031_);
                            crate::leanh::lean_dec(v___x_5003_);
                            v___x_5033_ = crate::leanh::lean_box(0);
                            v_isShared_5034_ = v_isSharedCheck_5038_;
                            state = 53;
                            continue;
                        }
                    }
                }
            },
            1 => {
                v___x_4707_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
                v___x_4708_ = 0;
                v___x_4709_ = crate::leanh::lean_box(0);
                v___x_4710_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_4707_,
                    v___x_4708_,
                    v___x_4709_,
                    v_a_4686_,
                    v_a_4687_,
                    v_a_4688_,
                    v_a_4689_,
                );
                if crate::leanh::lean_obj_tag(v___x_4710_) == 0 {
                    v_a_4711_ = crate::leanh::lean_ctor_get(v___x_4710_, 0);
                    crate::leanh::lean_inc(v_a_4711_);
                    crate::leanh::lean_dec_ref_known(v___x_4710_, 1);
                    v___x_4712_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3;
                    v___x_4713_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_u_4681_);
                    v___x_4714_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4714_, 0, v_u_4681_);
                    crate::leanh::lean_ctor_set(v___x_4714_, 1, v___x_4713_);
                    v___x_4715_ = l_Lean_mkConst(v___x_4712_, v___x_4714_);
                    crate::leanh::lean_inc_ref(v_H_4683_);
                    crate::leanh::lean_inc_ref(v_00_u03c3s_4682_);
                    v___x_4716_ =
                        l_Lean_mkApp3(v___x_4715_, v_00_u03c3s_4682_, v_H_4683_, v_a_4711_);
                    v___x_4717_ = crate::leanh::lean_box(0);
                    v___x_4718_ = l_Lean_Meta_synthInstance(
                        v___x_4716_,
                        v___x_4717_,
                        v_a_4686_,
                        v_a_4687_,
                        v_a_4688_,
                        v_a_4689_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4718_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4718_, 1);
                        crate::leanh::lean_inc(v_name_4691_);
                        v___x_4719_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4719_, 0, v_name_4691_);
                        crate::leanh::lean_inc_ref(v_k_4685_);
                        crate::leanh::lean_inc_ref(v_H_4683_);
                        crate::leanh::lean_inc_ref(v_00_u03c3s_4682_);
                        crate::leanh::lean_inc(v_u_4681_);
                        v___x_4720_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
                            v_u_4681_,
                            v_00_u03c3s_4682_,
                            v_H_4683_,
                            v___x_4719_,
                            v_k_4685_,
                            v_a_4686_,
                            v_a_4687_,
                            v_a_4688_,
                            v_a_4689_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4720_) == 0 {
                            crate::leanh::lean_del_object(v___x_4693_);
                            crate::leanh::lean_dec(v_name_4691_);
                            crate::leanh::lean_dec_ref(v_k_4685_);
                            crate::leanh::lean_dec_ref(v_H_4683_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                            crate::leanh::lean_dec(v_u_4681_);
                            return v___x_4720_;
                        } else {
                            v_a_4721_ = crate::leanh::lean_ctor_get(v___x_4720_, 0);
                            crate::leanh::lean_inc(v_a_4721_);
                            v___y_4703_ = v___x_4720_;
                            v_a_4704_ = v_a_4721_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_4722_ = crate::leanh::lean_ctor_get(v___x_4718_, 0);
                        v_isSharedCheck_4729_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4718_)) as u8;
                        if v_isSharedCheck_4729_ == 0 {
                            v___x_4724_ = v___x_4718_;
                            v_isShared_4725_ = v_isSharedCheck_4729_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4722_);
                            crate::leanh::lean_dec(v___x_4718_);
                            v___x_4724_ = crate::leanh::lean_box(0);
                            v_isShared_4725_ = v_isSharedCheck_4729_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_4730_ = crate::leanh::lean_ctor_get(v___x_4710_, 0);
                    v_isSharedCheck_4737_ = (!crate::leanh::lean_is_exclusive(v___x_4710_)) as u8;
                    if v_isSharedCheck_4737_ == 0 {
                        v___x_4732_ = v___x_4710_;
                        v_isShared_4733_ = v_isSharedCheck_4737_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4730_);
                        crate::leanh::lean_dec(v___x_4710_);
                        v___x_4732_ = crate::leanh::lean_box(0);
                        v_isShared_4733_ = v_isSharedCheck_4737_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_4697_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4696_);
                    if v_isShared_4694_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4693_, 5);
                        v___x_4699_ = v___x_4693_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4701_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_name_4691_);
                        v___x_4699_ = v_reuseFailAlloc_4701_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4693_);
                    crate::leanh::lean_dec(v_name_4691_);
                    crate::leanh::lean_dec_ref(v_k_4685_);
                    crate::leanh::lean_dec_ref(v_H_4683_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                    crate::leanh::lean_dec(v_u_4681_);
                    return v___y_4696_;
                }
            }
            3 => {
                v_pat_4684_ = v___x_4699_;
                state = 0;
                continue;
            }
            4 => {
                v___x_4705_ = l_Lean_Exception_isInterrupt(v_a_4704_);
                if v___x_4705_ == 0 {
                    v___x_4706_ = l_Lean_Exception_isRuntime(v_a_4704_);
                    v___y_4696_ = v___y_4703_;
                    v___y_4697_ = v___x_4706_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_a_4704_);
                    v___y_4696_ = v___y_4703_;
                    v___y_4697_ = v___x_4705_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_4722_);
                if v_isShared_4725_ == 0 {
                    v___x_4727_ = v___x_4724_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4728_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
                    v___x_4727_ = v_reuseFailAlloc_4728_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_4703_ = v___x_4727_;
                v_a_4704_ = v_a_4722_;
                state = 4;
                continue;
            }
            7 => {
                crate::leanh::lean_inc(v_a_4730_);
                if v_isShared_4733_ == 0 {
                    v___x_4735_ = v___x_4732_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4736_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
                    v___x_4735_ = v_reuseFailAlloc_4736_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_4703_ = v___x_4735_;
                v_a_4704_ = v_a_4730_;
                state = 4;
                continue;
            }
            9 => {
                v_fst_4747_ = crate::leanh::lean_ctor_get(v_snd_4742_, 0);
                v_snd_4748_ = crate::leanh::lean_ctor_get(v_snd_4742_, 1);
                v_isSharedCheck_4800_ = (!crate::leanh::lean_is_exclusive(v_snd_4742_)) as u8;
                if v_isSharedCheck_4800_ == 0 {
                    v___x_4750_ = v_snd_4742_;
                    v_isShared_4751_ = v_isSharedCheck_4800_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4748_);
                    crate::leanh::lean_inc(v_fst_4747_);
                    crate::leanh::lean_dec(v_snd_4742_);
                    v___x_4750_ = crate::leanh::lean_box(0);
                    v_isShared_4751_ = v_isSharedCheck_4800_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_inc(v_fst_4747_);
                v___x_4752_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_4747_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                if crate::leanh::lean_obj_tag(v___x_4752_) == 0 {
                    v_a_4753_ = crate::leanh::lean_ctor_get(v___x_4752_, 0);
                    v_isSharedCheck_4791_ = (!crate::leanh::lean_is_exclusive(v___x_4752_)) as u8;
                    if v_isSharedCheck_4791_ == 0 {
                        v___x_4755_ = v___x_4752_;
                        v_isShared_4756_ = v_isSharedCheck_4791_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4753_);
                        crate::leanh::lean_dec(v___x_4752_);
                        v___x_4755_ = crate::leanh::lean_box(0);
                        v_isShared_4756_ = v_isSharedCheck_4791_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4750_);
                    crate::leanh::lean_dec(v_snd_4748_);
                    crate::leanh::lean_dec(v_fst_4747_);
                    crate::leanh::lean_del_object(v___x_4745_);
                    crate::leanh::lean_dec(v_fst_4743_);
                    crate::leanh::lean_dec_ref(v_H_4683_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                    crate::leanh::lean_dec(v_u_4681_);
                    v_a_4792_ = crate::leanh::lean_ctor_get(v___x_4752_, 0);
                    v_isSharedCheck_4799_ = (!crate::leanh::lean_is_exclusive(v___x_4752_)) as u8;
                    if v_isSharedCheck_4799_ == 0 {
                        v___x_4794_ = v___x_4752_;
                        v_isShared_4795_ = v_isSharedCheck_4799_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4792_);
                        crate::leanh::lean_dec(v___x_4752_);
                        v___x_4794_ = crate::leanh::lean_box(0);
                        v_isShared_4795_ = v_isSharedCheck_4799_;
                        state = 19;
                        continue;
                    }
                }
            }
            11 => {
                v_fst_4757_ = crate::leanh::lean_ctor_get(v_a_4753_, 0);
                v_isSharedCheck_4789_ = (!crate::leanh::lean_is_exclusive(v_a_4753_)) as u8;
                if v_isSharedCheck_4789_ == 0 {
                    v_unused_4790_ = crate::leanh::lean_ctor_get(v_a_4753_, 1);
                    crate::leanh::lean_dec(v_unused_4790_);
                    v___x_4759_ = v_a_4753_;
                    v_isShared_4760_ = v_isSharedCheck_4789_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4757_);
                    crate::leanh::lean_dec(v_a_4753_);
                    v___x_4759_ = crate::leanh::lean_box(0);
                    v_isShared_4760_ = v_isSharedCheck_4789_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_u_4761_ = crate::leanh::lean_ctor_get(v_fst_4747_, 0);
                v_00_u03c3s_4762_ = crate::leanh::lean_ctor_get(v_fst_4747_, 1);
                v_target_4763_ = crate::leanh::lean_ctor_get(v_fst_4747_, 3);
                v_isSharedCheck_4787_ = (!crate::leanh::lean_is_exclusive(v_fst_4747_)) as u8;
                if v_isSharedCheck_4787_ == 0 {
                    v_unused_4788_ = crate::leanh::lean_ctor_get(v_fst_4747_, 2);
                    crate::leanh::lean_dec(v_unused_4788_);
                    v___x_4765_ = v_fst_4747_;
                    v_isShared_4766_ = v_isSharedCheck_4787_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_4763_);
                    crate::leanh::lean_inc(v_00_u03c3s_4762_);
                    crate::leanh::lean_inc(v_u_4761_);
                    crate::leanh::lean_dec(v_fst_4747_);
                    v___x_4765_ = crate::leanh::lean_box(0);
                    v_isShared_4766_ = v_isSharedCheck_4787_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4767_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1;
                v___x_4768_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_4681_);
                if v_isShared_4746_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4745_, 1);
                    crate::leanh::lean_ctor_set(v___x_4745_, 1, v___x_4768_);
                    crate::leanh::lean_ctor_set(v___x_4745_, 0, v_u_4681_);
                    v___x_4770_ = v___x_4745_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_u_4681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 1, v___x_4768_);
                    v___x_4770_ = v_reuseFailAlloc_4786_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4771_ = l_Lean_mkConst(v___x_4767_, v___x_4770_);
                crate::leanh::lean_inc_ref(v_target_4763_);
                crate::leanh::lean_inc_ref(v_H_4683_);
                crate::leanh::lean_inc(v_fst_4757_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_4682_);
                v___x_4772_ = l_Lean_mkApp5(
                    v___x_4771_,
                    v_00_u03c3s_4682_,
                    v_fst_4757_,
                    v_H_4683_,
                    v_target_4763_,
                    v_snd_4748_,
                );
                v___x_4773_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_4681_,
                    v_00_u03c3s_4682_,
                    v_fst_4757_,
                    v_H_4683_,
                );
                if v_isShared_4766_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4765_, 2, v___x_4773_);
                    v___x_4775_ = v___x_4765_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4785_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_u_4761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_00_u03c3s_4762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 2, v___x_4773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_target_4763_);
                    v___x_4775_ = v_reuseFailAlloc_4785_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_4760_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4759_, 1, v___x_4772_);
                    crate::leanh::lean_ctor_set(v___x_4759_, 0, v___x_4775_);
                    v___x_4777_ = v___x_4759_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4784_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4784_, 1, v___x_4772_);
                    v___x_4777_ = v_reuseFailAlloc_4784_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_4751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4750_, 1, v___x_4777_);
                    crate::leanh::lean_ctor_set(v___x_4750_, 0, v_fst_4743_);
                    v___x_4779_ = v___x_4750_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4783_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_fst_4743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4783_, 1, v___x_4777_);
                    v___x_4779_ = v_reuseFailAlloc_4783_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_4756_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4755_, 0, v___x_4779_);
                    v___x_4781_ = v___x_4755_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4779_);
                    v___x_4781_ = v_reuseFailAlloc_4782_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4781_;
            }
            19 => {
                if v_isShared_4795_ == 0 {
                    v___x_4797_ = v___x_4794_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
                    v___x_4797_ = v_reuseFailAlloc_4798_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4797_;
            }
            21 => {
                crate::leanh::lean_inc_ref(v_H_4683_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_4682_);
                crate::leanh::lean_inc(v_u_4681_);
                v___x_4812_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(
                    v_u_4681_,
                    v_00_u03c3s_4682_,
                    v_H_4683_,
                    v_a_4686_,
                    v_a_4687_,
                    v_a_4688_,
                    v_a_4689_,
                );
                if crate::leanh::lean_obj_tag(v___x_4812_) == 0 {
                    v_a_4813_ = crate::leanh::lean_ctor_get(v___x_4812_, 0);
                    crate::leanh::lean_inc(v_a_4813_);
                    crate::leanh::lean_dec_ref_known(v___x_4812_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4813_) == 1 {
                        v_val_4814_ = crate::leanh::lean_ctor_get(v_a_4813_, 0);
                        crate::leanh::lean_inc(v_val_4814_);
                        crate::leanh::lean_dec_ref_known(v_a_4813_, 1);
                        v_snd_4815_ = crate::leanh::lean_ctor_get(v_val_4814_, 1);
                        crate::leanh::lean_inc(v_snd_4815_);
                        v_fst_4816_ = crate::leanh::lean_ctor_get(v_val_4814_, 0);
                        crate::leanh::lean_inc_n(v_fst_4816_, 2);
                        crate::leanh::lean_dec(v_val_4814_);
                        v_fst_4817_ = crate::leanh::lean_ctor_get(v_snd_4815_, 0);
                        crate::leanh::lean_inc_n(v_fst_4817_, 2);
                        v_snd_4818_ = crate::leanh::lean_ctor_get(v_snd_4815_, 1);
                        crate::leanh::lean_inc(v_snd_4818_);
                        crate::leanh::lean_dec(v_snd_4815_);
                        crate::leanh::lean_inc_ref_n(v_00_u03c3s_4682_, 2);
                        crate::leanh::lean_inc_n(v_u_4681_, 2);
                        v___f_4819_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            11,
                            5,
                        );
                        crate::leanh::lean_closure_set(v___f_4819_, 0, v_u_4681_);
                        crate::leanh::lean_closure_set(v___f_4819_, 1, v_00_u03c3s_4682_);
                        crate::leanh::lean_closure_set(v___f_4819_, 2, v_k_4685_);
                        crate::leanh::lean_closure_set(v___f_4819_, 3, v_tail_4805_);
                        crate::leanh::lean_closure_set(v___f_4819_, 4, v_fst_4817_);
                        v___x_4820_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
                            v_u_4681_,
                            v_00_u03c3s_4682_,
                            v_fst_4816_,
                            v_head_4808_,
                            v___f_4819_,
                            v_a_4686_,
                            v_a_4687_,
                            v_a_4688_,
                            v_a_4689_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4820_) == 0 {
                            v_a_4821_ = crate::leanh::lean_ctor_get(v___x_4820_, 0);
                            v_isSharedCheck_4868_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4820_)) as u8;
                            if v_isSharedCheck_4868_ == 0 {
                                v___x_4823_ = v___x_4820_;
                                v_isShared_4824_ = v_isSharedCheck_4868_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4821_);
                                crate::leanh::lean_dec(v___x_4820_);
                                v___x_4823_ = crate::leanh::lean_box(0);
                                v_isShared_4824_ = v_isSharedCheck_4868_;
                                state = 22;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_snd_4818_);
                            crate::leanh::lean_dec(v_fst_4817_);
                            crate::leanh::lean_dec(v_fst_4816_);
                            crate::leanh::lean_del_object(v___x_4810_);
                            crate::leanh::lean_dec_ref(v_H_4683_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                            crate::leanh::lean_dec(v_u_4681_);
                            v_a_4869_ = crate::leanh::lean_ctor_get(v___x_4820_, 0);
                            v_isSharedCheck_4876_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4820_)) as u8;
                            if v_isSharedCheck_4876_ == 0 {
                                v___x_4871_ = v___x_4820_;
                                v_isShared_4872_ = v_isSharedCheck_4876_;
                                state = 31;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4869_);
                                crate::leanh::lean_dec(v___x_4820_);
                                v___x_4871_ = crate::leanh::lean_box(0);
                                v_isShared_4872_ = v_isSharedCheck_4876_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4813_);
                        crate::leanh::lean_del_object(v___x_4810_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                        v___x_4877_ = l_Lean_Expr_consumeMData(v_H_4683_);
                        v___x_4878_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1;
                        v___x_4879_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_4880_ =
                            l_Lean_Expr_isAppOfArity(v___x_4877_, v___x_4878_, v___x_4879_);
                        if v___x_4880_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4877_);
                            crate::leanh::lean_dec(v_head_4808_);
                            crate::leanh::lean_dec(v_tail_4805_);
                            crate::leanh::lean_dec_ref(v_k_4685_);
                            crate::leanh::lean_dec(v_u_4681_);
                            v___x_4881_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5);
                            v___x_4882_ = l_Lean_MessageData_ofExpr(v_H_4683_);
                            v___x_4883_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4883_, 0, v___x_4881_);
                            crate::leanh::lean_ctor_set(v___x_4883_, 1, v___x_4882_);
                            v___x_4884_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_4883_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                            return v___x_4884_;
                        } else {
                            if crate::leanh::lean_obj_tag(v_head_4808_) == 0 {
                                v_name_4885_ = crate::leanh::lean_ctor_get(v_head_4808_, 0);
                                crate::leanh::lean_inc(v_name_4885_);
                                crate::leanh::lean_dec_ref_known(v_head_4808_, 1);
                                v___x_4886_ = l_Lean_Expr_appFn_x21(v___x_4877_);
                                v___x_4887_ = l_Lean_Expr_appArg_x21(v___x_4886_);
                                crate::leanh::lean_dec_ref(v___x_4886_);
                                v___x_4888_ = l_Lean_Expr_appArg_x21(v___x_4877_);
                                crate::leanh::lean_dec_ref(v___x_4877_);
                                v___f_4889_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed as *mut core::ffi::c_void, 11, 5);
                                crate::leanh::lean_closure_set(v___f_4889_, 0, v___x_4888_);
                                crate::leanh::lean_closure_set(v___f_4889_, 1, v_tail_4805_);
                                crate::leanh::lean_closure_set(v___f_4889_, 2, v_u_4681_);
                                crate::leanh::lean_closure_set(v___f_4889_, 3, v___x_4887_);
                                crate::leanh::lean_closure_set(v___f_4889_, 4, v_k_4685_);
                                v___x_4890_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(
                                    v_H_4683_,
                                    v_name_4885_,
                                    v___f_4889_,
                                    v_a_4686_,
                                    v_a_4687_,
                                    v_a_4688_,
                                    v_a_4689_,
                                );
                                return v___x_4890_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4877_);
                                crate::leanh::lean_dec(v_head_4808_);
                                crate::leanh::lean_dec(v_tail_4805_);
                                crate::leanh::lean_dec_ref(v_k_4685_);
                                crate::leanh::lean_dec_ref(v_H_4683_);
                                crate::leanh::lean_dec(v_u_4681_);
                                v___x_4891_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7);
                                v___x_4892_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_4891_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                                return v___x_4892_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4810_);
                    crate::leanh::lean_dec(v_head_4808_);
                    crate::leanh::lean_dec(v_tail_4805_);
                    crate::leanh::lean_dec_ref(v_k_4685_);
                    crate::leanh::lean_dec_ref(v_H_4683_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                    crate::leanh::lean_dec(v_u_4681_);
                    v_a_4893_ = crate::leanh::lean_ctor_get(v___x_4812_, 0);
                    v_isSharedCheck_4900_ = (!crate::leanh::lean_is_exclusive(v___x_4812_)) as u8;
                    if v_isSharedCheck_4900_ == 0 {
                        v___x_4895_ = v___x_4812_;
                        v_isShared_4896_ = v_isSharedCheck_4900_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4893_);
                        crate::leanh::lean_dec(v___x_4812_);
                        v___x_4895_ = crate::leanh::lean_box(0);
                        v_isShared_4896_ = v_isSharedCheck_4900_;
                        state = 33;
                        continue;
                    }
                }
            }
            22 => {
                v_fst_4825_ = crate::leanh::lean_ctor_get(v_a_4821_, 0);
                crate::leanh::lean_inc(v_fst_4825_);
                v_snd_4826_ = crate::leanh::lean_ctor_get(v_a_4821_, 1);
                crate::leanh::lean_inc(v_snd_4826_);
                crate::leanh::lean_dec(v_a_4821_);
                v_fst_4827_ = crate::leanh::lean_ctor_get(v_snd_4826_, 0);
                crate::leanh::lean_inc(v_fst_4827_);
                v_fst_4828_ = crate::leanh::lean_ctor_get(v_fst_4825_, 0);
                v_snd_4829_ = crate::leanh::lean_ctor_get(v_fst_4825_, 1);
                v_isSharedCheck_4867_ = (!crate::leanh::lean_is_exclusive(v_fst_4825_)) as u8;
                if v_isSharedCheck_4867_ == 0 {
                    v___x_4831_ = v_fst_4825_;
                    v_isShared_4832_ = v_isSharedCheck_4867_;
                    state = 23;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4829_);
                    crate::leanh::lean_inc(v_fst_4828_);
                    crate::leanh::lean_dec(v_fst_4825_);
                    v___x_4831_ = crate::leanh::lean_box(0);
                    v_isShared_4832_ = v_isSharedCheck_4867_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v_snd_4833_ = crate::leanh::lean_ctor_get(v_snd_4826_, 1);
                v_isSharedCheck_4865_ = (!crate::leanh::lean_is_exclusive(v_snd_4826_)) as u8;
                if v_isSharedCheck_4865_ == 0 {
                    v_unused_4866_ = crate::leanh::lean_ctor_get(v_snd_4826_, 0);
                    crate::leanh::lean_dec(v_unused_4866_);
                    v___x_4835_ = v_snd_4826_;
                    v_isShared_4836_ = v_isSharedCheck_4865_;
                    state = 24;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4833_);
                    crate::leanh::lean_dec(v_snd_4826_);
                    v___x_4835_ = crate::leanh::lean_box(0);
                    v_isShared_4836_ = v_isSharedCheck_4865_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_u_4837_ = crate::leanh::lean_ctor_get(v_fst_4827_, 0);
                v_00_u03c3s_4838_ = crate::leanh::lean_ctor_get(v_fst_4827_, 1);
                v_target_4839_ = crate::leanh::lean_ctor_get(v_fst_4827_, 3);
                v_isSharedCheck_4863_ = (!crate::leanh::lean_is_exclusive(v_fst_4827_)) as u8;
                if v_isSharedCheck_4863_ == 0 {
                    v_unused_4864_ = crate::leanh::lean_ctor_get(v_fst_4827_, 2);
                    crate::leanh::lean_dec(v_unused_4864_);
                    v___x_4841_ = v_fst_4827_;
                    v_isShared_4842_ = v_isSharedCheck_4863_;
                    state = 25;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_4839_);
                    crate::leanh::lean_inc(v_00_u03c3s_4838_);
                    crate::leanh::lean_inc(v_u_4837_);
                    crate::leanh::lean_dec(v_fst_4827_);
                    v___x_4841_ = crate::leanh::lean_box(0);
                    v_isShared_4842_ = v_isSharedCheck_4863_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_4843_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3;
                v___x_4844_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_4681_);
                if v_isShared_4811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4810_, 1, v___x_4844_);
                    crate::leanh::lean_ctor_set(v___x_4810_, 0, v_u_4681_);
                    v___x_4846_ = v___x_4810_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4862_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_u_4681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4862_, 1, v___x_4844_);
                    v___x_4846_ = v_reuseFailAlloc_4862_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4847_ = l_Lean_mkConst(v___x_4843_, v___x_4846_);
                crate::leanh::lean_inc_ref(v_target_4839_);
                crate::leanh::lean_inc_ref(v_H_4683_);
                crate::leanh::lean_inc(v_snd_4829_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_4682_);
                v___x_4848_ = l_Lean_mkApp8(
                    v___x_4847_,
                    v_00_u03c3s_4682_,
                    v_snd_4829_,
                    v_fst_4816_,
                    v_fst_4817_,
                    v_H_4683_,
                    v_target_4839_,
                    v_snd_4818_,
                    v_snd_4833_,
                );
                v___x_4849_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_4681_,
                    v_00_u03c3s_4682_,
                    v_snd_4829_,
                    v_H_4683_,
                );
                if v_isShared_4842_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4841_, 2, v___x_4849_);
                    v___x_4851_ = v___x_4841_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_u_4837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 1, v_00_u03c3s_4838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 2, v___x_4849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 3, v_target_4839_);
                    v___x_4851_ = v_reuseFailAlloc_4861_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_4836_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4835_, 1, v___x_4848_);
                    crate::leanh::lean_ctor_set(v___x_4835_, 0, v___x_4851_);
                    v___x_4853_ = v___x_4835_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4860_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4860_, 1, v___x_4848_);
                    v___x_4853_ = v_reuseFailAlloc_4860_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_4832_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4831_, 1, v___x_4853_);
                    v___x_4855_ = v___x_4831_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4859_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_fst_4828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4859_, 1, v___x_4853_);
                    v___x_4855_ = v_reuseFailAlloc_4859_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_4824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4823_, 0, v___x_4855_);
                    v___x_4857_ = v___x_4823_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4855_);
                    v___x_4857_ = v_reuseFailAlloc_4858_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4857_;
            }
            31 => {
                if v_isShared_4872_ == 0 {
                    v___x_4874_ = v___x_4871_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
                    v___x_4874_ = v_reuseFailAlloc_4875_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4874_;
            }
            33 => {
                if v_isShared_4896_ == 0 {
                    v___x_4898_ = v___x_4895_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4899_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
                    v___x_4898_ = v_reuseFailAlloc_4899_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4898_;
            }
            35 => {
                if crate::leanh::lean_obj_tag(v_args_4903_) == 0 {
                    crate::leanh::lean_del_object(v___x_4905_);
                    crate::leanh::lean_dec_ref(v_k_4685_);
                    crate::leanh::lean_dec_ref(v_H_4683_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                    crate::leanh::lean_dec(v_u_4681_);
                    v___x_4907_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
                    return v___x_4907_;
                } else {
                    v_tail_4908_ = crate::leanh::lean_ctor_get(v_args_4903_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_4908_) == 0 {
                        crate::leanh::lean_del_object(v___x_4905_);
                        v_head_4909_ = crate::leanh::lean_ctor_get(v_args_4903_, 0);
                        crate::leanh::lean_inc(v_head_4909_);
                        crate::leanh::lean_dec_ref_known(v_args_4903_, 2);
                        v_pat_4684_ = v_head_4909_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4908_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4682_);
                        v_head_4911_ = crate::leanh::lean_ctor_get(v_args_4903_, 0);
                        v_isSharedCheck_4996_ =
                            (!crate::leanh::lean_is_exclusive(v_args_4903_)) as u8;
                        if v_isSharedCheck_4996_ == 0 {
                            v_unused_4997_ = crate::leanh::lean_ctor_get(v_args_4903_, 1);
                            crate::leanh::lean_dec(v_unused_4997_);
                            v___x_4913_ = v_args_4903_;
                            v_isShared_4914_ = v_isSharedCheck_4996_;
                            state = 36;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_4911_);
                            crate::leanh::lean_dec(v_args_4903_);
                            v___x_4913_ = crate::leanh::lean_box(0);
                            v_isShared_4914_ = v_isSharedCheck_4996_;
                            state = 36;
                            continue;
                        }
                    }
                }
            }
            36 => {
                v___x_4915_ = l_Lean_Expr_consumeMData(v_H_4683_);
                v___x_4916_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9;
                v___x_4917_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4918_ = l_Lean_Expr_isAppOfArity(v___x_4915_, v___x_4916_, v___x_4917_);
                if v___x_4918_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4915_);
                    crate::leanh::lean_del_object(v___x_4913_);
                    crate::leanh::lean_dec(v_head_4911_);
                    crate::leanh::lean_dec(v_tail_4908_);
                    crate::leanh::lean_del_object(v___x_4905_);
                    crate::leanh::lean_dec_ref(v_k_4685_);
                    crate::leanh::lean_dec(v_u_4681_);
                    v___x_4919_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11,
                    );
                    v___x_4920_ = l_Lean_MessageData_ofExpr(v_H_4683_);
                    v___x_4921_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4921_, 0, v___x_4919_);
                    crate::leanh::lean_ctor_set(v___x_4921_, 1, v___x_4920_);
                    v___x_4922_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_4921_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                    return v___x_4922_;
                } else {
                    crate::leanh::lean_dec_ref(v_H_4683_);
                    v___x_4923_ = l_Lean_Expr_appFn_x21(v___x_4915_);
                    v___x_4924_ = l_Lean_Expr_appFn_x21(v___x_4923_);
                    v___x_4925_ = l_Lean_Expr_appArg_x21(v___x_4924_);
                    crate::leanh::lean_dec_ref(v___x_4924_);
                    v___x_4926_ = l_Lean_Expr_appArg_x21(v___x_4923_);
                    crate::leanh::lean_dec_ref(v___x_4923_);
                    crate::leanh::lean_inc_ref(v_k_4685_);
                    crate::leanh::lean_inc_ref(v___x_4926_);
                    crate::leanh::lean_inc_ref(v___x_4925_);
                    crate::leanh::lean_inc(v_u_4681_);
                    v___x_4927_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
                        v_u_4681_,
                        v___x_4925_,
                        v___x_4926_,
                        v_head_4911_,
                        v_k_4685_,
                        v_a_4686_,
                        v_a_4687_,
                        v_a_4688_,
                        v_a_4689_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4927_) == 0 {
                        v_a_4928_ = crate::leanh::lean_ctor_get(v___x_4927_, 0);
                        crate::leanh::lean_inc(v_a_4928_);
                        crate::leanh::lean_dec_ref_known(v___x_4927_, 1);
                        v_snd_4929_ = crate::leanh::lean_ctor_get(v_a_4928_, 1);
                        crate::leanh::lean_inc(v_snd_4929_);
                        crate::leanh::lean_dec(v_a_4928_);
                        v_fst_4930_ = crate::leanh::lean_ctor_get(v_snd_4929_, 0);
                        crate::leanh::lean_inc(v_fst_4930_);
                        v_snd_4931_ = crate::leanh::lean_ctor_get(v_snd_4929_, 1);
                        crate::leanh::lean_inc(v_snd_4931_);
                        crate::leanh::lean_dec(v_snd_4929_);
                        v___x_4932_ = l_Lean_Expr_appArg_x21(v___x_4915_);
                        crate::leanh::lean_dec_ref(v___x_4915_);
                        if v_isShared_4906_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4905_, 0, v_tail_4908_);
                            v___x_4934_ = v___x_4905_;
                            state = 37;
                            continue;
                        } else {
                            v_reuseFailAlloc_4995_ =
                                crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_tail_4908_);
                            v___x_4934_ = v_reuseFailAlloc_4995_;
                            state = 37;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4926_);
                        crate::leanh::lean_dec_ref(v___x_4925_);
                        crate::leanh::lean_dec_ref(v___x_4915_);
                        crate::leanh::lean_del_object(v___x_4913_);
                        crate::leanh::lean_dec(v_tail_4908_);
                        crate::leanh::lean_del_object(v___x_4905_);
                        crate::leanh::lean_dec_ref(v_k_4685_);
                        crate::leanh::lean_dec(v_u_4681_);
                        return v___x_4927_;
                    }
                }
            }
            37 => {
                crate::leanh::lean_inc_ref(v___x_4932_);
                crate::leanh::lean_inc_ref(v___x_4925_);
                crate::leanh::lean_inc(v_u_4681_);
                v___x_4935_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
                    v_u_4681_,
                    v___x_4925_,
                    v___x_4932_,
                    v___x_4934_,
                    v_k_4685_,
                    v_a_4686_,
                    v_a_4687_,
                    v_a_4688_,
                    v_a_4689_,
                );
                if crate::leanh::lean_obj_tag(v___x_4935_) == 0 {
                    v_a_4936_ = crate::leanh::lean_ctor_get(v___x_4935_, 0);
                    crate::leanh::lean_inc(v_a_4936_);
                    crate::leanh::lean_dec_ref_known(v___x_4935_, 1);
                    v_snd_4937_ = crate::leanh::lean_ctor_get(v_a_4936_, 1);
                    crate::leanh::lean_inc(v_snd_4937_);
                    v_fst_4938_ = crate::leanh::lean_ctor_get(v_a_4936_, 0);
                    crate::leanh::lean_inc(v_fst_4938_);
                    crate::leanh::lean_dec(v_a_4936_);
                    v_snd_4939_ = crate::leanh::lean_ctor_get(v_snd_4937_, 1);
                    v_isSharedCheck_4993_ = (!crate::leanh::lean_is_exclusive(v_snd_4937_)) as u8;
                    if v_isSharedCheck_4993_ == 0 {
                        v_unused_4994_ = crate::leanh::lean_ctor_get(v_snd_4937_, 0);
                        crate::leanh::lean_dec(v_unused_4994_);
                        v___x_4941_ = v_snd_4937_;
                        v_isShared_4942_ = v_isSharedCheck_4993_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4939_);
                        crate::leanh::lean_dec(v_snd_4937_);
                        v___x_4941_ = crate::leanh::lean_box(0);
                        v_isShared_4942_ = v_isSharedCheck_4993_;
                        state = 38;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4932_);
                    crate::leanh::lean_dec(v_snd_4931_);
                    crate::leanh::lean_dec(v_fst_4930_);
                    crate::leanh::lean_dec_ref(v___x_4926_);
                    crate::leanh::lean_dec_ref(v___x_4925_);
                    crate::leanh::lean_del_object(v___x_4913_);
                    crate::leanh::lean_dec(v_u_4681_);
                    return v___x_4935_;
                }
            }
            38 => {
                crate::leanh::lean_inc(v_fst_4930_);
                v___x_4943_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_4930_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
                if crate::leanh::lean_obj_tag(v___x_4943_) == 0 {
                    v_a_4944_ = crate::leanh::lean_ctor_get(v___x_4943_, 0);
                    v_isSharedCheck_4984_ = (!crate::leanh::lean_is_exclusive(v___x_4943_)) as u8;
                    if v_isSharedCheck_4984_ == 0 {
                        v___x_4946_ = v___x_4943_;
                        v_isShared_4947_ = v_isSharedCheck_4984_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4944_);
                        crate::leanh::lean_dec(v___x_4943_);
                        v___x_4946_ = crate::leanh::lean_box(0);
                        v_isShared_4947_ = v_isSharedCheck_4984_;
                        state = 39;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4941_);
                    crate::leanh::lean_dec(v_snd_4939_);
                    crate::leanh::lean_dec(v_fst_4938_);
                    crate::leanh::lean_dec_ref(v___x_4932_);
                    crate::leanh::lean_dec(v_snd_4931_);
                    crate::leanh::lean_dec(v_fst_4930_);
                    crate::leanh::lean_dec_ref(v___x_4926_);
                    crate::leanh::lean_dec_ref(v___x_4925_);
                    crate::leanh::lean_del_object(v___x_4913_);
                    crate::leanh::lean_dec(v_u_4681_);
                    v_a_4985_ = crate::leanh::lean_ctor_get(v___x_4943_, 0);
                    v_isSharedCheck_4992_ = (!crate::leanh::lean_is_exclusive(v___x_4943_)) as u8;
                    if v_isSharedCheck_4992_ == 0 {
                        v___x_4987_ = v___x_4943_;
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 47;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4985_);
                        crate::leanh::lean_dec(v___x_4943_);
                        v___x_4987_ = crate::leanh::lean_box(0);
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 47;
                        continue;
                    }
                }
            }
            39 => {
                v_fst_4948_ = crate::leanh::lean_ctor_get(v_a_4944_, 0);
                v_isSharedCheck_4982_ = (!crate::leanh::lean_is_exclusive(v_a_4944_)) as u8;
                if v_isSharedCheck_4982_ == 0 {
                    v_unused_4983_ = crate::leanh::lean_ctor_get(v_a_4944_, 1);
                    crate::leanh::lean_dec(v_unused_4983_);
                    v___x_4950_ = v_a_4944_;
                    v_isShared_4951_ = v_isSharedCheck_4982_;
                    state = 40;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4948_);
                    crate::leanh::lean_dec(v_a_4944_);
                    v___x_4950_ = crate::leanh::lean_box(0);
                    v_isShared_4951_ = v_isSharedCheck_4982_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v_u_4952_ = crate::leanh::lean_ctor_get(v_fst_4930_, 0);
                v_00_u03c3s_4953_ = crate::leanh::lean_ctor_get(v_fst_4930_, 1);
                v_target_4954_ = crate::leanh::lean_ctor_get(v_fst_4930_, 3);
                v_isSharedCheck_4980_ = (!crate::leanh::lean_is_exclusive(v_fst_4930_)) as u8;
                if v_isSharedCheck_4980_ == 0 {
                    v_unused_4981_ = crate::leanh::lean_ctor_get(v_fst_4930_, 2);
                    crate::leanh::lean_dec(v_unused_4981_);
                    v___x_4956_ = v_fst_4930_;
                    v_isShared_4957_ = v_isSharedCheck_4980_;
                    state = 41;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_4954_);
                    crate::leanh::lean_inc(v_00_u03c3s_4953_);
                    crate::leanh::lean_inc(v_u_4952_);
                    crate::leanh::lean_dec(v_fst_4930_);
                    v___x_4956_ = crate::leanh::lean_box(0);
                    v_isShared_4957_ = v_isSharedCheck_4980_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                v___x_4958_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_4681_);
                if v_isShared_4914_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4913_, 1, v___x_4958_);
                    crate::leanh::lean_ctor_set(v___x_4913_, 0, v_u_4681_);
                    v___x_4960_ = v___x_4913_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4979_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_u_4681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4979_, 1, v___x_4958_);
                    v___x_4960_ = v_reuseFailAlloc_4979_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                crate::leanh::lean_inc_ref(v___x_4960_);
                v___x_4961_ = l_Lean_mkConst(v___x_4916_, v___x_4960_);
                crate::leanh::lean_inc_ref(v___x_4932_);
                crate::leanh::lean_inc_ref(v___x_4926_);
                crate::leanh::lean_inc_ref_n(v___x_4925_, 2);
                v___x_4962_ = l_Lean_mkApp3(v___x_4961_, v___x_4925_, v___x_4926_, v___x_4932_);
                crate::leanh::lean_inc(v_fst_4948_);
                v___x_4963_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_4681_,
                    v___x_4925_,
                    v_fst_4948_,
                    v___x_4962_,
                );
                crate::leanh::lean_inc_ref(v_target_4954_);
                if v_isShared_4957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4956_, 2, v___x_4963_);
                    v___x_4965_ = v___x_4956_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4978_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_u_4952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 1, v_00_u03c3s_4953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 2, v___x_4963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 3, v_target_4954_);
                    v___x_4965_ = v_reuseFailAlloc_4978_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_4966_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13;
                v___x_4967_ = l_Lean_mkConst(v___x_4966_, v___x_4960_);
                v___x_4968_ = l_Lean_mkApp7(
                    v___x_4967_,
                    v___x_4925_,
                    v_fst_4948_,
                    v___x_4926_,
                    v___x_4932_,
                    v_target_4954_,
                    v_snd_4931_,
                    v_snd_4939_,
                );
                if v_isShared_4951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4950_, 1, v___x_4968_);
                    crate::leanh::lean_ctor_set(v___x_4950_, 0, v___x_4965_);
                    v___x_4970_ = v___x_4950_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4977_, 1, v___x_4968_);
                    v___x_4970_ = v_reuseFailAlloc_4977_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_4942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4941_, 1, v___x_4970_);
                    crate::leanh::lean_ctor_set(v___x_4941_, 0, v_fst_4938_);
                    v___x_4972_ = v___x_4941_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4976_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_fst_4938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4976_, 1, v___x_4970_);
                    v___x_4972_ = v_reuseFailAlloc_4976_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_4947_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4946_, 0, v___x_4972_);
                    v___x_4974_ = v___x_4946_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4975_, 0, v___x_4972_);
                    v___x_4974_ = v_reuseFailAlloc_4975_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_4974_;
            }
            47 => {
                if v_isShared_4988_ == 0 {
                    v___x_4990_ = v___x_4987_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
                    v___x_4990_ = v_reuseFailAlloc_4991_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4990_;
            }
            49 => {
                if v_isShared_5018_ == 0 {
                    v___x_5020_ = v___x_5017_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_5021_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5015_);
                    v___x_5020_ = v_reuseFailAlloc_5021_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_5020_;
            }
            51 => {
                if v_isShared_5026_ == 0 {
                    v___x_5028_ = v___x_5025_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5029_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_a_5023_);
                    v___x_5028_ = v_reuseFailAlloc_5029_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5028_;
            }
            53 => {
                if v_isShared_5034_ == 0 {
                    v___x_5036_ = v___x_5033_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_5037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
                    v___x_5036_ = v_reuseFailAlloc_5037_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_5036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(
    mut v___x_5039_: *mut crate::leanh::LeanObject,
    mut v_tail_5040_: *mut crate::leanh::LeanObject,
    mut v_u_5041_: *mut crate::leanh::LeanObject,
    mut v___x_5042_: *mut crate::leanh::LeanObject,
    mut v_k_5043_: *mut crate::leanh::LeanObject,
    mut v_x_5044_: *mut crate::leanh::LeanObject,
    mut v___y_5045_: *mut crate::leanh::LeanObject,
    mut v___y_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: u8 = 0;
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5050_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_5051_ = lean_mk_empty_array_with_capacity(v___x_5050_);
    v___x_5052_ = lean_array_push(v___x_5051_, v_x_5044_);
    v___x_5053_ = 0;
    v___x_5054_ = l_Lean_Expr_betaRev(v___x_5039_, v___x_5052_, v___x_5053_, v___x_5053_);
    crate::leanh::lean_dec_ref(v___x_5052_);
    v___x_5055_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5055_, 0, v_tail_5040_);
    v___x_5056_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
        v_u_5041_,
        v___x_5042_,
        v___x_5054_,
        v___x_5055_,
        v_k_5043_,
        v___y_5045_,
        v___y_5046_,
        v___y_5047_,
        v___y_5048_,
    );
    return v___x_5056_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___boxed(
    mut v_u_5057_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5058_: *mut crate::leanh::LeanObject,
    mut v_H_5059_: *mut crate::leanh::LeanObject,
    mut v_pat_5060_: *mut crate::leanh::LeanObject,
    mut v_k_5061_: *mut crate::leanh::LeanObject,
    mut v_a_5062_: *mut crate::leanh::LeanObject,
    mut v_a_5063_: *mut crate::leanh::LeanObject,
    mut v_a_5064_: *mut crate::leanh::LeanObject,
    mut v_a_5065_: *mut crate::leanh::LeanObject,
    mut v_a_5066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5067_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
        v_u_5057_,
        v_00_u03c3s_5058_,
        v_H_5059_,
        v_pat_5060_,
        v_k_5061_,
        v_a_5062_,
        v_a_5063_,
        v_a_5064_,
        v_a_5065_,
    );
    crate::leanh::lean_dec(v_a_5065_);
    crate::leanh::lean_dec_ref(v_a_5064_);
    crate::leanh::lean_dec(v_a_5063_);
    crate::leanh::lean_dec_ref(v_a_5062_);
    return v_res_5067_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(
    mut v_00_u03b1_5068_: *mut crate::leanh::LeanObject,
    mut v_u_5069_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5070_: *mut crate::leanh::LeanObject,
    mut v_H_5071_: *mut crate::leanh::LeanObject,
    mut v_pat_5072_: *mut crate::leanh::LeanObject,
    mut v_k_5073_: *mut crate::leanh::LeanObject,
    mut v_a_5074_: *mut crate::leanh::LeanObject,
    mut v_a_5075_: *mut crate::leanh::LeanObject,
    mut v_a_5076_: *mut crate::leanh::LeanObject,
    mut v_a_5077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5079_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
        v_u_5069_,
        v_00_u03c3s_5070_,
        v_H_5071_,
        v_pat_5072_,
        v_k_5073_,
        v_a_5074_,
        v_a_5075_,
        v_a_5076_,
        v_a_5077_,
    );
    return v___x_5079_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___boxed(
    mut v_00_u03b1_5080_: *mut crate::leanh::LeanObject,
    mut v_u_5081_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5082_: *mut crate::leanh::LeanObject,
    mut v_H_5083_: *mut crate::leanh::LeanObject,
    mut v_pat_5084_: *mut crate::leanh::LeanObject,
    mut v_k_5085_: *mut crate::leanh::LeanObject,
    mut v_a_5086_: *mut crate::leanh::LeanObject,
    mut v_a_5087_: *mut crate::leanh::LeanObject,
    mut v_a_5088_: *mut crate::leanh::LeanObject,
    mut v_a_5089_: *mut crate::leanh::LeanObject,
    mut v_a_5090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5091_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(
        v_00_u03b1_5080_,
        v_u_5081_,
        v_00_u03c3s_5082_,
        v_H_5083_,
        v_pat_5084_,
        v_k_5085_,
        v_a_5086_,
        v_a_5087_,
        v_a_5088_,
        v_a_5089_,
    );
    crate::leanh::lean_dec(v_a_5089_);
    crate::leanh::lean_dec_ref(v_a_5088_);
    crate::leanh::lean_dec(v_a_5087_);
    crate::leanh::lean_dec_ref(v_a_5086_);
    return v_res_5091_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(
    mut v_00_u03b1_5092_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5093_: *mut crate::leanh::LeanObject,
    mut v_hyp_5094_: *mut crate::leanh::LeanObject,
    mut v_name_5095_: *mut crate::leanh::LeanObject,
    mut v_k_5096_: *mut crate::leanh::LeanObject,
    mut v___y_5097_: *mut crate::leanh::LeanObject,
    mut v___y_5098_: *mut crate::leanh::LeanObject,
    mut v___y_5099_: *mut crate::leanh::LeanObject,
    mut v___y_5100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5102_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_5093_, v_hyp_5094_, v_name_5095_, v_k_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
    return v___x_5102_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(
    mut v_00_u03b1_5103_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5104_: *mut crate::leanh::LeanObject,
    mut v_hyp_5105_: *mut crate::leanh::LeanObject,
    mut v_name_5106_: *mut crate::leanh::LeanObject,
    mut v_k_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
    mut v___y_5109_: *mut crate::leanh::LeanObject,
    mut v___y_5110_: *mut crate::leanh::LeanObject,
    mut v___y_5111_: *mut crate::leanh::LeanObject,
    mut v___y_5112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5113_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(v_00_u03b1_5103_, v_00_u03c3s_5104_, v_hyp_5105_, v_name_5106_, v_k_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_);
    crate::leanh::lean_dec(v___y_5111_);
    crate::leanh::lean_dec_ref(v___y_5110_);
    crate::leanh::lean_dec(v___y_5109_);
    crate::leanh::lean_dec_ref(v___y_5108_);
    return v_res_5113_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5115_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
    v___x_5116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5116_, 0, v___x_5115_);
    return v___x_5116_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(
    mut v___y_5117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5118_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
    return v_res_5118_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(
    mut v_00_u03b1_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
    mut v___y_5121_: *mut crate::leanh::LeanObject,
    mut v___y_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5129_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
    return v___x_5129_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(
    mut v_00_u03b1_5130_: *mut crate::leanh::LeanObject,
    mut v___y_5131_: *mut crate::leanh::LeanObject,
    mut v___y_5132_: *mut crate::leanh::LeanObject,
    mut v___y_5133_: *mut crate::leanh::LeanObject,
    mut v___y_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
    mut v___y_5139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5140_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(v_00_u03b1_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
    crate::leanh::lean_dec(v___y_5138_);
    crate::leanh::lean_dec_ref(v___y_5137_);
    crate::leanh::lean_dec(v___y_5136_);
    crate::leanh::lean_dec_ref(v___y_5135_);
    crate::leanh::lean_dec(v___y_5134_);
    crate::leanh::lean_dec_ref(v___y_5133_);
    crate::leanh::lean_dec(v___y_5132_);
    crate::leanh::lean_dec_ref(v___y_5131_);
    return v_res_5140_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(
    mut v_x_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
    mut v___y_5146_: *mut crate::leanh::LeanObject,
    mut v___y_5147_: *mut crate::leanh::LeanObject,
    mut v___y_5148_: *mut crate::leanh::LeanObject,
    mut v___y_5149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5145_);
    crate::leanh::lean_inc_ref(v___y_5144_);
    crate::leanh::lean_inc(v___y_5143_);
    crate::leanh::lean_inc_ref(v___y_5142_);
    v___x_5151_ = crate::leanh::lean_apply_9(
        v_x_5141_,
        v___y_5142_,
        v___y_5143_,
        v___y_5144_,
        v___y_5145_,
        v___y_5146_,
        v___y_5147_,
        v___y_5148_,
        v___y_5149_,
        crate::leanh::lean_box(0),
    );
    return v___x_5151_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(
    mut v_x_5152_: *mut crate::leanh::LeanObject,
    mut v___y_5153_: *mut crate::leanh::LeanObject,
    mut v___y_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
    mut v___y_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5162_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(v_x_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
    crate::leanh::lean_dec(v___y_5156_);
    crate::leanh::lean_dec_ref(v___y_5155_);
    crate::leanh::lean_dec(v___y_5154_);
    crate::leanh::lean_dec_ref(v___y_5153_);
    return v_res_5162_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(
    mut v_mvarId_5163_: *mut crate::leanh::LeanObject,
    mut v_x_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
    mut v___y_5168_: *mut crate::leanh::LeanObject,
    mut v___y_5169_: *mut crate::leanh::LeanObject,
    mut v___y_5170_: *mut crate::leanh::LeanObject,
    mut v___y_5171_: *mut crate::leanh::LeanObject,
    mut v___y_5172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5168_);
                crate::leanh::lean_inc_ref(v___y_5167_);
                crate::leanh::lean_inc(v___y_5166_);
                crate::leanh::lean_inc_ref(v___y_5165_);
                v___f_5174_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_5174_, 0, v_x_5164_);
                crate::leanh::lean_closure_set(v___f_5174_, 1, v___y_5165_);
                crate::leanh::lean_closure_set(v___f_5174_, 2, v___y_5166_);
                crate::leanh::lean_closure_set(v___f_5174_, 3, v___y_5167_);
                crate::leanh::lean_closure_set(v___f_5174_, 4, v___y_5168_);
                v___x_5175_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_5163_,
                    v___f_5174_,
                    v___y_5169_,
                    v___y_5170_,
                    v___y_5171_,
                    v___y_5172_,
                );
                if crate::leanh::lean_obj_tag(v___x_5175_) == 0 {
                    return v___x_5175_;
                } else {
                    v_a_5176_ = crate::leanh::lean_ctor_get(v___x_5175_, 0);
                    v_isSharedCheck_5183_ = (!crate::leanh::lean_is_exclusive(v___x_5175_)) as u8;
                    if v_isSharedCheck_5183_ == 0 {
                        v___x_5178_ = v___x_5175_;
                        v_isShared_5179_ = v_isSharedCheck_5183_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5176_);
                        crate::leanh::lean_dec(v___x_5175_);
                        v___x_5178_ = crate::leanh::lean_box(0);
                        v_isShared_5179_ = v_isSharedCheck_5183_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5179_ == 0 {
                    v___x_5181_ = v___x_5178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5182_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
                    v___x_5181_ = v_reuseFailAlloc_5182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___boxed(
    mut v_mvarId_5184_: *mut crate::leanh::LeanObject,
    mut v_x_5185_: *mut crate::leanh::LeanObject,
    mut v___y_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
    mut v___y_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
    mut v___y_5190_: *mut crate::leanh::LeanObject,
    mut v___y_5191_: *mut crate::leanh::LeanObject,
    mut v___y_5192_: *mut crate::leanh::LeanObject,
    mut v___y_5193_: *mut crate::leanh::LeanObject,
    mut v___y_5194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5195_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_5184_, v_x_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
    crate::leanh::lean_dec(v___y_5193_);
    crate::leanh::lean_dec_ref(v___y_5192_);
    crate::leanh::lean_dec(v___y_5191_);
    crate::leanh::lean_dec_ref(v___y_5190_);
    crate::leanh::lean_dec(v___y_5189_);
    crate::leanh::lean_dec_ref(v___y_5188_);
    crate::leanh::lean_dec(v___y_5187_);
    crate::leanh::lean_dec_ref(v___y_5186_);
    return v_res_5195_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(
    mut v_00_u03b1_5196_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5197_: *mut crate::leanh::LeanObject,
    mut v_x_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
    mut v___y_5200_: *mut crate::leanh::LeanObject,
    mut v___y_5201_: *mut crate::leanh::LeanObject,
    mut v___y_5202_: *mut crate::leanh::LeanObject,
    mut v___y_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5208_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_5197_, v_x_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
    return v___x_5208_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(
    mut v_00_u03b1_5209_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5210_: *mut crate::leanh::LeanObject,
    mut v_x_5211_: *mut crate::leanh::LeanObject,
    mut v___y_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
    mut v___y_5215_: *mut crate::leanh::LeanObject,
    mut v___y_5216_: *mut crate::leanh::LeanObject,
    mut v___y_5217_: *mut crate::leanh::LeanObject,
    mut v___y_5218_: *mut crate::leanh::LeanObject,
    mut v___y_5219_: *mut crate::leanh::LeanObject,
    mut v___y_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5221_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(
            v_00_u03b1_5209_,
            v_mvarId_5210_,
            v_x_5211_,
            v___y_5212_,
            v___y_5213_,
            v___y_5214_,
            v___y_5215_,
            v___y_5216_,
            v___y_5217_,
            v___y_5218_,
            v___y_5219_,
        );
    crate::leanh::lean_dec(v___y_5219_);
    crate::leanh::lean_dec_ref(v___y_5218_);
    crate::leanh::lean_dec(v___y_5217_);
    crate::leanh::lean_dec_ref(v___y_5216_);
    crate::leanh::lean_dec(v___y_5215_);
    crate::leanh::lean_dec_ref(v___y_5214_);
    crate::leanh::lean_dec(v___y_5213_);
    crate::leanh::lean_dec_ref(v___y_5212_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(
    mut v_x_5222_: *mut crate::leanh::LeanObject,
    mut v_x_5223_: *mut crate::leanh::LeanObject,
    mut v_x_5224_: *mut crate::leanh::LeanObject,
    mut v_x_5225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5230_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: u8 = 0;
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5251_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5226_ = crate::leanh::lean_ctor_get(v_x_5222_, 0);
                v_vs_5227_ = crate::leanh::lean_ctor_get(v_x_5222_, 1);
                v_isSharedCheck_5251_ = (!crate::leanh::lean_is_exclusive(v_x_5222_)) as u8;
                if v_isSharedCheck_5251_ == 0 {
                    v___x_5229_ = v_x_5222_;
                    v_isShared_5230_ = v_isSharedCheck_5251_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_5227_);
                    crate::leanh::lean_inc(v_ks_5226_);
                    crate::leanh::lean_dec(v_x_5222_);
                    v___x_5229_ = crate::leanh::lean_box(0);
                    v_isShared_5230_ = v_isSharedCheck_5251_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5231_ = lean_array_get_size(v_ks_5226_);
                v___x_5232_ = lean_nat_dec_lt(v_x_5223_, v___x_5231_);
                if v___x_5232_ == 0 {
                    crate::leanh::lean_dec(v_x_5223_);
                    v___x_5233_ = lean_array_push(v_ks_5226_, v_x_5224_);
                    v___x_5234_ = lean_array_push(v_vs_5227_, v_x_5225_);
                    if v_isShared_5230_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5229_, 1, v___x_5234_);
                        crate::leanh::lean_ctor_set(v___x_5229_, 0, v___x_5233_);
                        v___x_5236_ = v___x_5229_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5237_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5233_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5237_, 1, v___x_5234_);
                        v___x_5236_ = v_reuseFailAlloc_5237_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5238_ = lean_array_fget_borrowed(v_ks_5226_, v_x_5223_);
                    v___x_5239_ = l_Lean_instBEqMVarId_beq(v_x_5224_, v_k_x27_5238_);
                    if v___x_5239_ == 0 {
                        if v_isShared_5230_ == 0 {
                            v___x_5241_ = v___x_5229_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5245_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_ks_5226_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 1, v_vs_5227_);
                            v___x_5241_ = v_reuseFailAlloc_5245_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5246_ = lean_array_fset(v_ks_5226_, v_x_5223_, v_x_5224_);
                        v___x_5247_ = lean_array_fset(v_vs_5227_, v_x_5223_, v_x_5225_);
                        crate::leanh::lean_dec(v_x_5223_);
                        if v_isShared_5230_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5229_, 1, v___x_5247_);
                            crate::leanh::lean_ctor_set(v___x_5229_, 0, v___x_5246_);
                            v___x_5249_ = v___x_5229_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5250_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5246_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5250_, 1, v___x_5247_);
                            v___x_5249_ = v_reuseFailAlloc_5250_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5236_;
            }
            3 => {
                v___x_5242_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5243_ = lean_nat_add(v_x_5223_, v___x_5242_);
                crate::leanh::lean_dec(v_x_5223_);
                v_x_5222_ = v___x_5241_;
                v_x_5223_ = v___x_5243_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(
    mut v_n_5252_: *mut crate::leanh::LeanObject,
    mut v_k_5253_: *mut crate::leanh::LeanObject,
    mut v_v_5254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5255_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5256_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_n_5252_, v___x_5255_, v_k_5253_, v_v_5254_);
    return v___x_5256_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0()
-> usize {
    let mut v___x_5257_: usize = 0;
    let mut v___x_5258_: usize = 0;
    let mut v___x_5259_: usize = 0;
    v___x_5257_ = 5usize;
    v___x_5258_ = 1usize;
    v___x_5259_ = lean_usize_shift_left(v___x_5258_, v___x_5257_);
    return v___x_5259_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1()
-> usize {
    let mut v___x_5260_: usize = 0;
    let mut v___x_5261_: usize = 0;
    let mut v___x_5262_: usize = 0;
    v___x_5260_ = 1usize;
    v___x_5261_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0);
    v___x_5262_ = lean_usize_sub(v___x_5261_, v___x_5260_);
    return v___x_5262_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5263_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5263_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(
    mut v_x_5264_: *mut crate::leanh::LeanObject,
    mut v_x_5265_: usize,
    mut v_x_5266_: usize,
    mut v_x_5267_: *mut crate::leanh::LeanObject,
    mut v_x_5268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: usize = 0;
    let mut v___x_5271_: usize = 0;
    let mut v___x_5272_: usize = 0;
    let mut v___x_5273_: usize = 0;
    let mut v_j_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: u8 = 0;
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v_v_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v___x_5294_: u8 = 0;
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5300_: u8 = 0;
    let mut v_node_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5304_: u8 = 0;
    let mut v___x_5305_: usize = 0;
    let mut v___x_5306_: usize = 0;
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5311_: u8 = 0;
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5313_: u8 = 0;
    let mut v_unused_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5319_: u8 = 0;
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5324_: u8 = 0;
    let mut v_ks_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: usize = 0;
    let mut v___x_5331_: u8 = 0;
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: u8 = 0;
    let mut v_reuseFailAlloc_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5264_) == 0 {
                    v_es_5269_ = crate::leanh::lean_ctor_get(v_x_5264_, 0);
                    v___x_5270_ = 5usize;
                    v___x_5271_ = 1usize;
                    v___x_5272_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1);
                    v___x_5273_ = lean_usize_land(v_x_5265_, v___x_5272_);
                    v_j_5274_ = lean_usize_to_nat(v___x_5273_);
                    v___x_5275_ = lean_array_get_size(v_es_5269_);
                    v___x_5276_ = lean_nat_dec_lt(v_j_5274_, v___x_5275_);
                    if v___x_5276_ == 0 {
                        crate::leanh::lean_dec(v_j_5274_);
                        crate::leanh::lean_dec(v_x_5268_);
                        crate::leanh::lean_dec(v_x_5267_);
                        return v_x_5264_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_5269_);
                        v_isSharedCheck_5313_ = (!crate::leanh::lean_is_exclusive(v_x_5264_)) as u8;
                        if v_isSharedCheck_5313_ == 0 {
                            v_unused_5314_ = crate::leanh::lean_ctor_get(v_x_5264_, 0);
                            crate::leanh::lean_dec(v_unused_5314_);
                            v___x_5278_ = v_x_5264_;
                            v_isShared_5279_ = v_isSharedCheck_5313_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_5264_);
                            v___x_5278_ = crate::leanh::lean_box(0);
                            v_isShared_5279_ = v_isSharedCheck_5313_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5315_ = crate::leanh::lean_ctor_get(v_x_5264_, 0);
                    v_vs_5316_ = crate::leanh::lean_ctor_get(v_x_5264_, 1);
                    v_isSharedCheck_5336_ = (!crate::leanh::lean_is_exclusive(v_x_5264_)) as u8;
                    if v_isSharedCheck_5336_ == 0 {
                        v___x_5318_ = v_x_5264_;
                        v_isShared_5319_ = v_isSharedCheck_5336_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5316_);
                        crate::leanh::lean_inc(v_ks_5315_);
                        crate::leanh::lean_dec(v_x_5264_);
                        v___x_5318_ = crate::leanh::lean_box(0);
                        v_isShared_5319_ = v_isSharedCheck_5336_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5280_ = lean_array_fget(v_es_5269_, v_j_5274_);
                v___x_5281_ = crate::leanh::lean_box(0);
                v_xs_x27_5282_ = lean_array_fset(v_es_5269_, v_j_5274_, v___x_5281_);
                match crate::leanh::lean_obj_tag(v_v_5280_) {
                    0 => {
                        v_key_5289_ = crate::leanh::lean_ctor_get(v_v_5280_, 0);
                        v_val_5290_ = crate::leanh::lean_ctor_get(v_v_5280_, 1);
                        v_isSharedCheck_5300_ = (!crate::leanh::lean_is_exclusive(v_v_5280_)) as u8;
                        if v_isSharedCheck_5300_ == 0 {
                            v___x_5292_ = v_v_5280_;
                            v_isShared_5293_ = v_isSharedCheck_5300_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5290_);
                            crate::leanh::lean_inc(v_key_5289_);
                            crate::leanh::lean_dec(v_v_5280_);
                            v___x_5292_ = crate::leanh::lean_box(0);
                            v_isShared_5293_ = v_isSharedCheck_5300_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5301_ = crate::leanh::lean_ctor_get(v_v_5280_, 0);
                        v_isSharedCheck_5311_ = (!crate::leanh::lean_is_exclusive(v_v_5280_)) as u8;
                        if v_isSharedCheck_5311_ == 0 {
                            v___x_5303_ = v_v_5280_;
                            v_isShared_5304_ = v_isSharedCheck_5311_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_5301_);
                            crate::leanh::lean_dec(v_v_5280_);
                            v___x_5303_ = crate::leanh::lean_box(0);
                            v_isShared_5304_ = v_isSharedCheck_5311_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5312_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5312_, 0, v_x_5267_);
                        crate::leanh::lean_ctor_set(v___x_5312_, 1, v_x_5268_);
                        v___y_5284_ = v___x_5312_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5285_ = lean_array_fset(v_xs_x27_5282_, v_j_5274_, v___y_5284_);
                crate::leanh::lean_dec(v_j_5274_);
                if v_isShared_5279_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5278_, 0, v___x_5285_);
                    v___x_5287_ = v___x_5278_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5288_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5288_, 0, v___x_5285_);
                    v___x_5287_ = v_reuseFailAlloc_5288_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5287_;
            }
            4 => {
                v___x_5294_ = l_Lean_instBEqMVarId_beq(v_x_5267_, v_key_5289_);
                if v___x_5294_ == 0 {
                    crate::leanh::lean_del_object(v___x_5292_);
                    v___x_5295_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5289_,
                        v_val_5290_,
                        v_x_5267_,
                        v_x_5268_,
                    );
                    v___x_5296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5296_, 0, v___x_5295_);
                    v___y_5284_ = v___x_5296_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_5290_);
                    crate::leanh::lean_dec(v_key_5289_);
                    if v_isShared_5293_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5292_, 1, v_x_5268_);
                        crate::leanh::lean_ctor_set(v___x_5292_, 0, v_x_5267_);
                        v___x_5298_ = v___x_5292_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5299_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_x_5267_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5299_, 1, v_x_5268_);
                        v___x_5298_ = v_reuseFailAlloc_5299_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5284_ = v___x_5298_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5305_ = lean_usize_shift_right(v_x_5265_, v___x_5270_);
                v___x_5306_ = lean_usize_add(v_x_5266_, v___x_5271_);
                v___x_5307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_node_5301_, v___x_5305_, v___x_5306_, v_x_5267_, v_x_5268_);
                if v_isShared_5304_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5303_, 0, v___x_5307_);
                    v___x_5309_ = v___x_5303_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5307_);
                    v___x_5309_ = v_reuseFailAlloc_5310_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5284_ = v___x_5309_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5319_ == 0 {
                    v___x_5321_ = v___x_5318_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5335_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_ks_5315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5335_, 1, v_vs_5316_);
                    v___x_5321_ = v_reuseFailAlloc_5335_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5322_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v___x_5321_, v_x_5267_, v_x_5268_);
                v___x_5330_ = 7usize;
                v___x_5331_ = lean_usize_dec_le(v___x_5330_, v_x_5266_);
                if v___x_5331_ == 0 {
                    v___x_5332_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5322_);
                    v___x_5333_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5334_ = lean_nat_dec_lt(v___x_5332_, v___x_5333_);
                    crate::leanh::lean_dec(v___x_5332_);
                    v___y_5324_ = v___x_5334_;
                    state = 10;
                    continue;
                } else {
                    v___y_5324_ = v___x_5331_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5324_ == 0 {
                    v_ks_5325_ = crate::leanh::lean_ctor_get(v_newNode_5322_, 0);
                    crate::leanh::lean_inc_ref(v_ks_5325_);
                    v_vs_5326_ = crate::leanh::lean_ctor_get(v_newNode_5322_, 1);
                    crate::leanh::lean_inc_ref(v_vs_5326_);
                    crate::leanh::lean_dec_ref(v_newNode_5322_);
                    v___x_5327_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5328_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__2);
                    v___x_5329_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_x_5266_, v_ks_5325_, v_vs_5326_, v___x_5327_, v___x_5328_);
                    crate::leanh::lean_dec_ref(v_vs_5326_);
                    crate::leanh::lean_dec_ref(v_ks_5325_);
                    return v___x_5329_;
                } else {
                    return v_newNode_5322_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(
    mut v_depth_5337_: usize,
    mut v_keys_5338_: *mut crate::leanh::LeanObject,
    mut v_vals_5339_: *mut crate::leanh::LeanObject,
    mut v_i_5340_: *mut crate::leanh::LeanObject,
    mut v_entries_5341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: u8 = 0;
    let mut v_k_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: u64 = 0;
    let mut v_h_5347_: usize = 0;
    let mut v___x_5348_: usize = 0;
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: usize = 0;
    let mut v___x_5351_: usize = 0;
    let mut v___x_5352_: usize = 0;
    let mut v_h_5353_: usize = 0;
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5342_ = lean_array_get_size(v_keys_5338_);
                v___x_5343_ = lean_nat_dec_lt(v_i_5340_, v___x_5342_);
                if v___x_5343_ == 0 {
                    crate::leanh::lean_dec(v_i_5340_);
                    return v_entries_5341_;
                } else {
                    v_k_5344_ = lean_array_fget_borrowed(v_keys_5338_, v_i_5340_);
                    v_v_5345_ = lean_array_fget_borrowed(v_vals_5339_, v_i_5340_);
                    v___x_5346_ = l_Lean_instHashableMVarId_hash(v_k_5344_);
                    v_h_5347_ = lean_uint64_to_usize(v___x_5346_);
                    v___x_5348_ = 5usize;
                    v___x_5349_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5350_ = 1usize;
                    v___x_5351_ = lean_usize_sub(v_depth_5337_, v___x_5350_);
                    v___x_5352_ = lean_usize_mul(v___x_5348_, v___x_5351_);
                    v_h_5353_ = lean_usize_shift_right(v_h_5347_, v___x_5352_);
                    v___x_5354_ = lean_nat_add(v_i_5340_, v___x_5349_);
                    crate::leanh::lean_dec(v_i_5340_);
                    crate::leanh::lean_inc(v_v_5345_);
                    crate::leanh::lean_inc(v_k_5344_);
                    v___x_5355_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_entries_5341_, v_h_5353_, v_depth_5337_, v_k_5344_, v_v_5345_);
                    v_i_5340_ = v___x_5354_;
                    v_entries_5341_ = v___x_5355_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg___boxed(
    mut v_depth_5357_: *mut crate::leanh::LeanObject,
    mut v_keys_5358_: *mut crate::leanh::LeanObject,
    mut v_vals_5359_: *mut crate::leanh::LeanObject,
    mut v_i_5360_: *mut crate::leanh::LeanObject,
    mut v_entries_5361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5362_: usize = 0;
    let mut v_res_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5362_ = crate::leanh::lean_unbox_usize(v_depth_5357_);
    crate::leanh::lean_dec(v_depth_5357_);
    v_res_5363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_boxed_5362_, v_keys_5358_, v_vals_5359_, v_i_5360_, v_entries_5361_);
    crate::leanh::lean_dec_ref(v_vals_5359_);
    crate::leanh::lean_dec_ref(v_keys_5358_);
    return v_res_5363_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___boxed(
    mut v_x_5364_: *mut crate::leanh::LeanObject,
    mut v_x_5365_: *mut crate::leanh::LeanObject,
    mut v_x_5366_: *mut crate::leanh::LeanObject,
    mut v_x_5367_: *mut crate::leanh::LeanObject,
    mut v_x_5368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_20585__boxed_5369_: usize = 0;
    let mut v_x_20586__boxed_5370_: usize = 0;
    let mut v_res_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_20585__boxed_5369_ = crate::leanh::lean_unbox_usize(v_x_5365_);
    crate::leanh::lean_dec(v_x_5365_);
    v_x_20586__boxed_5370_ = crate::leanh::lean_unbox_usize(v_x_5366_);
    crate::leanh::lean_dec(v_x_5366_);
    v_res_5371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_5364_, v_x_20585__boxed_5369_, v_x_20586__boxed_5370_, v_x_5367_, v_x_5368_);
    return v_res_5371_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(
    mut v_x_5372_: *mut crate::leanh::LeanObject,
    mut v_x_5373_: *mut crate::leanh::LeanObject,
    mut v_x_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5375_: u64 = 0;
    let mut v___x_5376_: usize = 0;
    let mut v___x_5377_: usize = 0;
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5375_ = l_Lean_instHashableMVarId_hash(v_x_5373_);
    v___x_5376_ = lean_uint64_to_usize(v___x_5375_);
    v___x_5377_ = 1usize;
    v___x_5378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_5372_, v___x_5376_, v___x_5377_, v_x_5373_, v_x_5374_);
    return v___x_5378_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(
    mut v_mvarId_5379_: *mut crate::leanh::LeanObject,
    mut v_val_5380_: *mut crate::leanh::LeanObject,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5391_: u8 = 0;
    let mut v_depth_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5415_: u8 = 0;
    let mut v_isSharedCheck_5416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5383_ = lean_st_ref_take(v___y_5381_);
                v_mctx_5384_ = crate::leanh::lean_ctor_get(v___x_5383_, 0);
                v_cache_5385_ = crate::leanh::lean_ctor_get(v___x_5383_, 1);
                v_zetaDeltaFVarIds_5386_ = crate::leanh::lean_ctor_get(v___x_5383_, 2);
                v_postponed_5387_ = crate::leanh::lean_ctor_get(v___x_5383_, 3);
                v_diag_5388_ = crate::leanh::lean_ctor_get(v___x_5383_, 4);
                v_isSharedCheck_5416_ = (!crate::leanh::lean_is_exclusive(v___x_5383_)) as u8;
                if v_isSharedCheck_5416_ == 0 {
                    v___x_5390_ = v___x_5383_;
                    v_isShared_5391_ = v_isSharedCheck_5416_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5388_);
                    crate::leanh::lean_inc(v_postponed_5387_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5386_);
                    crate::leanh::lean_inc(v_cache_5385_);
                    crate::leanh::lean_inc(v_mctx_5384_);
                    crate::leanh::lean_dec(v___x_5383_);
                    v___x_5390_ = crate::leanh::lean_box(0);
                    v_isShared_5391_ = v_isSharedCheck_5416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5392_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 0);
                v_levelAssignDepth_5393_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 1);
                v_lmvarCounter_5394_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 2);
                v_mvarCounter_5395_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 3);
                v_lDecls_5396_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 4);
                v_decls_5397_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 5);
                v_userNames_5398_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 6);
                v_lAssignment_5399_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 7);
                v_eAssignment_5400_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 8);
                v_dAssignment_5401_ = crate::leanh::lean_ctor_get(v_mctx_5384_, 9);
                v_isSharedCheck_5415_ = (!crate::leanh::lean_is_exclusive(v_mctx_5384_)) as u8;
                if v_isSharedCheck_5415_ == 0 {
                    v___x_5403_ = v_mctx_5384_;
                    v_isShared_5404_ = v_isSharedCheck_5415_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_5401_);
                    crate::leanh::lean_inc(v_eAssignment_5400_);
                    crate::leanh::lean_inc(v_lAssignment_5399_);
                    crate::leanh::lean_inc(v_userNames_5398_);
                    crate::leanh::lean_inc(v_decls_5397_);
                    crate::leanh::lean_inc(v_lDecls_5396_);
                    crate::leanh::lean_inc(v_mvarCounter_5395_);
                    crate::leanh::lean_inc(v_lmvarCounter_5394_);
                    crate::leanh::lean_inc(v_levelAssignDepth_5393_);
                    crate::leanh::lean_inc(v_depth_5392_);
                    crate::leanh::lean_dec(v_mctx_5384_);
                    v___x_5403_ = crate::leanh::lean_box(0);
                    v_isShared_5404_ = v_isSharedCheck_5415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5405_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_eAssignment_5400_, v_mvarId_5379_, v_val_5380_);
                if v_isShared_5404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5403_, 8, v___x_5405_);
                    v___x_5407_ = v___x_5403_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5414_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_depth_5392_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5414_,
                        1,
                        v_levelAssignDepth_5393_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 2, v_lmvarCounter_5394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 3, v_mvarCounter_5395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 4, v_lDecls_5396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 5, v_decls_5397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 6, v_userNames_5398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 7, v_lAssignment_5399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 8, v___x_5405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 9, v_dAssignment_5401_);
                    v___x_5407_ = v_reuseFailAlloc_5414_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5391_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5390_, 0, v___x_5407_);
                    v___x_5409_ = v___x_5390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5413_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5413_, 1, v_cache_5385_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5413_,
                        2,
                        v_zetaDeltaFVarIds_5386_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5413_, 3, v_postponed_5387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5413_, 4, v_diag_5388_);
                    v___x_5409_ = v_reuseFailAlloc_5413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5410_ = lean_st_ref_set(v___y_5381_, v___x_5409_);
                v___x_5411_ = crate::leanh::lean_box(0);
                v___x_5412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5412_, 0, v___x_5411_);
                return v___x_5412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(
    mut v_mvarId_5417_: *mut crate::leanh::LeanObject,
    mut v_val_5418_: *mut crate::leanh::LeanObject,
    mut v___y_5419_: *mut crate::leanh::LeanObject,
    mut v___y_5420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5421_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(
            v_mvarId_5417_,
            v_val_5418_,
            v___y_5419_,
        );
    crate::leanh::lean_dec(v___y_5419_);
    return v_res_5421_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(
    mut v_snd_5424_: *mut crate::leanh::LeanObject,
    mut v_hyp_5425_: *mut crate::leanh::LeanObject,
    mut v_a_5426_: *mut crate::leanh::LeanObject,
    mut v_fst_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
    mut v___y_5429_: *mut crate::leanh::LeanObject,
    mut v___y_5430_: *mut crate::leanh::LeanObject,
    mut v___y_5431_: *mut crate::leanh::LeanObject,
    mut v___y_5432_: *mut crate::leanh::LeanObject,
    mut v___y_5433_: *mut crate::leanh::LeanObject,
    mut v___y_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5459_: u8 = 0;
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5463_: u8 = 0;
    let mut v_a_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_snd_5424_);
                v___x_5437_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
                    v_snd_5424_,
                    v_hyp_5425_,
                    v___y_5432_,
                    v___y_5433_,
                    v___y_5434_,
                    v___y_5435_,
                );
                if crate::leanh::lean_obj_tag(v___x_5437_) == 0 {
                    v_a_5438_ = crate::leanh::lean_ctor_get(v___x_5437_, 0);
                    crate::leanh::lean_inc(v_a_5438_);
                    crate::leanh::lean_dec_ref_known(v___x_5437_, 1);
                    v___x_5439_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0;
                    v___x_5440_ = lean_st_mk_ref(v___x_5439_);
                    v_focusHyp_5441_ = crate::leanh::lean_ctor_get(v_a_5438_, 0);
                    v_restHyps_5442_ = crate::leanh::lean_ctor_get(v_a_5438_, 1);
                    v_u_5443_ = crate::leanh::lean_ctor_get(v_snd_5424_, 0);
                    v_00_u03c3s_5444_ = crate::leanh::lean_ctor_get(v_snd_5424_, 1);
                    v_target_5445_ = crate::leanh::lean_ctor_get(v_snd_5424_, 3);
                    crate::leanh::lean_inc_ref(v_restHyps_5442_);
                    crate::leanh::lean_inc_ref(v_target_5445_);
                    crate::leanh::lean_inc_ref_n(v_00_u03c3s_5444_, 2);
                    crate::leanh::lean_inc(v___x_5440_);
                    crate::leanh::lean_inc_n(v_u_5443_, 2);
                    v___x_5446_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed
                            as *mut core::ffi::c_void,
                        11,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___x_5446_, 0, v_u_5443_);
                    crate::leanh::lean_closure_set(v___x_5446_, 1, v___x_5440_);
                    crate::leanh::lean_closure_set(v___x_5446_, 2, v_00_u03c3s_5444_);
                    crate::leanh::lean_closure_set(v___x_5446_, 3, v_target_5445_);
                    crate::leanh::lean_closure_set(v___x_5446_, 4, v_restHyps_5442_);
                    crate::leanh::lean_inc_ref(v_focusHyp_5441_);
                    v___x_5447_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(
                        v_u_5443_,
                        v_00_u03c3s_5444_,
                        v_focusHyp_5441_,
                        v_a_5426_,
                        v___x_5446_,
                        v___y_5432_,
                        v___y_5433_,
                        v___y_5434_,
                        v___y_5435_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5447_) == 0 {
                        v_a_5448_ = crate::leanh::lean_ctor_get(v___x_5447_, 0);
                        crate::leanh::lean_inc(v_a_5448_);
                        crate::leanh::lean_dec_ref_known(v___x_5447_, 1);
                        v_snd_5449_ = crate::leanh::lean_ctor_get(v_a_5448_, 1);
                        crate::leanh::lean_inc(v_snd_5449_);
                        crate::leanh::lean_dec(v_a_5448_);
                        v_snd_5450_ = crate::leanh::lean_ctor_get(v_snd_5449_, 1);
                        crate::leanh::lean_inc(v_snd_5450_);
                        crate::leanh::lean_dec(v_snd_5449_);
                        v___x_5451_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(
                            v_a_5438_,
                            v_snd_5424_,
                            v_snd_5450_,
                        );
                        v___x_5452_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_fst_5427_, v___x_5451_, v___y_5433_);
                        crate::leanh::lean_dec_ref(v___x_5452_);
                        v___x_5453_ = lean_st_ref_get(v___x_5440_);
                        crate::leanh::lean_dec(v___x_5440_);
                        v___x_5454_ = lean_array_to_list(v___x_5453_);
                        v___x_5455_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_5454_,
                            v___y_5429_,
                            v___y_5432_,
                            v___y_5433_,
                            v___y_5434_,
                            v___y_5435_,
                        );
                        return v___x_5455_;
                    } else {
                        crate::leanh::lean_dec(v___x_5440_);
                        crate::leanh::lean_dec(v_a_5438_);
                        crate::leanh::lean_dec(v_fst_5427_);
                        crate::leanh::lean_dec_ref(v_snd_5424_);
                        v_a_5456_ = crate::leanh::lean_ctor_get(v___x_5447_, 0);
                        v_isSharedCheck_5463_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5447_)) as u8;
                        if v_isSharedCheck_5463_ == 0 {
                            v___x_5458_ = v___x_5447_;
                            v_isShared_5459_ = v_isSharedCheck_5463_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5456_);
                            crate::leanh::lean_dec(v___x_5447_);
                            v___x_5458_ = crate::leanh::lean_box(0);
                            v_isShared_5459_ = v_isSharedCheck_5463_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_5427_);
                    crate::leanh::lean_dec(v_a_5426_);
                    crate::leanh::lean_dec_ref(v_snd_5424_);
                    v_a_5464_ = crate::leanh::lean_ctor_get(v___x_5437_, 0);
                    v_isSharedCheck_5471_ = (!crate::leanh::lean_is_exclusive(v___x_5437_)) as u8;
                    if v_isSharedCheck_5471_ == 0 {
                        v___x_5466_ = v___x_5437_;
                        v_isShared_5467_ = v_isSharedCheck_5471_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5464_);
                        crate::leanh::lean_dec(v___x_5437_);
                        v___x_5466_ = crate::leanh::lean_box(0);
                        v_isShared_5467_ = v_isSharedCheck_5471_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5459_ == 0 {
                    v___x_5461_ = v___x_5458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5456_);
                    v___x_5461_ = v_reuseFailAlloc_5462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5461_;
            }
            3 => {
                if v_isShared_5467_ == 0 {
                    v___x_5469_ = v___x_5466_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
                    v___x_5469_ = v_reuseFailAlloc_5470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(
    mut v_snd_5472_: *mut crate::leanh::LeanObject,
    mut v_hyp_5473_: *mut crate::leanh::LeanObject,
    mut v_a_5474_: *mut crate::leanh::LeanObject,
    mut v_fst_5475_: *mut crate::leanh::LeanObject,
    mut v___y_5476_: *mut crate::leanh::LeanObject,
    mut v___y_5477_: *mut crate::leanh::LeanObject,
    mut v___y_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
    mut v___y_5480_: *mut crate::leanh::LeanObject,
    mut v___y_5481_: *mut crate::leanh::LeanObject,
    mut v___y_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
    mut v___y_5484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5485_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(
        v_snd_5472_,
        v_hyp_5473_,
        v_a_5474_,
        v_fst_5475_,
        v___y_5476_,
        v___y_5477_,
        v___y_5478_,
        v___y_5479_,
        v___y_5480_,
        v___y_5481_,
        v___y_5482_,
        v___y_5483_,
    );
    crate::leanh::lean_dec(v___y_5483_);
    crate::leanh::lean_dec_ref(v___y_5482_);
    crate::leanh::lean_dec(v___y_5481_);
    crate::leanh::lean_dec_ref(v___y_5480_);
    crate::leanh::lean_dec(v___y_5479_);
    crate::leanh::lean_dec_ref(v___y_5478_);
    crate::leanh::lean_dec(v___y_5477_);
    crate::leanh::lean_dec_ref(v___y_5476_);
    return v_res_5485_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: f64 = 0.0;
    v___x_5486_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5487_ = lean_float_of_nat(v___x_5486_);
    return v___x_5487_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(
    mut v_cls_5491_: *mut crate::leanh::LeanObject,
    mut v_msg_5492_: *mut crate::leanh::LeanObject,
    mut v___y_5493_: *mut crate::leanh::LeanObject,
    mut v___y_5494_: *mut crate::leanh::LeanObject,
    mut v___y_5495_: *mut crate::leanh::LeanObject,
    mut v___y_5496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5503_: u8 = 0;
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5516_: u8 = 0;
    let mut v_tid_5517_: u64 = 0;
    let mut v_traces_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5521_: u8 = 0;
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: f64 = 0.0;
    let mut v___x_5524_: u8 = 0;
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut v_isSharedCheck_5543_: u8 = 0;
    let mut v_isSharedCheck_5544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5498_ = crate::leanh::lean_ctor_get(v___y_5495_, 5);
                v___x_5499_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
                v_a_5500_ = crate::leanh::lean_ctor_get(v___x_5499_, 0);
                v_isSharedCheck_5544_ = (!crate::leanh::lean_is_exclusive(v___x_5499_)) as u8;
                if v_isSharedCheck_5544_ == 0 {
                    v___x_5502_ = v___x_5499_;
                    v_isShared_5503_ = v_isSharedCheck_5544_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5500_);
                    crate::leanh::lean_dec(v___x_5499_);
                    v___x_5502_ = crate::leanh::lean_box(0);
                    v_isShared_5503_ = v_isSharedCheck_5544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5504_ = lean_st_ref_take(v___y_5496_);
                v_traceState_5505_ = crate::leanh::lean_ctor_get(v___x_5504_, 4);
                v_env_5506_ = crate::leanh::lean_ctor_get(v___x_5504_, 0);
                v_nextMacroScope_5507_ = crate::leanh::lean_ctor_get(v___x_5504_, 1);
                v_ngen_5508_ = crate::leanh::lean_ctor_get(v___x_5504_, 2);
                v_auxDeclNGen_5509_ = crate::leanh::lean_ctor_get(v___x_5504_, 3);
                v_cache_5510_ = crate::leanh::lean_ctor_get(v___x_5504_, 5);
                v_messages_5511_ = crate::leanh::lean_ctor_get(v___x_5504_, 6);
                v_infoState_5512_ = crate::leanh::lean_ctor_get(v___x_5504_, 7);
                v_snapshotTasks_5513_ = crate::leanh::lean_ctor_get(v___x_5504_, 8);
                v_isSharedCheck_5543_ = (!crate::leanh::lean_is_exclusive(v___x_5504_)) as u8;
                if v_isSharedCheck_5543_ == 0 {
                    v___x_5515_ = v___x_5504_;
                    v_isShared_5516_ = v_isSharedCheck_5543_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5513_);
                    crate::leanh::lean_inc(v_infoState_5512_);
                    crate::leanh::lean_inc(v_messages_5511_);
                    crate::leanh::lean_inc(v_cache_5510_);
                    crate::leanh::lean_inc(v_traceState_5505_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5509_);
                    crate::leanh::lean_inc(v_ngen_5508_);
                    crate::leanh::lean_inc(v_nextMacroScope_5507_);
                    crate::leanh::lean_inc(v_env_5506_);
                    crate::leanh::lean_dec(v___x_5504_);
                    v___x_5515_ = crate::leanh::lean_box(0);
                    v_isShared_5516_ = v_isSharedCheck_5543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5517_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5518_ = crate::leanh::lean_ctor_get(v_traceState_5505_, 0);
                v_isSharedCheck_5542_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5505_)) as u8;
                if v_isSharedCheck_5542_ == 0 {
                    v___x_5520_ = v_traceState_5505_;
                    v_isShared_5521_ = v_isSharedCheck_5542_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5518_);
                    crate::leanh::lean_dec(v_traceState_5505_);
                    v___x_5520_ = crate::leanh::lean_box(0);
                    v_isShared_5521_ = v_isSharedCheck_5542_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5522_ = crate::leanh::lean_box(0);
                v___x_5523_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0);
                v___x_5524_ = 0;
                v___x_5525_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1;
                v___x_5526_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_5526_, 0, v_cls_5491_);
                crate::leanh::lean_ctor_set(v___x_5526_, 1, v___x_5522_);
                crate::leanh::lean_ctor_set(v___x_5526_, 2, v___x_5525_);
                crate::leanh::lean_ctor_set_float(
                    v___x_5526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5523_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_5526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5523_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5524_,
                );
                v___x_5527_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2;
                v___x_5528_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5528_, 0, v___x_5526_);
                crate::leanh::lean_ctor_set(v___x_5528_, 1, v_a_5500_);
                crate::leanh::lean_ctor_set(v___x_5528_, 2, v___x_5527_);
                crate::leanh::lean_inc(v_ref_5498_);
                v___x_5529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5529_, 0, v_ref_5498_);
                crate::leanh::lean_ctor_set(v___x_5529_, 1, v___x_5528_);
                v___x_5530_ = l_Lean_PersistentArray_push___redArg(v_traces_5518_, v___x_5529_);
                if v_isShared_5521_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5520_, 0, v___x_5530_);
                    v___x_5532_ = v___x_5520_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5541_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5541_, 0, v___x_5530_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5541_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5517_,
                    );
                    v___x_5532_ = v_reuseFailAlloc_5541_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5516_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5515_, 4, v___x_5532_);
                    v___x_5534_ = v___x_5515_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5540_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_env_5506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 1, v_nextMacroScope_5507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 2, v_ngen_5508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 3, v_auxDeclNGen_5509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 4, v___x_5532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 5, v_cache_5510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 6, v_messages_5511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 7, v_infoState_5512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 8, v_snapshotTasks_5513_);
                    v___x_5534_ = v_reuseFailAlloc_5540_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5535_ = lean_st_ref_set(v___y_5496_, v___x_5534_);
                v___x_5536_ = crate::leanh::lean_box(0);
                if v_isShared_5503_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5502_, 0, v___x_5536_);
                    v___x_5538_ = v___x_5502_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5536_);
                    v___x_5538_ = v_reuseFailAlloc_5539_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(
    mut v_cls_5545_: *mut crate::leanh::LeanObject,
    mut v_msg_5546_: *mut crate::leanh::LeanObject,
    mut v___y_5547_: *mut crate::leanh::LeanObject,
    mut v___y_5548_: *mut crate::leanh::LeanObject,
    mut v___y_5549_: *mut crate::leanh::LeanObject,
    mut v___y_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5552_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_5545_, v_msg_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
    crate::leanh::lean_dec(v___y_5550_);
    crate::leanh::lean_dec_ref(v___y_5549_);
    crate::leanh::lean_dec(v___y_5548_);
    crate::leanh::lean_dec_ref(v___y_5547_);
    return v_res_5552_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(
    mut v_as_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
    mut v___y_5560_: *mut crate::leanh::LeanObject,
    mut v___y_5561_: *mut crate::leanh::LeanObject,
    mut v___y_5562_: *mut crate::leanh::LeanObject,
    mut v___y_5563_: *mut crate::leanh::LeanObject,
    mut v___y_5564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5569_: u8 = 0;
    let mut v_tail_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: u8 = 0;
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_5556_) == 0 {
                    v___x_5566_ = crate::leanh::lean_box(0);
                    v___x_5567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5567_, 0, v___x_5566_);
                    return v___x_5567_;
                } else {
                    v_options_5568_ = crate::leanh::lean_ctor_get(v___y_5563_, 2);
                    v_hasTrace_5569_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_5568_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5569_ == 0 {
                        v_tail_5570_ = crate::leanh::lean_ctor_get(v_as_5556_, 1);
                        crate::leanh::lean_inc(v_tail_5570_);
                        crate::leanh::lean_dec_ref_known(v_as_5556_, 2);
                        v_as_5556_ = v_tail_5570_;
                        state = 0;
                        continue;
                    } else {
                        v_head_5572_ = crate::leanh::lean_ctor_get(v_as_5556_, 0);
                        crate::leanh::lean_inc(v_head_5572_);
                        v_tail_5573_ = crate::leanh::lean_ctor_get(v_as_5556_, 1);
                        crate::leanh::lean_inc(v_tail_5573_);
                        crate::leanh::lean_dec_ref_known(v_as_5556_, 2);
                        v_fst_5574_ = crate::leanh::lean_ctor_get(v_head_5572_, 0);
                        crate::leanh::lean_inc_n(v_fst_5574_, 2);
                        v_snd_5575_ = crate::leanh::lean_ctor_get(v_head_5572_, 1);
                        crate::leanh::lean_inc(v_snd_5575_);
                        crate::leanh::lean_dec(v_head_5572_);
                        v_inheritedTraceOptions_5576_ =
                            crate::leanh::lean_ctor_get(v___y_5563_, 13);
                        v___x_5577_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1;
                        v___x_5578_ = l_Lean_Name_append(v___x_5577_, v_fst_5574_);
                        v___x_5579_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5576_,
                            v_options_5568_,
                            v___x_5578_,
                        );
                        crate::leanh::lean_dec(v___x_5578_);
                        if v___x_5579_ == 0 {
                            crate::leanh::lean_dec(v_snd_5575_);
                            crate::leanh::lean_dec(v_fst_5574_);
                            v_as_5556_ = v_tail_5573_;
                            state = 0;
                            continue;
                        } else {
                            v___x_5581_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5581_, 0, v_snd_5575_);
                            v___x_5582_ = l_Lean_MessageData_ofFormat(v___x_5581_);
                            v___x_5583_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_fst_5574_, v___x_5582_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
                            if crate::leanh::lean_obj_tag(v___x_5583_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5583_, 1);
                                v_as_5556_ = v_tail_5573_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_5573_);
                                return v___x_5583_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(
    mut v_as_5585_: *mut crate::leanh::LeanObject,
    mut v___y_5586_: *mut crate::leanh::LeanObject,
    mut v___y_5587_: *mut crate::leanh::LeanObject,
    mut v___y_5588_: *mut crate::leanh::LeanObject,
    mut v___y_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5595_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v_as_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
    crate::leanh::lean_dec(v___y_5593_);
    crate::leanh::lean_dec_ref(v___y_5592_);
    crate::leanh::lean_dec(v___y_5591_);
    crate::leanh::lean_dec_ref(v___y_5590_);
    crate::leanh::lean_dec(v___y_5589_);
    crate::leanh::lean_dec_ref(v___y_5588_);
    crate::leanh::lean_dec(v___y_5587_);
    crate::leanh::lean_dec_ref(v___y_5586_);
    return v_res_5595_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(
    mut v_x_5596_: *mut crate::leanh::LeanObject,
    mut v___y_5597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5596_) == 0 {
        let mut v_a_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5598_ = crate::leanh::lean_ctor_get(v_x_5596_, 0);
        crate::leanh::lean_inc(v_a_5598_);
        v___x_5599_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5599_, 0, v_a_5598_);
        crate::leanh::lean_ctor_set(v___x_5599_, 1, v___y_5597_);
        return v___x_5599_;
    } else {
        let mut v_a_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5600_ = crate::leanh::lean_ctor_get(v_x_5596_, 0);
        crate::leanh::lean_inc(v_a_5600_);
        v___x_5601_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5601_, 0, v_a_5600_);
        crate::leanh::lean_ctor_set(v___x_5601_, 1, v___y_5597_);
        return v___x_5601_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(
    mut v_x_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5604_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_5602_, v___y_5603_);
    crate::leanh::lean_dec_ref(v_x_5602_);
    return v_res_5604_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(
    mut v_env_5605_: *mut crate::leanh::LeanObject,
    mut v_stx_5606_: *mut crate::leanh::LeanObject,
    mut v___y_5607_: *mut crate::leanh::LeanObject,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5614_: u8 = 0;
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5619_: u8 = 0;
    let mut v_unused_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v_snd_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5630_: u8 = 0;
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_a_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5640_: u8 = 0;
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5648_: u8 = 0;
    let mut v_isSharedCheck_5649_: u8 = 0;
    let mut v_a_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5654_: u8 = 0;
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5609_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_5605_,
                    v_stx_5606_,
                    v___y_5607_,
                    v___y_5608_,
                );
                if crate::leanh::lean_obj_tag(v___x_5609_) == 0 {
                    v_a_5610_ = crate::leanh::lean_ctor_get(v___x_5609_, 0);
                    crate::leanh::lean_inc(v_a_5610_);
                    if crate::leanh::lean_obj_tag(v_a_5610_) == 0 {
                        v_a_5611_ = crate::leanh::lean_ctor_get(v___x_5609_, 1);
                        v_isSharedCheck_5619_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5609_)) as u8;
                        if v_isSharedCheck_5619_ == 0 {
                            v_unused_5620_ = crate::leanh::lean_ctor_get(v___x_5609_, 0);
                            crate::leanh::lean_dec(v_unused_5620_);
                            v___x_5613_ = v___x_5609_;
                            v_isShared_5614_ = v_isSharedCheck_5619_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5611_);
                            crate::leanh::lean_dec(v___x_5609_);
                            v___x_5613_ = crate::leanh::lean_box(0);
                            v_isShared_5614_ = v_isSharedCheck_5619_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_5621_ = crate::leanh::lean_ctor_get(v_a_5610_, 0);
                        v_isSharedCheck_5649_ = (!crate::leanh::lean_is_exclusive(v_a_5610_)) as u8;
                        if v_isSharedCheck_5649_ == 0 {
                            v___x_5623_ = v_a_5610_;
                            v_isShared_5624_ = v_isSharedCheck_5649_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5621_);
                            crate::leanh::lean_dec(v_a_5610_);
                            v___x_5623_ = crate::leanh::lean_box(0);
                            v_isShared_5624_ = v_isSharedCheck_5649_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_5650_ = crate::leanh::lean_ctor_get(v___x_5609_, 0);
                    v_a_5651_ = crate::leanh::lean_ctor_get(v___x_5609_, 1);
                    v_isSharedCheck_5658_ = (!crate::leanh::lean_is_exclusive(v___x_5609_)) as u8;
                    if v_isSharedCheck_5658_ == 0 {
                        v___x_5653_ = v___x_5609_;
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5651_);
                        crate::leanh::lean_inc(v_a_5650_);
                        crate::leanh::lean_dec(v___x_5609_);
                        v___x_5653_ = crate::leanh::lean_box(0);
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5615_ = crate::leanh::lean_box(0);
                if v_isShared_5614_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5613_, 0, v___x_5615_);
                    v___x_5617_ = v___x_5613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5618_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5618_, 1, v_a_5611_);
                    v___x_5617_ = v_reuseFailAlloc_5618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5617_;
            }
            3 => {
                v_snd_5625_ = crate::leanh::lean_ctor_get(v_val_5621_, 1);
                crate::leanh::lean_inc(v_snd_5625_);
                crate::leanh::lean_dec(v_val_5621_);
                if crate::leanh::lean_obj_tag(v_snd_5625_) == 0 {
                    crate::leanh::lean_del_object(v___x_5623_);
                    v_a_5626_ = crate::leanh::lean_ctor_get(v___x_5609_, 1);
                    crate::leanh::lean_inc(v_a_5626_);
                    crate::leanh::lean_dec_ref_known(v___x_5609_, 2);
                    v_a_5627_ = crate::leanh::lean_ctor_get(v_snd_5625_, 0);
                    v_isSharedCheck_5635_ = (!crate::leanh::lean_is_exclusive(v_snd_5625_)) as u8;
                    if v_isSharedCheck_5635_ == 0 {
                        v___x_5629_ = v_snd_5625_;
                        v_isShared_5630_ = v_isSharedCheck_5635_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5627_);
                        crate::leanh::lean_dec(v_snd_5625_);
                        v___x_5629_ = crate::leanh::lean_box(0);
                        v_isShared_5630_ = v_isSharedCheck_5635_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_5636_ = crate::leanh::lean_ctor_get(v___x_5609_, 1);
                    crate::leanh::lean_inc(v_a_5636_);
                    crate::leanh::lean_dec_ref_known(v___x_5609_, 2);
                    v_a_5637_ = crate::leanh::lean_ctor_get(v_snd_5625_, 0);
                    v_isSharedCheck_5648_ = (!crate::leanh::lean_is_exclusive(v_snd_5625_)) as u8;
                    if v_isSharedCheck_5648_ == 0 {
                        v___x_5639_ = v_snd_5625_;
                        v_isShared_5640_ = v_isSharedCheck_5648_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5637_);
                        crate::leanh::lean_dec(v_snd_5625_);
                        v___x_5639_ = crate::leanh::lean_box(0);
                        v_isShared_5640_ = v_isSharedCheck_5648_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5630_ == 0 {
                    v___x_5632_ = v___x_5629_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5627_);
                    v___x_5632_ = v_reuseFailAlloc_5634_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5633_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_5632_, v_a_5626_);
                crate::leanh::lean_dec_ref(v___x_5632_);
                return v___x_5633_;
            }
            6 => {
                if v_isShared_5624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5623_, 0, v_a_5637_);
                    v___x_5642_ = v___x_5623_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5647_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_a_5637_);
                    v___x_5642_ = v_reuseFailAlloc_5647_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5640_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5639_, 0, v___x_5642_);
                    v___x_5644_ = v___x_5639_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5646_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5642_);
                    v___x_5644_ = v_reuseFailAlloc_5646_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5645_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_5644_, v_a_5636_);
                crate::leanh::lean_dec_ref(v___x_5644_);
                return v___x_5645_;
            }
            9 => {
                if v_isShared_5654_ == 0 {
                    v___x_5656_ = v___x_5653_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5657_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5657_, 1, v_a_5651_);
                    v___x_5656_ = v_reuseFailAlloc_5657_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(
    mut v_env_5659_: *mut crate::leanh::LeanObject,
    mut v_stx_5660_: *mut crate::leanh::LeanObject,
    mut v___y_5661_: *mut crate::leanh::LeanObject,
    mut v___y_5662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5663_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(v_env_5659_, v_stx_5660_, v___y_5661_, v___y_5662_);
    crate::leanh::lean_dec_ref(v___y_5661_);
    return v_res_5663_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(
    mut v_msg_5664_: *mut crate::leanh::LeanObject,
    mut v___y_5665_: *mut crate::leanh::LeanObject,
    mut v___y_5666_: *mut crate::leanh::LeanObject,
    mut v___y_5667_: *mut crate::leanh::LeanObject,
    mut v___y_5668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5675_: u8 = 0;
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5670_ = crate::leanh::lean_ctor_get(v___y_5667_, 5);
                v___x_5671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_);
                v_a_5672_ = crate::leanh::lean_ctor_get(v___x_5671_, 0);
                v_isSharedCheck_5680_ = (!crate::leanh::lean_is_exclusive(v___x_5671_)) as u8;
                if v_isSharedCheck_5680_ == 0 {
                    v___x_5674_ = v___x_5671_;
                    v_isShared_5675_ = v_isSharedCheck_5680_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5672_);
                    crate::leanh::lean_dec(v___x_5671_);
                    v___x_5674_ = crate::leanh::lean_box(0);
                    v_isShared_5675_ = v_isSharedCheck_5680_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5670_);
                v___x_5676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5676_, 0, v_ref_5670_);
                crate::leanh::lean_ctor_set(v___x_5676_, 1, v_a_5672_);
                if v_isShared_5675_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5674_, 1);
                    crate::leanh::lean_ctor_set(v___x_5674_, 0, v___x_5676_);
                    v___x_5678_ = v___x_5674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5679_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5679_, 0, v___x_5676_);
                    v___x_5678_ = v_reuseFailAlloc_5679_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(
    mut v_msg_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5687_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
    crate::leanh::lean_dec(v___y_5685_);
    crate::leanh::lean_dec_ref(v___y_5684_);
    crate::leanh::lean_dec(v___y_5683_);
    crate::leanh::lean_dec_ref(v___y_5682_);
    return v_res_5687_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(
    mut v_ref_5688_: *mut crate::leanh::LeanObject,
    mut v_msg_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
    mut v___y_5693_: *mut crate::leanh::LeanObject,
    mut v___y_5694_: *mut crate::leanh::LeanObject,
    mut v___y_5695_: *mut crate::leanh::LeanObject,
    mut v___y_5696_: *mut crate::leanh::LeanObject,
    mut v___y_5697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5711_: u8 = 0;
    let mut v_cancelTk_x3f_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5713_: u8 = 0;
    let mut v_inheritedTraceOptions_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5699_ = crate::leanh::lean_ctor_get(v___y_5696_, 0);
    v_fileMap_5700_ = crate::leanh::lean_ctor_get(v___y_5696_, 1);
    v_options_5701_ = crate::leanh::lean_ctor_get(v___y_5696_, 2);
    v_currRecDepth_5702_ = crate::leanh::lean_ctor_get(v___y_5696_, 3);
    v_maxRecDepth_5703_ = crate::leanh::lean_ctor_get(v___y_5696_, 4);
    v_ref_5704_ = crate::leanh::lean_ctor_get(v___y_5696_, 5);
    v_currNamespace_5705_ = crate::leanh::lean_ctor_get(v___y_5696_, 6);
    v_openDecls_5706_ = crate::leanh::lean_ctor_get(v___y_5696_, 7);
    v_initHeartbeats_5707_ = crate::leanh::lean_ctor_get(v___y_5696_, 8);
    v_maxHeartbeats_5708_ = crate::leanh::lean_ctor_get(v___y_5696_, 9);
    v_quotContext_5709_ = crate::leanh::lean_ctor_get(v___y_5696_, 10);
    v_currMacroScope_5710_ = crate::leanh::lean_ctor_get(v___y_5696_, 11);
    v_diag_5711_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5696_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5712_ = crate::leanh::lean_ctor_get(v___y_5696_, 12);
    v_suppressElabErrors_5713_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5696_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5714_ = crate::leanh::lean_ctor_get(v___y_5696_, 13);
    v_ref_5715_ = l_Lean_replaceRef(v_ref_5688_, v_ref_5704_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5714_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5712_);
    crate::leanh::lean_inc(v_currMacroScope_5710_);
    crate::leanh::lean_inc(v_quotContext_5709_);
    crate::leanh::lean_inc(v_maxHeartbeats_5708_);
    crate::leanh::lean_inc(v_initHeartbeats_5707_);
    crate::leanh::lean_inc(v_openDecls_5706_);
    crate::leanh::lean_inc(v_currNamespace_5705_);
    crate::leanh::lean_inc(v_maxRecDepth_5703_);
    crate::leanh::lean_inc(v_currRecDepth_5702_);
    crate::leanh::lean_inc_ref(v_options_5701_);
    crate::leanh::lean_inc_ref(v_fileMap_5700_);
    crate::leanh::lean_inc_ref(v_fileName_5699_);
    v___x_5716_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5716_, 0, v_fileName_5699_);
    crate::leanh::lean_ctor_set(v___x_5716_, 1, v_fileMap_5700_);
    crate::leanh::lean_ctor_set(v___x_5716_, 2, v_options_5701_);
    crate::leanh::lean_ctor_set(v___x_5716_, 3, v_currRecDepth_5702_);
    crate::leanh::lean_ctor_set(v___x_5716_, 4, v_maxRecDepth_5703_);
    crate::leanh::lean_ctor_set(v___x_5716_, 5, v_ref_5715_);
    crate::leanh::lean_ctor_set(v___x_5716_, 6, v_currNamespace_5705_);
    crate::leanh::lean_ctor_set(v___x_5716_, 7, v_openDecls_5706_);
    crate::leanh::lean_ctor_set(v___x_5716_, 8, v_initHeartbeats_5707_);
    crate::leanh::lean_ctor_set(v___x_5716_, 9, v_maxHeartbeats_5708_);
    crate::leanh::lean_ctor_set(v___x_5716_, 10, v_quotContext_5709_);
    crate::leanh::lean_ctor_set(v___x_5716_, 11, v_currMacroScope_5710_);
    crate::leanh::lean_ctor_set(v___x_5716_, 12, v_cancelTk_x3f_5712_);
    crate::leanh::lean_ctor_set(v___x_5716_, 13, v_inheritedTraceOptions_5714_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5716_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5711_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5716_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5713_,
    );
    v___x_5717_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_5689_, v___y_5694_, v___y_5695_, v___x_5716_, v___y_5697_);
    crate::leanh::lean_dec_ref_known(v___x_5716_, 14);
    return v___x_5717_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(
    mut v_ref_5718_: *mut crate::leanh::LeanObject,
    mut v_msg_5719_: *mut crate::leanh::LeanObject,
    mut v___y_5720_: *mut crate::leanh::LeanObject,
    mut v___y_5721_: *mut crate::leanh::LeanObject,
    mut v___y_5722_: *mut crate::leanh::LeanObject,
    mut v___y_5723_: *mut crate::leanh::LeanObject,
    mut v___y_5724_: *mut crate::leanh::LeanObject,
    mut v___y_5725_: *mut crate::leanh::LeanObject,
    mut v___y_5726_: *mut crate::leanh::LeanObject,
    mut v___y_5727_: *mut crate::leanh::LeanObject,
    mut v___y_5728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5729_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_5718_, v_msg_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_);
    crate::leanh::lean_dec(v___y_5727_);
    crate::leanh::lean_dec_ref(v___y_5726_);
    crate::leanh::lean_dec(v___y_5725_);
    crate::leanh::lean_dec_ref(v___y_5724_);
    crate::leanh::lean_dec(v___y_5723_);
    crate::leanh::lean_dec_ref(v___y_5722_);
    crate::leanh::lean_dec(v___y_5721_);
    crate::leanh::lean_dec_ref(v___y_5720_);
    crate::leanh::lean_dec(v_ref_5718_);
    return v_res_5729_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(
    mut v_env_5730_: *mut crate::leanh::LeanObject,
    mut v_options_5731_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5732_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5733_: *mut crate::leanh::LeanObject,
    mut v_n_5734_: *mut crate::leanh::LeanObject,
    mut v___y_5735_: *mut crate::leanh::LeanObject,
    mut v___y_5736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5737_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_5730_,
        v_options_5731_,
        v_currNamespace_5732_,
        v_openDecls_5733_,
        v_n_5734_,
    );
    v___x_5738_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5738_, 0, v___x_5737_);
    crate::leanh::lean_ctor_set(v___x_5738_, 1, v___y_5736_);
    return v___x_5738_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(
    mut v_env_5739_: *mut crate::leanh::LeanObject,
    mut v_options_5740_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5741_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5742_: *mut crate::leanh::LeanObject,
    mut v_n_5743_: *mut crate::leanh::LeanObject,
    mut v___y_5744_: *mut crate::leanh::LeanObject,
    mut v___y_5745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5746_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(v_env_5739_, v_options_5740_, v_currNamespace_5741_, v_openDecls_5742_, v_n_5743_, v___y_5744_, v___y_5745_);
    crate::leanh::lean_dec_ref(v___y_5744_);
    crate::leanh::lean_dec_ref(v_options_5740_);
    return v_res_5746_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(
    mut v_currNamespace_5747_: *mut crate::leanh::LeanObject,
    mut v___y_5748_: *mut crate::leanh::LeanObject,
    mut v___y_5749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5750_, 0, v_currNamespace_5747_);
    crate::leanh::lean_ctor_set(v___x_5750_, 1, v___y_5749_);
    return v___x_5750_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(
    mut v_currNamespace_5751_: *mut crate::leanh::LeanObject,
    mut v___y_5752_: *mut crate::leanh::LeanObject,
    mut v___y_5753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5754_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(v_currNamespace_5751_, v___y_5752_, v___y_5753_);
    crate::leanh::lean_dec_ref(v___y_5752_);
    return v_res_5754_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5760_ = l_Lean_maxRecDepthErrorMessage;
    v___x_5761_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5761_, 0, v___x_5760_);
    return v___x_5761_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5762_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3);
    v___x_5763_ = l_Lean_MessageData_ofFormat(v___x_5762_);
    return v___x_5763_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5764_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4);
    v___x_5765_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2;
    v___x_5766_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5766_, 0, v___x_5765_);
    crate::leanh::lean_ctor_set(v___x_5766_, 1, v___x_5764_);
    return v___x_5766_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(
    mut v_ref_5767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5769_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5);
    v___x_5770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5770_, 0, v_ref_5767_);
    crate::leanh::lean_ctor_set(v___x_5770_, 1, v___x_5769_);
    v___x_5771_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5771_, 0, v___x_5770_);
    return v___x_5771_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(
    mut v_ref_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5774_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_5772_);
    return v_res_5774_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(
    mut v_env_5775_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5776_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5777_: *mut crate::leanh::LeanObject,
    mut v_n_5778_: *mut crate::leanh::LeanObject,
    mut v___y_5779_: *mut crate::leanh::LeanObject,
    mut v___y_5780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5781_ = l_Lean_ResolveName_resolveNamespace(
        v_env_5775_,
        v_currNamespace_5776_,
        v_openDecls_5777_,
        v_n_5778_,
    );
    v___x_5782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5782_, 0, v___x_5781_);
    crate::leanh::lean_ctor_set(v___x_5782_, 1, v___y_5780_);
    return v___x_5782_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(
    mut v_env_5783_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5784_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5785_: *mut crate::leanh::LeanObject,
    mut v_n_5786_: *mut crate::leanh::LeanObject,
    mut v___y_5787_: *mut crate::leanh::LeanObject,
    mut v___y_5788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5789_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(v_env_5783_, v_currNamespace_5784_, v_openDecls_5785_, v_n_5786_, v___y_5787_, v___y_5788_);
    crate::leanh::lean_dec_ref(v___y_5787_);
    return v_res_5789_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(
    mut v_keys_5790_: *mut crate::leanh::LeanObject,
    mut v_i_5791_: *mut crate::leanh::LeanObject,
    mut v_k_5792_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: u8 = 0;
    let mut v_k_x27_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: u8 = 0;
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5793_ = lean_array_get_size(v_keys_5790_);
                v___x_5794_ = lean_nat_dec_lt(v_i_5791_, v___x_5793_);
                if v___x_5794_ == 0 {
                    crate::leanh::lean_dec(v_i_5791_);
                    return v___x_5794_;
                } else {
                    v_k_x27_5795_ = lean_array_fget_borrowed(v_keys_5790_, v_i_5791_);
                    v___x_5796_ = l_Lean_instBEqExtraModUse_beq(v_k_5792_, v_k_x27_5795_);
                    if v___x_5796_ == 0 {
                        v___x_5797_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5798_ = lean_nat_add(v_i_5791_, v___x_5797_);
                        crate::leanh::lean_dec(v_i_5791_);
                        v_i_5791_ = v___x_5798_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_5791_);
                        return v___x_5796_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(
    mut v_keys_5800_: *mut crate::leanh::LeanObject,
    mut v_i_5801_: *mut crate::leanh::LeanObject,
    mut v_k_5802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5803_: u8 = 0;
    let mut v_r_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5803_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_5800_, v_i_5801_, v_k_5802_);
    crate::leanh::lean_dec_ref(v_k_5802_);
    crate::leanh::lean_dec_ref(v_keys_5800_);
    v_r_5804_ = crate::leanh::lean_box((v_res_5803_) as usize);
    return v_r_5804_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(
    mut v_x_5805_: *mut crate::leanh::LeanObject,
    mut v_x_5806_: usize,
    mut v_x_5807_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: usize = 0;
    let mut v___x_5811_: usize = 0;
    let mut v___x_5812_: usize = 0;
    let mut v_j_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: u8 = 0;
    let mut v_node_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: usize = 0;
    let mut v___x_5820_: u8 = 0;
    let mut v_ks_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5805_) == 0 {
                    v_es_5808_ = crate::leanh::lean_ctor_get(v_x_5805_, 0);
                    v___x_5809_ = crate::leanh::lean_box(2);
                    v___x_5810_ = 5usize;
                    v___x_5811_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__1);
                    v___x_5812_ = lean_usize_land(v_x_5806_, v___x_5811_);
                    v_j_5813_ = lean_usize_to_nat(v___x_5812_);
                    v___x_5814_ = lean_array_get_borrowed(v___x_5809_, v_es_5808_, v_j_5813_);
                    crate::leanh::lean_dec(v_j_5813_);
                    match crate::leanh::lean_obj_tag(v___x_5814_) {
                        0 => {
                            v_key_5815_ = crate::leanh::lean_ctor_get(v___x_5814_, 0);
                            v___x_5816_ = l_Lean_instBEqExtraModUse_beq(v_x_5807_, v_key_5815_);
                            return v___x_5816_;
                        }
                        1 => {
                            v_node_5817_ = crate::leanh::lean_ctor_get(v___x_5814_, 0);
                            v___x_5818_ = lean_usize_shift_right(v_x_5806_, v___x_5810_);
                            v_x_5805_ = v_node_5817_;
                            v_x_5806_ = v___x_5818_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5820_ = 0;
                            return v___x_5820_;
                        }
                    }
                } else {
                    v_ks_5821_ = crate::leanh::lean_ctor_get(v_x_5805_, 0);
                    v___x_5822_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5823_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_ks_5821_, v___x_5822_, v_x_5807_);
                    return v___x_5823_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(
    mut v_x_5824_: *mut crate::leanh::LeanObject,
    mut v_x_5825_: *mut crate::leanh::LeanObject,
    mut v_x_5826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21359__boxed_5827_: usize = 0;
    let mut v_res_5828_: u8 = 0;
    let mut v_r_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21359__boxed_5827_ = crate::leanh::lean_unbox_usize(v_x_5825_);
    crate::leanh::lean_dec(v_x_5825_);
    v_res_5828_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_5824_, v_x_21359__boxed_5827_, v_x_5826_);
    crate::leanh::lean_dec_ref(v_x_5826_);
    crate::leanh::lean_dec_ref(v_x_5824_);
    v_r_5829_ = crate::leanh::lean_box((v_res_5828_) as usize);
    return v_r_5829_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(
    mut v_x_5830_: *mut crate::leanh::LeanObject,
    mut v_x_5831_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5832_: u64 = 0;
    let mut v___x_5833_: usize = 0;
    let mut v___x_5834_: u8 = 0;
    v___x_5832_ = l_Lean_instHashableExtraModUse_hash(v_x_5831_);
    v___x_5833_ = lean_uint64_to_usize(v___x_5832_);
    v___x_5834_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_5830_, v___x_5833_, v_x_5831_);
    return v___x_5834_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(
    mut v_x_5835_: *mut crate::leanh::LeanObject,
    mut v_x_5836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5837_: u8 = 0;
    let mut v_r_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5837_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_5835_, v_x_5836_);
    crate::leanh::lean_dec_ref(v_x_5836_);
    crate::leanh::lean_dec_ref(v_x_5835_);
    v_r_5838_ = crate::leanh::lean_box((v_res_5837_) as usize);
    return v_r_5838_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5841_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1;
    v___x_5842_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0;
    v___x_5843_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5842_,
        v___x_5841_,
    );
    return v___x_5843_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5844_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5844_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5845_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3);
    v___x_5846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5846_, 0, v___x_5845_);
    return v___x_5846_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
    v___x_5848_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5848_, 0, v___x_5847_);
    crate::leanh::lean_ctor_set(v___x_5848_, 1, v___x_5847_);
    return v___x_5848_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5849_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
    v___x_5850_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5850_, 0, v___x_5849_);
    crate::leanh::lean_ctor_set(v___x_5850_, 1, v___x_5849_);
    crate::leanh::lean_ctor_set(v___x_5850_, 2, v___x_5849_);
    crate::leanh::lean_ctor_set(v___x_5850_, 3, v___x_5849_);
    crate::leanh::lean_ctor_set(v___x_5850_, 4, v___x_5849_);
    crate::leanh::lean_ctor_set(v___x_5850_, 5, v___x_5849_);
    return v___x_5850_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5855_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9;
    v___x_5856_ = l_Lean_stringToMessageData(v___x_5855_);
    return v___x_5856_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5858_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11;
    v___x_5859_ = l_Lean_stringToMessageData(v___x_5858_);
    return v___x_5859_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5860_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1;
    v___x_5861_ = l_Lean_stringToMessageData(v___x_5860_);
    return v___x_5861_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_5862_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8;
    v___x_5863_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1;
    v___x_5864_ = l_Lean_Name_append(v___x_5863_, v_cls_5862_);
    return v___x_5864_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5866_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15;
    v___x_5867_ = l_Lean_stringToMessageData(v___x_5866_);
    return v___x_5867_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5869_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17;
    v___x_5870_ = l_Lean_stringToMessageData(v___x_5869_);
    return v___x_5870_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(
    mut v_mod_5875_: *mut crate::leanh::LeanObject,
    mut v_isMeta_5876_: u8,
    mut v_hint_5877_: *mut crate::leanh::LeanObject,
    mut v___y_5878_: *mut crate::leanh::LeanObject,
    mut v___y_5879_: *mut crate::leanh::LeanObject,
    mut v___y_5880_: *mut crate::leanh::LeanObject,
    mut v___y_5881_: *mut crate::leanh::LeanObject,
    mut v___y_5882_: *mut crate::leanh::LeanObject,
    mut v___y_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5889_: u8 = 0;
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5912_: u8 = 0;
    let mut v_asyncMode_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5926_: u8 = 0;
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5934_: u8 = 0;
    let mut v_unused_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5937_: u8 = 0;
    let mut v_unused_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: u8 = 0;
    let mut v_options_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5942_: u8 = 0;
    let mut v_inheritedTraceOptions_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: u8 = 0;
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: u8 = 0;
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5887_ = lean_st_ref_get(v___y_5885_);
                v_env_5888_ = crate::leanh::lean_ctor_get(v___x_5887_, 0);
                crate::leanh::lean_inc_ref(v_env_5888_);
                crate::leanh::lean_dec(v___x_5887_);
                v_isExporting_5889_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_5888_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_5888_);
                v___x_5890_ = lean_st_ref_get(v___y_5885_);
                v_env_5891_ = crate::leanh::lean_ctor_get(v___x_5890_, 0);
                crate::leanh::lean_inc_ref(v_env_5891_);
                crate::leanh::lean_dec(v___x_5890_);
                v___x_5892_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2);
                crate::leanh::lean_inc(v_mod_5875_);
                v_entry_5893_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_5893_, 0, v_mod_5875_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_5893_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_5889_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_5893_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_5876_,
                );
                v___x_5894_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_5895_ = crate::leanh::lean_box(1);
                v___x_5896_ = crate::leanh::lean_box(0);
                v___x_5939_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_5892_,
                    v___x_5894_,
                    v_env_5891_,
                    v___x_5895_,
                    v___x_5896_,
                );
                v___x_5940_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v___x_5939_, v_entry_5893_);
                crate::leanh::lean_dec(v___x_5939_);
                if v___x_5940_ == 0 {
                    v_options_5941_ = crate::leanh::lean_ctor_get(v___y_5884_, 2);
                    v_hasTrace_5942_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_5941_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5942_ == 0 {
                        crate::leanh::lean_dec(v_hint_5877_);
                        crate::leanh::lean_dec(v_mod_5875_);
                        v___y_5898_ = v___y_5883_;
                        v___y_5899_ = v___y_5885_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5943_ =
                            crate::leanh::lean_ctor_get(v___y_5884_, 13);
                        v_cls_5944_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8;
                        v___x_5964_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14);
                        v___x_5965_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5943_,
                            v_options_5941_,
                            v___x_5964_,
                        );
                        if v___x_5965_ == 0 {
                            crate::leanh::lean_dec(v_hint_5877_);
                            crate::leanh::lean_dec(v_mod_5875_);
                            v___y_5898_ = v___y_5883_;
                            v___y_5899_ = v___y_5885_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5966_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16);
                            if v_isExporting_5889_ == 0 {
                                v___x_5975_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21;
                                v___y_5968_ = v___x_5975_;
                                state = 8;
                                continue;
                            } else {
                                v___x_5976_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22;
                                v___y_5968_ = v___x_5976_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_5893_, 1);
                    crate::leanh::lean_dec(v_hint_5877_);
                    crate::leanh::lean_dec(v_mod_5875_);
                    v___x_5977_ = crate::leanh::lean_box(0);
                    v___x_5978_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5978_, 0, v___x_5977_);
                    return v___x_5978_;
                }
            }
            1 => {
                v___x_5900_ = lean_st_ref_take(v___y_5899_);
                v_toEnvExtension_5901_ = crate::leanh::lean_ctor_get(v___x_5894_, 0);
                v_env_5902_ = crate::leanh::lean_ctor_get(v___x_5900_, 0);
                v_nextMacroScope_5903_ = crate::leanh::lean_ctor_get(v___x_5900_, 1);
                v_ngen_5904_ = crate::leanh::lean_ctor_get(v___x_5900_, 2);
                v_auxDeclNGen_5905_ = crate::leanh::lean_ctor_get(v___x_5900_, 3);
                v_traceState_5906_ = crate::leanh::lean_ctor_get(v___x_5900_, 4);
                v_messages_5907_ = crate::leanh::lean_ctor_get(v___x_5900_, 6);
                v_infoState_5908_ = crate::leanh::lean_ctor_get(v___x_5900_, 7);
                v_snapshotTasks_5909_ = crate::leanh::lean_ctor_get(v___x_5900_, 8);
                v_isSharedCheck_5937_ = (!crate::leanh::lean_is_exclusive(v___x_5900_)) as u8;
                if v_isSharedCheck_5937_ == 0 {
                    v_unused_5938_ = crate::leanh::lean_ctor_get(v___x_5900_, 5);
                    crate::leanh::lean_dec(v_unused_5938_);
                    v___x_5911_ = v___x_5900_;
                    v_isShared_5912_ = v_isSharedCheck_5937_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5909_);
                    crate::leanh::lean_inc(v_infoState_5908_);
                    crate::leanh::lean_inc(v_messages_5907_);
                    crate::leanh::lean_inc(v_traceState_5906_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5905_);
                    crate::leanh::lean_inc(v_ngen_5904_);
                    crate::leanh::lean_inc(v_nextMacroScope_5903_);
                    crate::leanh::lean_inc(v_env_5902_);
                    crate::leanh::lean_dec(v___x_5900_);
                    v___x_5911_ = crate::leanh::lean_box(0);
                    v_isShared_5912_ = v_isSharedCheck_5937_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_5913_ = crate::leanh::lean_ctor_get(v_toEnvExtension_5901_, 2);
                v___x_5914_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_5894_,
                    v_env_5902_,
                    v_entry_5893_,
                    v_asyncMode_5913_,
                    v___x_5896_,
                );
                v___x_5915_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5);
                if v_isShared_5912_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5911_, 5, v___x_5915_);
                    crate::leanh::lean_ctor_set(v___x_5911_, 0, v___x_5914_);
                    v___x_5917_ = v___x_5911_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5936_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 0, v___x_5914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 1, v_nextMacroScope_5903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 2, v_ngen_5904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 3, v_auxDeclNGen_5905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 4, v_traceState_5906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 5, v___x_5915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 6, v_messages_5907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 7, v_infoState_5908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 8, v_snapshotTasks_5909_);
                    v___x_5917_ = v_reuseFailAlloc_5936_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5918_ = lean_st_ref_set(v___y_5899_, v___x_5917_);
                v___x_5919_ = lean_st_ref_take(v___y_5898_);
                v_mctx_5920_ = crate::leanh::lean_ctor_get(v___x_5919_, 0);
                v_zetaDeltaFVarIds_5921_ = crate::leanh::lean_ctor_get(v___x_5919_, 2);
                v_postponed_5922_ = crate::leanh::lean_ctor_get(v___x_5919_, 3);
                v_diag_5923_ = crate::leanh::lean_ctor_get(v___x_5919_, 4);
                v_isSharedCheck_5934_ = (!crate::leanh::lean_is_exclusive(v___x_5919_)) as u8;
                if v_isSharedCheck_5934_ == 0 {
                    v_unused_5935_ = crate::leanh::lean_ctor_get(v___x_5919_, 1);
                    crate::leanh::lean_dec(v_unused_5935_);
                    v___x_5925_ = v___x_5919_;
                    v_isShared_5926_ = v_isSharedCheck_5934_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5923_);
                    crate::leanh::lean_inc(v_postponed_5922_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5921_);
                    crate::leanh::lean_inc(v_mctx_5920_);
                    crate::leanh::lean_dec(v___x_5919_);
                    v___x_5925_ = crate::leanh::lean_box(0);
                    v_isShared_5926_ = v_isSharedCheck_5934_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5927_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6);
                if v_isShared_5926_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5925_, 1, v___x_5927_);
                    v___x_5929_ = v___x_5925_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5933_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_mctx_5920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 1, v___x_5927_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5933_,
                        2,
                        v_zetaDeltaFVarIds_5921_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 3, v_postponed_5922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 4, v_diag_5923_);
                    v___x_5929_ = v_reuseFailAlloc_5933_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5930_ = lean_st_ref_set(v___y_5898_, v___x_5929_);
                v___x_5931_ = crate::leanh::lean_box(0);
                v___x_5932_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5932_, 0, v___x_5931_);
                return v___x_5932_;
            }
            6 => {
                v___x_5948_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5948_, 0, v___y_5946_);
                crate::leanh::lean_ctor_set(v___x_5948_, 1, v___y_5947_);
                v___x_5949_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_5944_, v___x_5948_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_);
                if crate::leanh::lean_obj_tag(v___x_5949_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5949_, 1);
                    v___y_5898_ = v___y_5883_;
                    v___y_5899_ = v___y_5885_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_5893_, 1);
                    return v___x_5949_;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___y_5952_);
                v___x_5953_ = l_Lean_stringToMessageData(v___y_5952_);
                v___x_5954_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5954_, 0, v___y_5951_);
                crate::leanh::lean_ctor_set(v___x_5954_, 1, v___x_5953_);
                v___x_5955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10);
                v___x_5956_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5956_, 0, v___x_5954_);
                crate::leanh::lean_ctor_set(v___x_5956_, 1, v___x_5955_);
                v___x_5957_ = l_Lean_MessageData_ofName(v_mod_5875_);
                v___x_5958_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5958_, 0, v___x_5956_);
                crate::leanh::lean_ctor_set(v___x_5958_, 1, v___x_5957_);
                v___x_5959_ = l_Lean_Name_isAnonymous(v_hint_5877_);
                if v___x_5959_ == 0 {
                    v___x_5960_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12);
                    v___x_5961_ = l_Lean_MessageData_ofName(v_hint_5877_);
                    v___x_5962_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5962_, 0, v___x_5960_);
                    crate::leanh::lean_ctor_set(v___x_5962_, 1, v___x_5961_);
                    v___y_5946_ = v___x_5958_;
                    v___y_5947_ = v___x_5962_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_5877_);
                    v___x_5963_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13);
                    v___y_5946_ = v___x_5958_;
                    v___y_5947_ = v___x_5963_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___y_5968_);
                v___x_5969_ = l_Lean_stringToMessageData(v___y_5968_);
                v___x_5970_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5970_, 0, v___x_5966_);
                crate::leanh::lean_ctor_set(v___x_5970_, 1, v___x_5969_);
                v___x_5971_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18);
                v___x_5972_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5972_, 0, v___x_5970_);
                crate::leanh::lean_ctor_set(v___x_5972_, 1, v___x_5971_);
                if v_isMeta_5876_ == 0 {
                    v___x_5973_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19;
                    v___y_5951_ = v___x_5972_;
                    v___y_5952_ = v___x_5973_;
                    state = 7;
                    continue;
                } else {
                    v___x_5974_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20;
                    v___y_5951_ = v___x_5972_;
                    v___y_5952_ = v___x_5974_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(
    mut v_mod_5979_: *mut crate::leanh::LeanObject,
    mut v_isMeta_5980_: *mut crate::leanh::LeanObject,
    mut v_hint_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
    mut v___y_5983_: *mut crate::leanh::LeanObject,
    mut v___y_5984_: *mut crate::leanh::LeanObject,
    mut v___y_5985_: *mut crate::leanh::LeanObject,
    mut v___y_5986_: *mut crate::leanh::LeanObject,
    mut v___y_5987_: *mut crate::leanh::LeanObject,
    mut v___y_5988_: *mut crate::leanh::LeanObject,
    mut v___y_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_5991_: u8 = 0;
    let mut v_res_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5991_ = (crate::leanh::lean_unbox(v_isMeta_5980_) as u8);
    v_res_5992_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_mod_5979_, v_isMeta_boxed_5991_, v_hint_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
    crate::leanh::lean_dec(v___y_5989_);
    crate::leanh::lean_dec_ref(v___y_5988_);
    crate::leanh::lean_dec(v___y_5987_);
    crate::leanh::lean_dec_ref(v___y_5986_);
    crate::leanh::lean_dec(v___y_5985_);
    crate::leanh::lean_dec_ref(v___y_5984_);
    crate::leanh::lean_dec(v___y_5983_);
    crate::leanh::lean_dec_ref(v___y_5982_);
    return v_res_5992_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(
    mut v_a_5993_: *mut crate::leanh::LeanObject,
    mut v_x_5994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: u8 = 0;
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5994_) == 0 {
                    v___x_5995_ = crate::leanh::lean_box(0);
                    return v___x_5995_;
                } else {
                    v_key_5996_ = crate::leanh::lean_ctor_get(v_x_5994_, 0);
                    v_value_5997_ = crate::leanh::lean_ctor_get(v_x_5994_, 1);
                    v_tail_5998_ = crate::leanh::lean_ctor_get(v_x_5994_, 2);
                    v___x_5999_ = lean_name_eq(v_key_5996_, v_a_5993_);
                    if v___x_5999_ == 0 {
                        v_x_5994_ = v_tail_5998_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5997_);
                        v___x_6001_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6001_, 0, v_value_5997_);
                        return v___x_6001_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(
    mut v_a_6002_: *mut crate::leanh::LeanObject,
    mut v_x_6003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6004_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_6002_, v_x_6003_);
    crate::leanh::lean_dec(v_x_6003_);
    crate::leanh::lean_dec(v_a_6002_);
    return v_res_6004_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0()
-> u64 {
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: u64 = 0;
    v___x_6005_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_6006_ = lean_uint64_of_nat(v___x_6005_);
    return v___x_6006_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(
    mut v_m_6007_: *mut crate::leanh::LeanObject,
    mut v_a_6008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6012_: u64 = 0;
    let mut v___x_6013_: u64 = 0;
    let mut v___x_6014_: u64 = 0;
    let mut v_fold_6015_: u64 = 0;
    let mut v___x_6016_: u64 = 0;
    let mut v___x_6017_: u64 = 0;
    let mut v___x_6018_: u64 = 0;
    let mut v___x_6019_: usize = 0;
    let mut v___x_6020_: usize = 0;
    let mut v___x_6021_: usize = 0;
    let mut v___x_6022_: usize = 0;
    let mut v___x_6023_: usize = 0;
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: u64 = 0;
    let mut v_hash_6027_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_6009_ = crate::leanh::lean_ctor_get(v_m_6007_, 1);
                v___x_6010_ = lean_array_get_size(v_buckets_6009_);
                if crate::leanh::lean_obj_tag(v_a_6008_) == 0 {
                    v___x_6026_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___closed__0);
                    v___y_6012_ = v___x_6026_;
                    state = 1;
                    continue;
                } else {
                    v_hash_6027_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_6008_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_6012_ = v_hash_6027_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6013_ = 32u64;
                v___x_6014_ = lean_uint64_shift_right(v___y_6012_, v___x_6013_);
                v_fold_6015_ = lean_uint64_xor(v___y_6012_, v___x_6014_);
                v___x_6016_ = 16u64;
                v___x_6017_ = lean_uint64_shift_right(v_fold_6015_, v___x_6016_);
                v___x_6018_ = lean_uint64_xor(v_fold_6015_, v___x_6017_);
                v___x_6019_ = lean_uint64_to_usize(v___x_6018_);
                v___x_6020_ = lean_usize_of_nat(v___x_6010_);
                v___x_6021_ = 1usize;
                v___x_6022_ = lean_usize_sub(v___x_6020_, v___x_6021_);
                v___x_6023_ = lean_usize_land(v___x_6019_, v___x_6022_);
                v___x_6024_ = lean_array_uget_borrowed(v_buckets_6009_, v___x_6023_);
                v___x_6025_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_6008_, v___x_6024_);
                return v___x_6025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_m_6028_: *mut crate::leanh::LeanObject,
    mut v_a_6029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_6028_, v_a_6029_);
    crate::leanh::lean_dec(v_a_6029_);
    crate::leanh::lean_dec_ref(v_m_6028_);
    return v_res_6030_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(
    mut v___x_6031_: *mut crate::leanh::LeanObject,
    mut v_declName_6032_: *mut crate::leanh::LeanObject,
    mut v_as_6033_: *mut crate::leanh::LeanObject,
    mut v_sz_6034_: usize,
    mut v_i_6035_: usize,
    mut v_b_6036_: *mut crate::leanh::LeanObject,
    mut v___y_6037_: *mut crate::leanh::LeanObject,
    mut v___y_6038_: *mut crate::leanh::LeanObject,
    mut v___y_6039_: *mut crate::leanh::LeanObject,
    mut v___y_6040_: *mut crate::leanh::LeanObject,
    mut v___y_6041_: *mut crate::leanh::LeanObject,
    mut v___y_6042_: *mut crate::leanh::LeanObject,
    mut v___y_6043_: *mut crate::leanh::LeanObject,
    mut v___y_6044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: u8 = 0;
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: usize = 0;
    let mut v___x_6059_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6046_ = lean_usize_dec_lt(v_i_6035_, v_sz_6034_);
                if v___x_6046_ == 0 {
                    crate::leanh::lean_dec(v_declName_6032_);
                    v___x_6047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6047_, 0, v_b_6036_);
                    return v___x_6047_;
                } else {
                    v___x_6048_ = l_Lean_Environment_header(v___x_6031_);
                    v_modules_6049_ = crate::leanh::lean_ctor_get(v___x_6048_, 3);
                    crate::leanh::lean_inc_ref(v_modules_6049_);
                    crate::leanh::lean_dec_ref(v___x_6048_);
                    v___x_6050_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_6051_ = lean_array_uget_borrowed(v_as_6033_, v_i_6035_);
                    v___x_6052_ = lean_array_get(v___x_6050_, v_modules_6049_, v_a_6051_);
                    crate::leanh::lean_dec_ref(v_modules_6049_);
                    v_toImport_6053_ = crate::leanh::lean_ctor_get(v___x_6052_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_6053_);
                    crate::leanh::lean_dec(v___x_6052_);
                    v_module_6054_ = crate::leanh::lean_ctor_get(v_toImport_6053_, 0);
                    crate::leanh::lean_inc(v_module_6054_);
                    crate::leanh::lean_dec_ref(v_toImport_6053_);
                    v___x_6055_ = 0;
                    crate::leanh::lean_inc(v_declName_6032_);
                    v___x_6056_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_6054_, v___x_6055_, v_declName_6032_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_);
                    if crate::leanh::lean_obj_tag(v___x_6056_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6056_, 1);
                        v___x_6057_ = crate::leanh::lean_box(0);
                        v___x_6058_ = 1usize;
                        v___x_6059_ = lean_usize_add(v_i_6035_, v___x_6058_);
                        v_i_6035_ = v___x_6059_;
                        v_b_6036_ = v___x_6057_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_6032_);
                        return v___x_6056_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(
    mut v___x_6061_: *mut crate::leanh::LeanObject,
    mut v_declName_6062_: *mut crate::leanh::LeanObject,
    mut v_as_6063_: *mut crate::leanh::LeanObject,
    mut v_sz_6064_: *mut crate::leanh::LeanObject,
    mut v_i_6065_: *mut crate::leanh::LeanObject,
    mut v_b_6066_: *mut crate::leanh::LeanObject,
    mut v___y_6067_: *mut crate::leanh::LeanObject,
    mut v___y_6068_: *mut crate::leanh::LeanObject,
    mut v___y_6069_: *mut crate::leanh::LeanObject,
    mut v___y_6070_: *mut crate::leanh::LeanObject,
    mut v___y_6071_: *mut crate::leanh::LeanObject,
    mut v___y_6072_: *mut crate::leanh::LeanObject,
    mut v___y_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6076_: usize = 0;
    let mut v_i_boxed_6077_: usize = 0;
    let mut v_res_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6076_ = crate::leanh::lean_unbox_usize(v_sz_6064_);
    crate::leanh::lean_dec(v_sz_6064_);
    v_i_boxed_6077_ = crate::leanh::lean_unbox_usize(v_i_6065_);
    crate::leanh::lean_dec(v_i_6065_);
    v_res_6078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v___x_6061_, v_declName_6062_, v_as_6063_, v_sz_boxed_6076_, v_i_boxed_6077_, v_b_6066_, v___y_6067_, v___y_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_);
    crate::leanh::lean_dec(v___y_6074_);
    crate::leanh::lean_dec_ref(v___y_6073_);
    crate::leanh::lean_dec(v___y_6072_);
    crate::leanh::lean_dec_ref(v___y_6071_);
    crate::leanh::lean_dec(v___y_6070_);
    crate::leanh::lean_dec_ref(v___y_6069_);
    crate::leanh::lean_dec(v___y_6068_);
    crate::leanh::lean_dec_ref(v___y_6067_);
    crate::leanh::lean_dec_ref(v_as_6063_);
    crate::leanh::lean_dec_ref(v___x_6061_);
    return v_res_6078_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6081_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1;
    v___x_6082_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0;
    v___x_6083_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6082_,
        v___x_6081_,
    );
    return v___x_6083_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(
    mut v_declName_6086_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6087_: u8,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
    mut v___y_6089_: *mut crate::leanh::LeanObject,
    mut v___y_6090_: *mut crate::leanh::LeanObject,
    mut v___y_6091_: *mut crate::leanh::LeanObject,
    mut v___y_6092_: *mut crate::leanh::LeanObject,
    mut v___y_6093_: *mut crate::leanh::LeanObject,
    mut v___y_6094_: *mut crate::leanh::LeanObject,
    mut v___y_6095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6105_: usize = 0;
    let mut v___x_6106_: usize = 0;
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6110_: u8 = 0;
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6114_: u8 = 0;
    let mut v_unused_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: u8 = 0;
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6127_: u8 = 0;
    let mut v_toImport_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: u8 = 0;
    let mut v___x_6139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6097_ = lean_st_ref_get(v___y_6095_);
                v_env_6101_ = crate::leanh::lean_ctor_get(v___x_6097_, 0);
                crate::leanh::lean_inc_ref(v_env_6101_);
                crate::leanh::lean_dec(v___x_6097_);
                v___x_6116_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6101_, v_declName_6086_);
                if crate::leanh::lean_obj_tag(v___x_6116_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_6101_);
                    crate::leanh::lean_dec(v_declName_6086_);
                    state = 1;
                    continue;
                } else {
                    v_val_6117_ = crate::leanh::lean_ctor_get(v___x_6116_, 0);
                    crate::leanh::lean_inc(v_val_6117_);
                    crate::leanh::lean_dec_ref_known(v___x_6116_, 1);
                    v___x_6118_ = l_Lean_Environment_header(v_env_6101_);
                    v_modules_6119_ = crate::leanh::lean_ctor_get(v___x_6118_, 3);
                    crate::leanh::lean_inc_ref(v_modules_6119_);
                    crate::leanh::lean_dec_ref(v___x_6118_);
                    v___x_6120_ = lean_array_get_size(v_modules_6119_);
                    v___x_6121_ = lean_nat_dec_lt(v_val_6117_, v___x_6120_);
                    if v___x_6121_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_6119_);
                        crate::leanh::lean_dec(v_val_6117_);
                        crate::leanh::lean_dec_ref(v_env_6101_);
                        crate::leanh::lean_dec(v_declName_6086_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6122_ = lean_st_ref_get(v___y_6095_);
                        v_env_6123_ = crate::leanh::lean_ctor_get(v___x_6122_, 0);
                        crate::leanh::lean_inc_ref(v_env_6123_);
                        crate::leanh::lean_dec(v___x_6122_);
                        v___x_6124_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2);
                        v___x_6125_ = lean_array_fget(v_modules_6119_, v_val_6117_);
                        crate::leanh::lean_dec(v_val_6117_);
                        crate::leanh::lean_dec_ref(v_modules_6119_);
                        if v_isMeta_6087_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_6123_);
                            v___y_6127_ = v_isMeta_6087_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_6086_);
                            v___x_6138_ = l_Lean_isMarkedMeta(v_env_6123_, v_declName_6086_);
                            if v___x_6138_ == 0 {
                                v___y_6127_ = v_isMeta_6087_;
                                state = 5;
                                continue;
                            } else {
                                v___x_6139_ = 0;
                                v___y_6127_ = v___x_6139_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6099_ = crate::leanh::lean_box(0);
                v___x_6100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6100_, 0, v___x_6099_);
                return v___x_6100_;
            }
            2 => {
                v___x_6104_ = crate::leanh::lean_box(0);
                v_sz_6105_ = lean_array_size(v___y_6103_);
                v___x_6106_ = 0usize;
                v___x_6107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v_env_6101_, v_declName_6086_, v___y_6103_, v_sz_6105_, v___x_6106_, v___x_6104_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_);
                crate::leanh::lean_dec_ref(v___y_6103_);
                crate::leanh::lean_dec_ref(v_env_6101_);
                if crate::leanh::lean_obj_tag(v___x_6107_) == 0 {
                    v_isSharedCheck_6114_ = (!crate::leanh::lean_is_exclusive(v___x_6107_)) as u8;
                    if v_isSharedCheck_6114_ == 0 {
                        v_unused_6115_ = crate::leanh::lean_ctor_get(v___x_6107_, 0);
                        crate::leanh::lean_dec(v_unused_6115_);
                        v___x_6109_ = v___x_6107_;
                        v_isShared_6110_ = v_isSharedCheck_6114_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6107_);
                        v___x_6109_ = crate::leanh::lean_box(0);
                        v_isShared_6110_ = v_isSharedCheck_6114_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_6107_;
                }
            }
            3 => {
                if v_isShared_6110_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6109_, 0, v___x_6104_);
                    v___x_6112_ = v___x_6109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6113_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6113_, 0, v___x_6104_);
                    v___x_6112_ = v_reuseFailAlloc_6113_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6112_;
            }
            5 => {
                v_toImport_6128_ = crate::leanh::lean_ctor_get(v___x_6125_, 0);
                crate::leanh::lean_inc_ref(v_toImport_6128_);
                crate::leanh::lean_dec(v___x_6125_);
                v_module_6129_ = crate::leanh::lean_ctor_get(v_toImport_6128_, 0);
                crate::leanh::lean_inc(v_module_6129_);
                crate::leanh::lean_dec_ref(v_toImport_6128_);
                crate::leanh::lean_inc(v_declName_6086_);
                v___x_6130_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_6129_, v___y_6127_, v_declName_6086_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_);
                if crate::leanh::lean_obj_tag(v___x_6130_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6130_, 1);
                    v___x_6131_ = l_Lean_indirectModUseExt;
                    v___x_6132_ = crate::leanh::lean_box(1);
                    v___x_6133_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_6101_);
                    v___x_6134_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_6124_,
                        v___x_6131_,
                        v_env_6101_,
                        v___x_6132_,
                        v___x_6133_,
                    );
                    v___x_6135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v___x_6134_, v_declName_6086_);
                    crate::leanh::lean_dec(v___x_6134_);
                    if crate::leanh::lean_obj_tag(v___x_6135_) == 0 {
                        v___x_6136_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3;
                        v___y_6103_ = v___x_6136_;
                        state = 2;
                        continue;
                    } else {
                        v_val_6137_ = crate::leanh::lean_ctor_get(v___x_6135_, 0);
                        crate::leanh::lean_inc(v_val_6137_);
                        crate::leanh::lean_dec_ref_known(v___x_6135_, 1);
                        v___y_6103_ = v_val_6137_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_6101_);
                    crate::leanh::lean_dec(v_declName_6086_);
                    return v___x_6130_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(
    mut v_declName_6140_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6141_: *mut crate::leanh::LeanObject,
    mut v___y_6142_: *mut crate::leanh::LeanObject,
    mut v___y_6143_: *mut crate::leanh::LeanObject,
    mut v___y_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
    mut v___y_6147_: *mut crate::leanh::LeanObject,
    mut v___y_6148_: *mut crate::leanh::LeanObject,
    mut v___y_6149_: *mut crate::leanh::LeanObject,
    mut v___y_6150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_6151_: u8 = 0;
    let mut v_res_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6151_ = (crate::leanh::lean_unbox(v_isMeta_6141_) as u8);
    v_res_6152_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_declName_6140_, v_isMeta_boxed_6151_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_);
    crate::leanh::lean_dec(v___y_6149_);
    crate::leanh::lean_dec_ref(v___y_6148_);
    crate::leanh::lean_dec(v___y_6147_);
    crate::leanh::lean_dec_ref(v___y_6146_);
    crate::leanh::lean_dec(v___y_6145_);
    crate::leanh::lean_dec_ref(v___y_6144_);
    crate::leanh::lean_dec(v___y_6143_);
    crate::leanh::lean_dec_ref(v___y_6142_);
    return v_res_6152_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(
    mut v_as_x27_6153_: *mut crate::leanh::LeanObject,
    mut v_b_6154_: *mut crate::leanh::LeanObject,
    mut v___y_6155_: *mut crate::leanh::LeanObject,
    mut v___y_6156_: *mut crate::leanh::LeanObject,
    mut v___y_6157_: *mut crate::leanh::LeanObject,
    mut v___y_6158_: *mut crate::leanh::LeanObject,
    mut v___y_6159_: *mut crate::leanh::LeanObject,
    mut v___y_6160_: *mut crate::leanh::LeanObject,
    mut v___y_6161_: *mut crate::leanh::LeanObject,
    mut v___y_6162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: u8 = 0;
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_6153_) == 0 {
                    v___x_6164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6164_, 0, v_b_6154_);
                    return v___x_6164_;
                } else {
                    v_head_6165_ = crate::leanh::lean_ctor_get(v_as_x27_6153_, 0);
                    v_tail_6166_ = crate::leanh::lean_ctor_get(v_as_x27_6153_, 1);
                    v___x_6167_ = 1;
                    crate::leanh::lean_inc(v_head_6165_);
                    v___x_6168_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_head_6165_, v___x_6167_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_);
                    if crate::leanh::lean_obj_tag(v___x_6168_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6168_, 1);
                        v___x_6169_ = crate::leanh::lean_box(0);
                        v_as_x27_6153_ = v_tail_6166_;
                        v_b_6154_ = v___x_6169_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6168_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(
    mut v_as_x27_6171_: *mut crate::leanh::LeanObject,
    mut v_b_6172_: *mut crate::leanh::LeanObject,
    mut v___y_6173_: *mut crate::leanh::LeanObject,
    mut v___y_6174_: *mut crate::leanh::LeanObject,
    mut v___y_6175_: *mut crate::leanh::LeanObject,
    mut v___y_6176_: *mut crate::leanh::LeanObject,
    mut v___y_6177_: *mut crate::leanh::LeanObject,
    mut v___y_6178_: *mut crate::leanh::LeanObject,
    mut v___y_6179_: *mut crate::leanh::LeanObject,
    mut v___y_6180_: *mut crate::leanh::LeanObject,
    mut v___y_6181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6182_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_6171_, v_b_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
    crate::leanh::lean_dec(v___y_6180_);
    crate::leanh::lean_dec_ref(v___y_6179_);
    crate::leanh::lean_dec(v___y_6178_);
    crate::leanh::lean_dec_ref(v___y_6177_);
    crate::leanh::lean_dec(v___y_6176_);
    crate::leanh::lean_dec_ref(v___y_6175_);
    crate::leanh::lean_dec(v___y_6174_);
    crate::leanh::lean_dec_ref(v___y_6173_);
    crate::leanh::lean_dec(v_as_x27_6171_);
    return v_res_6182_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(
    mut v_env_6183_: *mut crate::leanh::LeanObject,
    mut v_declName_6184_: *mut crate::leanh::LeanObject,
    mut v___y_6185_: *mut crate::leanh::LeanObject,
    mut v___y_6186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6187_: u8 = 0;
    let mut v_env_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: u8 = 0;
    let mut v___x_6191_: u8 = 0;
    v___x_6187_ = 0;
    v_env_6188_ = l_Lean_Environment_setExporting(v_env_6183_, v___x_6187_);
    crate::leanh::lean_inc(v_declName_6184_);
    v___x_6189_ = l_Lean_mkPrivateName(v_env_6188_, v_declName_6184_);
    v___x_6190_ = 1;
    crate::leanh::lean_inc_ref(v_env_6188_);
    v___x_6191_ = l_Lean_Environment_contains(v_env_6188_, v___x_6189_, v___x_6190_);
    if v___x_6191_ == 0 {
        let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6193_: u8 = 0;
        let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6192_ = l_Lean_privateToUserName(v_declName_6184_);
        v___x_6193_ = l_Lean_Environment_contains(v_env_6188_, v___x_6192_, v___x_6190_);
        v___x_6194_ = crate::leanh::lean_box((v___x_6193_) as usize);
        v___x_6195_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6195_, 0, v___x_6194_);
        crate::leanh::lean_ctor_set(v___x_6195_, 1, v___y_6186_);
        return v___x_6195_;
    } else {
        let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_6188_);
        crate::leanh::lean_dec(v_declName_6184_);
        v___x_6196_ = crate::leanh::lean_box((v___x_6191_) as usize);
        v___x_6197_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6197_, 0, v___x_6196_);
        crate::leanh::lean_ctor_set(v___x_6197_, 1, v___y_6186_);
        return v___x_6197_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(
    mut v_env_6198_: *mut crate::leanh::LeanObject,
    mut v_declName_6199_: *mut crate::leanh::LeanObject,
    mut v___y_6200_: *mut crate::leanh::LeanObject,
    mut v___y_6201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6202_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(v_env_6198_, v_declName_6199_, v___y_6200_, v___y_6201_);
    crate::leanh::lean_dec_ref(v___y_6200_);
    return v_res_6202_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(
    mut v_x_6204_: *mut crate::leanh::LeanObject,
    mut v___y_6205_: *mut crate::leanh::LeanObject,
    mut v___y_6206_: *mut crate::leanh::LeanObject,
    mut v___y_6207_: *mut crate::leanh::LeanObject,
    mut v___y_6208_: *mut crate::leanh::LeanObject,
    mut v___y_6209_: *mut crate::leanh::LeanObject,
    mut v___y_6210_: *mut crate::leanh::LeanObject,
    mut v___y_6211_: *mut crate::leanh::LeanObject,
    mut v___y_6212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6254_: u8 = 0;
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6262_: u8 = 0;
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6266_: u8 = 0;
    let mut v_unused_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6271_: u8 = 0;
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6275_: u8 = 0;
    let mut v_reuseFailAlloc_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6277_: u8 = 0;
    let mut v_unused_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6282_: u8 = 0;
    let mut v___x_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6286_: u8 = 0;
    let mut v_a_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: u8 = 0;
    let mut v___x_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6214_ = lean_st_ref_get(v___y_6212_);
                v_env_6215_ = crate::leanh::lean_ctor_get(v___x_6214_, 0);
                crate::leanh::lean_inc_ref_n(v_env_6215_, 4);
                crate::leanh::lean_dec(v___x_6214_);
                v_options_6216_ = crate::leanh::lean_ctor_get(v___y_6211_, 2);
                v_currRecDepth_6217_ = crate::leanh::lean_ctor_get(v___y_6211_, 3);
                v_maxRecDepth_6218_ = crate::leanh::lean_ctor_get(v___y_6211_, 4);
                v_ref_6219_ = crate::leanh::lean_ctor_get(v___y_6211_, 5);
                v_currNamespace_6220_ = crate::leanh::lean_ctor_get(v___y_6211_, 6);
                v_openDecls_6221_ = crate::leanh::lean_ctor_get(v___y_6211_, 7);
                v_quotContext_6222_ = crate::leanh::lean_ctor_get(v___y_6211_, 10);
                v_currMacroScope_6223_ = crate::leanh::lean_ctor_get(v___y_6211_, 11);
                v___x_6224_ = lean_st_ref_get(v___y_6212_);
                v_nextMacroScope_6225_ = crate::leanh::lean_ctor_get(v___x_6224_, 1);
                crate::leanh::lean_inc(v_nextMacroScope_6225_);
                crate::leanh::lean_dec(v___x_6224_);
                v___f_6226_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_6226_, 0, v_env_6215_);
                v___f_6227_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_6227_, 0, v_env_6215_);
                crate::leanh::lean_inc_n(v_openDecls_6221_, 2);
                crate::leanh::lean_inc_n(v_currNamespace_6220_, 3);
                v___f_6228_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                crate::leanh::lean_closure_set(v___f_6228_, 0, v_env_6215_);
                crate::leanh::lean_closure_set(v___f_6228_, 1, v_currNamespace_6220_);
                crate::leanh::lean_closure_set(v___f_6228_, 2, v_openDecls_6221_);
                v___f_6229_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                crate::leanh::lean_closure_set(v___f_6229_, 0, v_currNamespace_6220_);
                crate::leanh::lean_inc_ref(v_options_6216_);
                v___f_6230_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                crate::leanh::lean_closure_set(v___f_6230_, 0, v_env_6215_);
                crate::leanh::lean_closure_set(v___f_6230_, 1, v_options_6216_);
                crate::leanh::lean_closure_set(v___f_6230_, 2, v_currNamespace_6220_);
                crate::leanh::lean_closure_set(v___f_6230_, 3, v_openDecls_6221_);
                v_methods_6231_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v_methods_6231_, 0, v___f_6226_);
                crate::leanh::lean_ctor_set(v_methods_6231_, 1, v___f_6229_);
                crate::leanh::lean_ctor_set(v_methods_6231_, 2, v___f_6227_);
                crate::leanh::lean_ctor_set(v_methods_6231_, 3, v___f_6228_);
                crate::leanh::lean_ctor_set(v_methods_6231_, 4, v___f_6230_);
                crate::leanh::lean_inc(v_ref_6219_);
                crate::leanh::lean_inc(v_maxRecDepth_6218_);
                crate::leanh::lean_inc(v_currRecDepth_6217_);
                crate::leanh::lean_inc(v_currMacroScope_6223_);
                crate::leanh::lean_inc(v_quotContext_6222_);
                v___x_6232_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6232_, 0, v_methods_6231_);
                crate::leanh::lean_ctor_set(v___x_6232_, 1, v_quotContext_6222_);
                crate::leanh::lean_ctor_set(v___x_6232_, 2, v_currMacroScope_6223_);
                crate::leanh::lean_ctor_set(v___x_6232_, 3, v_currRecDepth_6217_);
                crate::leanh::lean_ctor_set(v___x_6232_, 4, v_maxRecDepth_6218_);
                crate::leanh::lean_ctor_set(v___x_6232_, 5, v_ref_6219_);
                v___x_6233_ = crate::leanh::lean_box(0);
                v___x_6234_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6234_, 0, v_nextMacroScope_6225_);
                crate::leanh::lean_ctor_set(v___x_6234_, 1, v___x_6233_);
                crate::leanh::lean_ctor_set(v___x_6234_, 2, v___x_6233_);
                v___x_6235_ = crate::leanh::lean_apply_2(v_x_6204_, v___x_6232_, v___x_6234_);
                if crate::leanh::lean_obj_tag(v___x_6235_) == 0 {
                    v_a_6236_ = crate::leanh::lean_ctor_get(v___x_6235_, 1);
                    crate::leanh::lean_inc(v_a_6236_);
                    v_a_6237_ = crate::leanh::lean_ctor_get(v___x_6235_, 0);
                    crate::leanh::lean_inc(v_a_6237_);
                    crate::leanh::lean_dec_ref_known(v___x_6235_, 2);
                    v_macroScope_6238_ = crate::leanh::lean_ctor_get(v_a_6236_, 0);
                    crate::leanh::lean_inc(v_macroScope_6238_);
                    v_traceMsgs_6239_ = crate::leanh::lean_ctor_get(v_a_6236_, 1);
                    crate::leanh::lean_inc(v_traceMsgs_6239_);
                    v_expandedMacroDecls_6240_ = crate::leanh::lean_ctor_get(v_a_6236_, 2);
                    crate::leanh::lean_inc(v_expandedMacroDecls_6240_);
                    crate::leanh::lean_dec(v_a_6236_);
                    v___x_6241_ = crate::leanh::lean_box(0);
                    v___x_6242_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_expandedMacroDecls_6240_, v___x_6241_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
                    crate::leanh::lean_dec(v_expandedMacroDecls_6240_);
                    if crate::leanh::lean_obj_tag(v___x_6242_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6242_, 1);
                        v___x_6243_ = lean_st_ref_take(v___y_6212_);
                        v_env_6244_ = crate::leanh::lean_ctor_get(v___x_6243_, 0);
                        v_ngen_6245_ = crate::leanh::lean_ctor_get(v___x_6243_, 2);
                        v_auxDeclNGen_6246_ = crate::leanh::lean_ctor_get(v___x_6243_, 3);
                        v_traceState_6247_ = crate::leanh::lean_ctor_get(v___x_6243_, 4);
                        v_cache_6248_ = crate::leanh::lean_ctor_get(v___x_6243_, 5);
                        v_messages_6249_ = crate::leanh::lean_ctor_get(v___x_6243_, 6);
                        v_infoState_6250_ = crate::leanh::lean_ctor_get(v___x_6243_, 7);
                        v_snapshotTasks_6251_ = crate::leanh::lean_ctor_get(v___x_6243_, 8);
                        v_isSharedCheck_6277_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6243_)) as u8;
                        if v_isSharedCheck_6277_ == 0 {
                            v_unused_6278_ = crate::leanh::lean_ctor_get(v___x_6243_, 1);
                            crate::leanh::lean_dec(v_unused_6278_);
                            v___x_6253_ = v___x_6243_;
                            v_isShared_6254_ = v_isSharedCheck_6277_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_6251_);
                            crate::leanh::lean_inc(v_infoState_6250_);
                            crate::leanh::lean_inc(v_messages_6249_);
                            crate::leanh::lean_inc(v_cache_6248_);
                            crate::leanh::lean_inc(v_traceState_6247_);
                            crate::leanh::lean_inc(v_auxDeclNGen_6246_);
                            crate::leanh::lean_inc(v_ngen_6245_);
                            crate::leanh::lean_inc(v_env_6244_);
                            crate::leanh::lean_dec(v___x_6243_);
                            v___x_6253_ = crate::leanh::lean_box(0);
                            v_isShared_6254_ = v_isSharedCheck_6277_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_traceMsgs_6239_);
                        crate::leanh::lean_dec(v_macroScope_6238_);
                        crate::leanh::lean_dec(v_a_6237_);
                        v_a_6279_ = crate::leanh::lean_ctor_get(v___x_6242_, 0);
                        v_isSharedCheck_6286_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6242_)) as u8;
                        if v_isSharedCheck_6286_ == 0 {
                            v___x_6281_ = v___x_6242_;
                            v_isShared_6282_ = v_isSharedCheck_6286_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6279_);
                            crate::leanh::lean_dec(v___x_6242_);
                            v___x_6281_ = crate::leanh::lean_box(0);
                            v_isShared_6282_ = v_isSharedCheck_6286_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_6287_ = crate::leanh::lean_ctor_get(v___x_6235_, 0);
                    crate::leanh::lean_inc(v_a_6287_);
                    crate::leanh::lean_dec_ref_known(v___x_6235_, 2);
                    if crate::leanh::lean_obj_tag(v_a_6287_) == 0 {
                        v_a_6288_ = crate::leanh::lean_ctor_get(v_a_6287_, 0);
                        crate::leanh::lean_inc(v_a_6288_);
                        v_a_6289_ = crate::leanh::lean_ctor_get(v_a_6287_, 1);
                        crate::leanh::lean_inc_ref(v_a_6289_);
                        crate::leanh::lean_dec_ref_known(v_a_6287_, 2);
                        v___x_6290_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0;
                        v___x_6291_ = lean_string_dec_eq(v_a_6289_, v___x_6290_);
                        if v___x_6291_ == 0 {
                            v___x_6292_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6292_, 0, v_a_6289_);
                            v___x_6293_ = l_Lean_MessageData_ofFormat(v___x_6292_);
                            v___x_6294_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_a_6288_, v___x_6293_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
                            crate::leanh::lean_dec(v_a_6288_);
                            return v___x_6294_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_6289_);
                            v___x_6295_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_a_6288_);
                            return v___x_6295_;
                        }
                    } else {
                        v___x_6296_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
                        return v___x_6296_;
                    }
                }
            }
            1 => {
                if v_isShared_6254_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6253_, 1, v_macroScope_6238_);
                    v___x_6256_ = v___x_6253_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6276_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_env_6244_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 1, v_macroScope_6238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 2, v_ngen_6245_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 3, v_auxDeclNGen_6246_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 4, v_traceState_6247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 5, v_cache_6248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 6, v_messages_6249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 7, v_infoState_6250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 8, v_snapshotTasks_6251_);
                    v___x_6256_ = v_reuseFailAlloc_6276_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6257_ = lean_st_ref_set(v___y_6212_, v___x_6256_);
                v___x_6258_ = l_List_reverse___redArg(v_traceMsgs_6239_);
                v___x_6259_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v___x_6258_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
                if crate::leanh::lean_obj_tag(v___x_6259_) == 0 {
                    v_isSharedCheck_6266_ = (!crate::leanh::lean_is_exclusive(v___x_6259_)) as u8;
                    if v_isSharedCheck_6266_ == 0 {
                        v_unused_6267_ = crate::leanh::lean_ctor_get(v___x_6259_, 0);
                        crate::leanh::lean_dec(v_unused_6267_);
                        v___x_6261_ = v___x_6259_;
                        v_isShared_6262_ = v_isSharedCheck_6266_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6259_);
                        v___x_6261_ = crate::leanh::lean_box(0);
                        v_isShared_6262_ = v_isSharedCheck_6266_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6237_);
                    v_a_6268_ = crate::leanh::lean_ctor_get(v___x_6259_, 0);
                    v_isSharedCheck_6275_ = (!crate::leanh::lean_is_exclusive(v___x_6259_)) as u8;
                    if v_isSharedCheck_6275_ == 0 {
                        v___x_6270_ = v___x_6259_;
                        v_isShared_6271_ = v_isSharedCheck_6275_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6268_);
                        crate::leanh::lean_dec(v___x_6259_);
                        v___x_6270_ = crate::leanh::lean_box(0);
                        v_isShared_6271_ = v_isSharedCheck_6275_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6261_, 0, v_a_6237_);
                    v___x_6264_ = v___x_6261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_a_6237_);
                    v___x_6264_ = v_reuseFailAlloc_6265_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6264_;
            }
            5 => {
                if v_isShared_6271_ == 0 {
                    v___x_6273_ = v___x_6270_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6274_, 0, v_a_6268_);
                    v___x_6273_ = v_reuseFailAlloc_6274_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6273_;
            }
            7 => {
                if v_isShared_6282_ == 0 {
                    v___x_6284_ = v___x_6281_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6285_, 0, v_a_6279_);
                    v___x_6284_ = v_reuseFailAlloc_6285_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___boxed(
    mut v_x_6297_: *mut crate::leanh::LeanObject,
    mut v___y_6298_: *mut crate::leanh::LeanObject,
    mut v___y_6299_: *mut crate::leanh::LeanObject,
    mut v___y_6300_: *mut crate::leanh::LeanObject,
    mut v___y_6301_: *mut crate::leanh::LeanObject,
    mut v___y_6302_: *mut crate::leanh::LeanObject,
    mut v___y_6303_: *mut crate::leanh::LeanObject,
    mut v___y_6304_: *mut crate::leanh::LeanObject,
    mut v___y_6305_: *mut crate::leanh::LeanObject,
    mut v___y_6306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6307_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(
            v_x_6297_,
            v___y_6298_,
            v___y_6299_,
            v___y_6300_,
            v___y_6301_,
            v___y_6302_,
            v___y_6303_,
            v___y_6304_,
            v___y_6305_,
        );
    crate::leanh::lean_dec(v___y_6305_);
    crate::leanh::lean_dec_ref(v___y_6304_);
    crate::leanh::lean_dec(v___y_6303_);
    crate::leanh::lean_dec_ref(v___y_6302_);
    crate::leanh::lean_dec(v___y_6301_);
    crate::leanh::lean_dec_ref(v___y_6300_);
    crate::leanh::lean_dec(v___y_6299_);
    crate::leanh::lean_dec_ref(v___y_6298_);
    return v_res_6307_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(
    mut v_x_6318_: *mut crate::leanh::LeanObject,
    mut v_a_6319_: *mut crate::leanh::LeanObject,
    mut v_a_6320_: *mut crate::leanh::LeanObject,
    mut v_a_6321_: *mut crate::leanh::LeanObject,
    mut v_a_6322_: *mut crate::leanh::LeanObject,
    mut v_a_6323_: *mut crate::leanh::LeanObject,
    mut v_a_6324_: *mut crate::leanh::LeanObject,
    mut v_a_6325_: *mut crate::leanh::LeanObject,
    mut v_a_6326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: u8 = 0;
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyp_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: u8 = 0;
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pat_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6350_: u8 = 0;
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6354_: u8 = 0;
    let mut v_a_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6358_: u8 = 0;
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6328_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2;
                crate::leanh::lean_inc(v_x_6318_);
                v___x_6329_ = l_Lean_Syntax_isOfKind(v_x_6318_, v___x_6328_);
                if v___x_6329_ == 0 {
                    crate::leanh::lean_dec(v_x_6318_);
                    v___x_6330_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
                    return v___x_6330_;
                } else {
                    v___x_6331_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_hyp_6332_ = l_Lean_Syntax_getArg(v_x_6318_, v___x_6331_);
                    v___x_6333_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4;
                    crate::leanh::lean_inc(v_hyp_6332_);
                    v___x_6334_ = l_Lean_Syntax_isOfKind(v_hyp_6332_, v___x_6333_);
                    if v___x_6334_ == 0 {
                        crate::leanh::lean_dec(v_hyp_6332_);
                        crate::leanh::lean_dec(v_x_6318_);
                        v___x_6335_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
                        return v___x_6335_;
                    } else {
                        v___x_6336_ = crate::leanh::lean_unsigned_to_nat(3);
                        v_pat_6337_ = l_Lean_Syntax_getArg(v_x_6318_, v___x_6336_);
                        crate::leanh::lean_dec(v_x_6318_);
                        v___x_6338_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Parser_Tactic_MCasesPat_parse___boxed as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_6338_, 0, v_pat_6337_);
                        v___x_6339_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v___x_6338_, v_a_6319_, v_a_6320_, v_a_6321_, v_a_6322_, v_a_6323_, v_a_6324_, v_a_6325_, v_a_6326_);
                        if crate::leanh::lean_obj_tag(v___x_6339_) == 0 {
                            v_a_6340_ = crate::leanh::lean_ctor_get(v___x_6339_, 0);
                            crate::leanh::lean_inc(v_a_6340_);
                            crate::leanh::lean_dec_ref_known(v___x_6339_, 1);
                            v___x_6341_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                                v_a_6320_, v_a_6323_, v_a_6324_, v_a_6325_, v_a_6326_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6341_) == 0 {
                                v_a_6342_ = crate::leanh::lean_ctor_get(v___x_6341_, 0);
                                crate::leanh::lean_inc(v_a_6342_);
                                crate::leanh::lean_dec_ref_known(v___x_6341_, 1);
                                v_fst_6343_ = crate::leanh::lean_ctor_get(v_a_6342_, 0);
                                crate::leanh::lean_inc_n(v_fst_6343_, 2);
                                v_snd_6344_ = crate::leanh::lean_ctor_get(v_a_6342_, 1);
                                crate::leanh::lean_inc(v_snd_6344_);
                                crate::leanh::lean_dec(v_a_6342_);
                                v___f_6345_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    13,
                                    4,
                                );
                                crate::leanh::lean_closure_set(v___f_6345_, 0, v_snd_6344_);
                                crate::leanh::lean_closure_set(v___f_6345_, 1, v_hyp_6332_);
                                crate::leanh::lean_closure_set(v___f_6345_, 2, v_a_6340_);
                                crate::leanh::lean_closure_set(v___f_6345_, 3, v_fst_6343_);
                                v___x_6346_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_fst_6343_, v___f_6345_, v_a_6319_, v_a_6320_, v_a_6321_, v_a_6322_, v_a_6323_, v_a_6324_, v_a_6325_, v_a_6326_);
                                return v___x_6346_;
                            } else {
                                crate::leanh::lean_dec(v_a_6340_);
                                crate::leanh::lean_dec(v_hyp_6332_);
                                v_a_6347_ = crate::leanh::lean_ctor_get(v___x_6341_, 0);
                                v_isSharedCheck_6354_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6341_)) as u8;
                                if v_isSharedCheck_6354_ == 0 {
                                    v___x_6349_ = v___x_6341_;
                                    v_isShared_6350_ = v_isSharedCheck_6354_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6347_);
                                    crate::leanh::lean_dec(v___x_6341_);
                                    v___x_6349_ = crate::leanh::lean_box(0);
                                    v_isShared_6350_ = v_isSharedCheck_6354_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_hyp_6332_);
                            v_a_6355_ = crate::leanh::lean_ctor_get(v___x_6339_, 0);
                            v_isSharedCheck_6362_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6339_)) as u8;
                            if v_isSharedCheck_6362_ == 0 {
                                v___x_6357_ = v___x_6339_;
                                v_isShared_6358_ = v_isSharedCheck_6362_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6355_);
                                crate::leanh::lean_dec(v___x_6339_);
                                v___x_6357_ = crate::leanh::lean_box(0);
                                v_isShared_6358_ = v_isSharedCheck_6362_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6350_ == 0 {
                    v___x_6352_ = v___x_6349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6353_, 0, v_a_6347_);
                    v___x_6352_ = v_reuseFailAlloc_6353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6352_;
            }
            3 => {
                if v_isShared_6358_ == 0 {
                    v___x_6360_ = v___x_6357_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_a_6355_);
                    v___x_6360_ = v_reuseFailAlloc_6361_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(
    mut v_x_6363_: *mut crate::leanh::LeanObject,
    mut v_a_6364_: *mut crate::leanh::LeanObject,
    mut v_a_6365_: *mut crate::leanh::LeanObject,
    mut v_a_6366_: *mut crate::leanh::LeanObject,
    mut v_a_6367_: *mut crate::leanh::LeanObject,
    mut v_a_6368_: *mut crate::leanh::LeanObject,
    mut v_a_6369_: *mut crate::leanh::LeanObject,
    mut v_a_6370_: *mut crate::leanh::LeanObject,
    mut v_a_6371_: *mut crate::leanh::LeanObject,
    mut v_a_6372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6373_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(
        v_x_6363_, v_a_6364_, v_a_6365_, v_a_6366_, v_a_6367_, v_a_6368_, v_a_6369_, v_a_6370_,
        v_a_6371_,
    );
    crate::leanh::lean_dec(v_a_6371_);
    crate::leanh::lean_dec_ref(v_a_6370_);
    crate::leanh::lean_dec(v_a_6369_);
    crate::leanh::lean_dec_ref(v_a_6368_);
    crate::leanh::lean_dec(v_a_6367_);
    crate::leanh::lean_dec_ref(v_a_6366_);
    crate::leanh::lean_dec(v_a_6365_);
    crate::leanh::lean_dec_ref(v_a_6364_);
    return v_res_6373_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(
    mut v_00_u03b1_6374_: *mut crate::leanh::LeanObject,
    mut v_x_6375_: *mut crate::leanh::LeanObject,
    mut v___y_6376_: *mut crate::leanh::LeanObject,
    mut v___y_6377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6378_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_6375_, v___y_6377_);
    return v___x_6378_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(
    mut v_00_u03b1_6379_: *mut crate::leanh::LeanObject,
    mut v_x_6380_: *mut crate::leanh::LeanObject,
    mut v___y_6381_: *mut crate::leanh::LeanObject,
    mut v___y_6382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6383_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(v_00_u03b1_6379_, v_x_6380_, v___y_6381_, v___y_6382_);
    crate::leanh::lean_dec_ref(v___y_6381_);
    crate::leanh::lean_dec_ref(v_x_6380_);
    return v_res_6383_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(
    mut v_00_u03b1_6384_: *mut crate::leanh::LeanObject,
    mut v_ref_6385_: *mut crate::leanh::LeanObject,
    mut v___y_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
    mut v___y_6391_: *mut crate::leanh::LeanObject,
    mut v___y_6392_: *mut crate::leanh::LeanObject,
    mut v___y_6393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6395_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_6385_);
    return v___x_6395_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(
    mut v_00_u03b1_6396_: *mut crate::leanh::LeanObject,
    mut v_ref_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
    mut v___y_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
    mut v___y_6401_: *mut crate::leanh::LeanObject,
    mut v___y_6402_: *mut crate::leanh::LeanObject,
    mut v___y_6403_: *mut crate::leanh::LeanObject,
    mut v___y_6404_: *mut crate::leanh::LeanObject,
    mut v___y_6405_: *mut crate::leanh::LeanObject,
    mut v___y_6406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6407_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(v_00_u03b1_6396_, v_ref_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_, v___y_6403_, v___y_6404_, v___y_6405_);
    crate::leanh::lean_dec(v___y_6405_);
    crate::leanh::lean_dec_ref(v___y_6404_);
    crate::leanh::lean_dec(v___y_6403_);
    crate::leanh::lean_dec_ref(v___y_6402_);
    crate::leanh::lean_dec(v___y_6401_);
    crate::leanh::lean_dec_ref(v___y_6400_);
    crate::leanh::lean_dec(v___y_6399_);
    crate::leanh::lean_dec_ref(v___y_6398_);
    return v_res_6407_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(
    mut v_00_u03b1_6408_: *mut crate::leanh::LeanObject,
    mut v_x_6409_: *mut crate::leanh::LeanObject,
    mut v___y_6410_: *mut crate::leanh::LeanObject,
    mut v___y_6411_: *mut crate::leanh::LeanObject,
    mut v___y_6412_: *mut crate::leanh::LeanObject,
    mut v___y_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
    mut v___y_6415_: *mut crate::leanh::LeanObject,
    mut v___y_6416_: *mut crate::leanh::LeanObject,
    mut v___y_6417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6419_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(
            v_x_6409_,
            v___y_6410_,
            v___y_6411_,
            v___y_6412_,
            v___y_6413_,
            v___y_6414_,
            v___y_6415_,
            v___y_6416_,
            v___y_6417_,
        );
    return v___x_6419_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(
    mut v_00_u03b1_6420_: *mut crate::leanh::LeanObject,
    mut v_x_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
    mut v___y_6423_: *mut crate::leanh::LeanObject,
    mut v___y_6424_: *mut crate::leanh::LeanObject,
    mut v___y_6425_: *mut crate::leanh::LeanObject,
    mut v___y_6426_: *mut crate::leanh::LeanObject,
    mut v___y_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
    mut v___y_6429_: *mut crate::leanh::LeanObject,
    mut v___y_6430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6431_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(
        v_00_u03b1_6420_,
        v_x_6421_,
        v___y_6422_,
        v___y_6423_,
        v___y_6424_,
        v___y_6425_,
        v___y_6426_,
        v___y_6427_,
        v___y_6428_,
        v___y_6429_,
    );
    crate::leanh::lean_dec(v___y_6429_);
    crate::leanh::lean_dec_ref(v___y_6428_);
    crate::leanh::lean_dec(v___y_6427_);
    crate::leanh::lean_dec_ref(v___y_6426_);
    crate::leanh::lean_dec(v___y_6425_);
    crate::leanh::lean_dec_ref(v___y_6424_);
    crate::leanh::lean_dec(v___y_6423_);
    crate::leanh::lean_dec_ref(v___y_6422_);
    return v_res_6431_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(
    mut v_mvarId_6432_: *mut crate::leanh::LeanObject,
    mut v_val_6433_: *mut crate::leanh::LeanObject,
    mut v___y_6434_: *mut crate::leanh::LeanObject,
    mut v___y_6435_: *mut crate::leanh::LeanObject,
    mut v___y_6436_: *mut crate::leanh::LeanObject,
    mut v___y_6437_: *mut crate::leanh::LeanObject,
    mut v___y_6438_: *mut crate::leanh::LeanObject,
    mut v___y_6439_: *mut crate::leanh::LeanObject,
    mut v___y_6440_: *mut crate::leanh::LeanObject,
    mut v___y_6441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6443_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(
            v_mvarId_6432_,
            v_val_6433_,
            v___y_6439_,
        );
    return v___x_6443_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(
    mut v_mvarId_6444_: *mut crate::leanh::LeanObject,
    mut v_val_6445_: *mut crate::leanh::LeanObject,
    mut v___y_6446_: *mut crate::leanh::LeanObject,
    mut v___y_6447_: *mut crate::leanh::LeanObject,
    mut v___y_6448_: *mut crate::leanh::LeanObject,
    mut v___y_6449_: *mut crate::leanh::LeanObject,
    mut v___y_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
    mut v___y_6452_: *mut crate::leanh::LeanObject,
    mut v___y_6453_: *mut crate::leanh::LeanObject,
    mut v___y_6454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6455_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(
        v_mvarId_6444_,
        v_val_6445_,
        v___y_6446_,
        v___y_6447_,
        v___y_6448_,
        v___y_6449_,
        v___y_6450_,
        v___y_6451_,
        v___y_6452_,
        v___y_6453_,
    );
    crate::leanh::lean_dec(v___y_6453_);
    crate::leanh::lean_dec_ref(v___y_6452_);
    crate::leanh::lean_dec(v___y_6451_);
    crate::leanh::lean_dec_ref(v___y_6450_);
    crate::leanh::lean_dec(v___y_6449_);
    crate::leanh::lean_dec_ref(v___y_6448_);
    crate::leanh::lean_dec(v___y_6447_);
    crate::leanh::lean_dec_ref(v___y_6446_);
    return v_res_6455_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(
    mut v_cls_6456_: *mut crate::leanh::LeanObject,
    mut v_msg_6457_: *mut crate::leanh::LeanObject,
    mut v___y_6458_: *mut crate::leanh::LeanObject,
    mut v___y_6459_: *mut crate::leanh::LeanObject,
    mut v___y_6460_: *mut crate::leanh::LeanObject,
    mut v___y_6461_: *mut crate::leanh::LeanObject,
    mut v___y_6462_: *mut crate::leanh::LeanObject,
    mut v___y_6463_: *mut crate::leanh::LeanObject,
    mut v___y_6464_: *mut crate::leanh::LeanObject,
    mut v___y_6465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6467_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_6456_, v_msg_6457_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_);
    return v___x_6467_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(
    mut v_cls_6468_: *mut crate::leanh::LeanObject,
    mut v_msg_6469_: *mut crate::leanh::LeanObject,
    mut v___y_6470_: *mut crate::leanh::LeanObject,
    mut v___y_6471_: *mut crate::leanh::LeanObject,
    mut v___y_6472_: *mut crate::leanh::LeanObject,
    mut v___y_6473_: *mut crate::leanh::LeanObject,
    mut v___y_6474_: *mut crate::leanh::LeanObject,
    mut v___y_6475_: *mut crate::leanh::LeanObject,
    mut v___y_6476_: *mut crate::leanh::LeanObject,
    mut v___y_6477_: *mut crate::leanh::LeanObject,
    mut v___y_6478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6479_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(v_cls_6468_, v_msg_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_);
    crate::leanh::lean_dec(v___y_6477_);
    crate::leanh::lean_dec_ref(v___y_6476_);
    crate::leanh::lean_dec(v___y_6475_);
    crate::leanh::lean_dec_ref(v___y_6474_);
    crate::leanh::lean_dec(v___y_6473_);
    crate::leanh::lean_dec_ref(v___y_6472_);
    crate::leanh::lean_dec(v___y_6471_);
    crate::leanh::lean_dec_ref(v___y_6470_);
    return v_res_6479_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(
    mut v_as_6480_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6481_: *mut crate::leanh::LeanObject,
    mut v_b_6482_: *mut crate::leanh::LeanObject,
    mut v_a_6483_: *mut crate::leanh::LeanObject,
    mut v___y_6484_: *mut crate::leanh::LeanObject,
    mut v___y_6485_: *mut crate::leanh::LeanObject,
    mut v___y_6486_: *mut crate::leanh::LeanObject,
    mut v___y_6487_: *mut crate::leanh::LeanObject,
    mut v___y_6488_: *mut crate::leanh::LeanObject,
    mut v___y_6489_: *mut crate::leanh::LeanObject,
    mut v___y_6490_: *mut crate::leanh::LeanObject,
    mut v___y_6491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6493_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_6481_, v_b_6482_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
    return v___x_6493_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(
    mut v_as_6494_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6495_: *mut crate::leanh::LeanObject,
    mut v_b_6496_: *mut crate::leanh::LeanObject,
    mut v_a_6497_: *mut crate::leanh::LeanObject,
    mut v___y_6498_: *mut crate::leanh::LeanObject,
    mut v___y_6499_: *mut crate::leanh::LeanObject,
    mut v___y_6500_: *mut crate::leanh::LeanObject,
    mut v___y_6501_: *mut crate::leanh::LeanObject,
    mut v___y_6502_: *mut crate::leanh::LeanObject,
    mut v___y_6503_: *mut crate::leanh::LeanObject,
    mut v___y_6504_: *mut crate::leanh::LeanObject,
    mut v___y_6505_: *mut crate::leanh::LeanObject,
    mut v___y_6506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6507_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_as_6494_, v_as_x27_6495_, v_b_6496_, v_a_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_);
    crate::leanh::lean_dec(v___y_6505_);
    crate::leanh::lean_dec_ref(v___y_6504_);
    crate::leanh::lean_dec(v___y_6503_);
    crate::leanh::lean_dec_ref(v___y_6502_);
    crate::leanh::lean_dec(v___y_6501_);
    crate::leanh::lean_dec_ref(v___y_6500_);
    crate::leanh::lean_dec(v___y_6499_);
    crate::leanh::lean_dec_ref(v___y_6498_);
    crate::leanh::lean_dec(v_as_x27_6495_);
    crate::leanh::lean_dec(v_as_6494_);
    return v_res_6507_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(
    mut v_00_u03b1_6508_: *mut crate::leanh::LeanObject,
    mut v_ref_6509_: *mut crate::leanh::LeanObject,
    mut v_msg_6510_: *mut crate::leanh::LeanObject,
    mut v___y_6511_: *mut crate::leanh::LeanObject,
    mut v___y_6512_: *mut crate::leanh::LeanObject,
    mut v___y_6513_: *mut crate::leanh::LeanObject,
    mut v___y_6514_: *mut crate::leanh::LeanObject,
    mut v___y_6515_: *mut crate::leanh::LeanObject,
    mut v___y_6516_: *mut crate::leanh::LeanObject,
    mut v___y_6517_: *mut crate::leanh::LeanObject,
    mut v___y_6518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6520_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_6509_, v_msg_6510_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
    return v___x_6520_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(
    mut v_00_u03b1_6521_: *mut crate::leanh::LeanObject,
    mut v_ref_6522_: *mut crate::leanh::LeanObject,
    mut v_msg_6523_: *mut crate::leanh::LeanObject,
    mut v___y_6524_: *mut crate::leanh::LeanObject,
    mut v___y_6525_: *mut crate::leanh::LeanObject,
    mut v___y_6526_: *mut crate::leanh::LeanObject,
    mut v___y_6527_: *mut crate::leanh::LeanObject,
    mut v___y_6528_: *mut crate::leanh::LeanObject,
    mut v___y_6529_: *mut crate::leanh::LeanObject,
    mut v___y_6530_: *mut crate::leanh::LeanObject,
    mut v___y_6531_: *mut crate::leanh::LeanObject,
    mut v___y_6532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6533_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(v_00_u03b1_6521_, v_ref_6522_, v_msg_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_, v___y_6530_, v___y_6531_);
    crate::leanh::lean_dec(v___y_6531_);
    crate::leanh::lean_dec_ref(v___y_6530_);
    crate::leanh::lean_dec(v___y_6529_);
    crate::leanh::lean_dec_ref(v___y_6528_);
    crate::leanh::lean_dec(v___y_6527_);
    crate::leanh::lean_dec_ref(v___y_6526_);
    crate::leanh::lean_dec(v___y_6525_);
    crate::leanh::lean_dec_ref(v___y_6524_);
    crate::leanh::lean_dec(v_ref_6522_);
    return v_res_6533_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9(
    mut v_00_u03b2_6534_: *mut crate::leanh::LeanObject,
    mut v_x_6535_: *mut crate::leanh::LeanObject,
    mut v_x_6536_: *mut crate::leanh::LeanObject,
    mut v_x_6537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6538_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_x_6535_, v_x_6536_, v_x_6537_);
    return v___x_6538_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(
    mut v_00_u03b2_6539_: *mut crate::leanh::LeanObject,
    mut v_m_6540_: *mut crate::leanh::LeanObject,
    mut v_a_6541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_6540_, v_a_6541_);
    return v___x_6542_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_6543_: *mut crate::leanh::LeanObject,
    mut v_m_6544_: *mut crate::leanh::LeanObject,
    mut v_a_6545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(v_00_u03b2_6543_, v_m_6544_, v_a_6545_);
    crate::leanh::lean_dec(v_a_6545_);
    crate::leanh::lean_dec_ref(v_m_6544_);
    return v_res_6546_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(
    mut v_00_u03b1_6547_: *mut crate::leanh::LeanObject,
    mut v_msg_6548_: *mut crate::leanh::LeanObject,
    mut v___y_6549_: *mut crate::leanh::LeanObject,
    mut v___y_6550_: *mut crate::leanh::LeanObject,
    mut v___y_6551_: *mut crate::leanh::LeanObject,
    mut v___y_6552_: *mut crate::leanh::LeanObject,
    mut v___y_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
    mut v___y_6555_: *mut crate::leanh::LeanObject,
    mut v___y_6556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6558_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_6548_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_);
    return v___x_6558_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___boxed(
    mut v_00_u03b1_6559_: *mut crate::leanh::LeanObject,
    mut v_msg_6560_: *mut crate::leanh::LeanObject,
    mut v___y_6561_: *mut crate::leanh::LeanObject,
    mut v___y_6562_: *mut crate::leanh::LeanObject,
    mut v___y_6563_: *mut crate::leanh::LeanObject,
    mut v___y_6564_: *mut crate::leanh::LeanObject,
    mut v___y_6565_: *mut crate::leanh::LeanObject,
    mut v___y_6566_: *mut crate::leanh::LeanObject,
    mut v___y_6567_: *mut crate::leanh::LeanObject,
    mut v___y_6568_: *mut crate::leanh::LeanObject,
    mut v___y_6569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6570_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(v_00_u03b1_6559_, v_msg_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
    crate::leanh::lean_dec(v___y_6568_);
    crate::leanh::lean_dec_ref(v___y_6567_);
    crate::leanh::lean_dec(v___y_6566_);
    crate::leanh::lean_dec_ref(v___y_6565_);
    crate::leanh::lean_dec(v___y_6564_);
    crate::leanh::lean_dec_ref(v___y_6563_);
    crate::leanh::lean_dec(v___y_6562_);
    crate::leanh::lean_dec_ref(v___y_6561_);
    return v_res_6570_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(
    mut v_00_u03b2_6571_: *mut crate::leanh::LeanObject,
    mut v_x_6572_: *mut crate::leanh::LeanObject,
    mut v_x_6573_: usize,
    mut v_x_6574_: usize,
    mut v_x_6575_: *mut crate::leanh::LeanObject,
    mut v_x_6576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6577_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_6572_, v_x_6573_, v_x_6574_, v_x_6575_, v_x_6576_);
    return v___x_6577_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___boxed(
    mut v_00_u03b2_6578_: *mut crate::leanh::LeanObject,
    mut v_x_6579_: *mut crate::leanh::LeanObject,
    mut v_x_6580_: *mut crate::leanh::LeanObject,
    mut v_x_6581_: *mut crate::leanh::LeanObject,
    mut v_x_6582_: *mut crate::leanh::LeanObject,
    mut v_x_6583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_22501__boxed_6584_: usize = 0;
    let mut v_x_22502__boxed_6585_: usize = 0;
    let mut v_res_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_22501__boxed_6584_ = crate::leanh::lean_unbox_usize(v_x_6580_);
    crate::leanh::lean_dec(v_x_6580_);
    v_x_22502__boxed_6585_ = crate::leanh::lean_unbox_usize(v_x_6581_);
    crate::leanh::lean_dec(v_x_6581_);
    v_res_6586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(v_00_u03b2_6578_, v_x_6579_, v_x_22501__boxed_6584_, v_x_22502__boxed_6585_, v_x_6582_, v_x_6583_);
    return v_res_6586_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(
    mut v_00_u03b2_6587_: *mut crate::leanh::LeanObject,
    mut v_x_6588_: *mut crate::leanh::LeanObject,
    mut v_x_6589_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6590_: u8 = 0;
    v___x_6590_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_6588_, v_x_6589_);
    return v___x_6590_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___boxed(
    mut v_00_u03b2_6591_: *mut crate::leanh::LeanObject,
    mut v_x_6592_: *mut crate::leanh::LeanObject,
    mut v_x_6593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6594_: u8 = 0;
    let mut v_r_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6594_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(v_00_u03b2_6591_, v_x_6592_, v_x_6593_);
    crate::leanh::lean_dec_ref(v_x_6593_);
    crate::leanh::lean_dec_ref(v_x_6592_);
    v_r_6595_ = crate::leanh::lean_box((v_res_6594_) as usize);
    return v_r_6595_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(
    mut v_00_u03b2_6596_: *mut crate::leanh::LeanObject,
    mut v_a_6597_: *mut crate::leanh::LeanObject,
    mut v_x_6598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6599_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_6597_, v_x_6598_);
    return v___x_6599_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___boxed(
    mut v_00_u03b2_6600_: *mut crate::leanh::LeanObject,
    mut v_a_6601_: *mut crate::leanh::LeanObject,
    mut v_x_6602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6603_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(v_00_u03b2_6600_, v_a_6601_, v_x_6602_);
    crate::leanh::lean_dec(v_x_6602_);
    crate::leanh::lean_dec(v_a_6601_);
    return v_res_6603_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18(
    mut v_00_u03b2_6604_: *mut crate::leanh::LeanObject,
    mut v_n_6605_: *mut crate::leanh::LeanObject,
    mut v_k_6606_: *mut crate::leanh::LeanObject,
    mut v_v_6607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6608_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v_n_6605_, v_k_6606_, v_v_6607_);
    return v___x_6608_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(
    mut v_00_u03b2_6609_: *mut crate::leanh::LeanObject,
    mut v_depth_6610_: usize,
    mut v_keys_6611_: *mut crate::leanh::LeanObject,
    mut v_vals_6612_: *mut crate::leanh::LeanObject,
    mut v_heq_6613_: *mut crate::leanh::LeanObject,
    mut v_i_6614_: *mut crate::leanh::LeanObject,
    mut v_entries_6615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6616_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_6610_, v_keys_6611_, v_vals_6612_, v_i_6614_, v_entries_6615_);
    return v___x_6616_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___boxed(
    mut v_00_u03b2_6617_: *mut crate::leanh::LeanObject,
    mut v_depth_6618_: *mut crate::leanh::LeanObject,
    mut v_keys_6619_: *mut crate::leanh::LeanObject,
    mut v_vals_6620_: *mut crate::leanh::LeanObject,
    mut v_heq_6621_: *mut crate::leanh::LeanObject,
    mut v_i_6622_: *mut crate::leanh::LeanObject,
    mut v_entries_6623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_6624_: usize = 0;
    let mut v_res_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_6624_ = crate::leanh::lean_unbox_usize(v_depth_6618_);
    crate::leanh::lean_dec(v_depth_6618_);
    v_res_6625_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(v_00_u03b2_6617_, v_depth_boxed_6624_, v_keys_6619_, v_vals_6620_, v_heq_6621_, v_i_6622_, v_entries_6623_);
    crate::leanh::lean_dec_ref(v_vals_6620_);
    crate::leanh::lean_dec_ref(v_keys_6619_);
    return v_res_6625_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(
    mut v_00_u03b2_6626_: *mut crate::leanh::LeanObject,
    mut v_x_6627_: *mut crate::leanh::LeanObject,
    mut v_x_6628_: usize,
    mut v_x_6629_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6630_: u8 = 0;
    v___x_6630_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_6627_, v_x_6628_, v_x_6629_);
    return v___x_6630_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___boxed(
    mut v_00_u03b2_6631_: *mut crate::leanh::LeanObject,
    mut v_x_6632_: *mut crate::leanh::LeanObject,
    mut v_x_6633_: *mut crate::leanh::LeanObject,
    mut v_x_6634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_22535__boxed_6635_: usize = 0;
    let mut v_res_6636_: u8 = 0;
    let mut v_r_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_22535__boxed_6635_ = crate::leanh::lean_unbox_usize(v_x_6633_);
    crate::leanh::lean_dec(v_x_6633_);
    v_res_6636_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(v_00_u03b2_6631_, v_x_6632_, v_x_22535__boxed_6635_, v_x_6634_);
    crate::leanh::lean_dec_ref(v_x_6634_);
    crate::leanh::lean_dec_ref(v_x_6632_);
    v_r_6637_ = crate::leanh::lean_box((v_res_6636_) as usize);
    return v_r_6637_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20(
    mut v_00_u03b2_6638_: *mut crate::leanh::LeanObject,
    mut v_x_6639_: *mut crate::leanh::LeanObject,
    mut v_x_6640_: *mut crate::leanh::LeanObject,
    mut v_x_6641_: *mut crate::leanh::LeanObject,
    mut v_x_6642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6643_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_x_6639_, v_x_6640_, v_x_6641_, v_x_6642_);
    return v___x_6643_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(
    mut v_00_u03b2_6644_: *mut crate::leanh::LeanObject,
    mut v_keys_6645_: *mut crate::leanh::LeanObject,
    mut v_vals_6646_: *mut crate::leanh::LeanObject,
    mut v_heq_6647_: *mut crate::leanh::LeanObject,
    mut v_i_6648_: *mut crate::leanh::LeanObject,
    mut v_k_6649_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6650_: u8 = 0;
    v___x_6650_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_6645_, v_i_6648_, v_k_6649_);
    return v___x_6650_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___boxed(
    mut v_00_u03b2_6651_: *mut crate::leanh::LeanObject,
    mut v_keys_6652_: *mut crate::leanh::LeanObject,
    mut v_vals_6653_: *mut crate::leanh::LeanObject,
    mut v_heq_6654_: *mut crate::leanh::LeanObject,
    mut v_i_6655_: *mut crate::leanh::LeanObject,
    mut v_k_6656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6657_: u8 = 0;
    let mut v_r_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6657_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(v_00_u03b2_6651_, v_keys_6652_, v_vals_6653_, v_heq_6654_, v_i_6655_, v_k_6656_);
    crate::leanh::lean_dec_ref(v_k_6656_);
    crate::leanh::lean_dec_ref(v_vals_6653_);
    crate::leanh::lean_dec_ref(v_keys_6652_);
    v_r_6658_ = crate::leanh::lean_box((v_res_6657_) as usize);
    return v_r_6658_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6668_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_6669_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2;
    v___x_6670_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1;
    v___x_6671_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_6672_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6668_,
        v___x_6669_,
        v___x_6670_,
        v___x_6671_,
    );
    return v___x_6672_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(
    mut v_a_6673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6674_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
    return v_res_6674_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_Do_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
}
